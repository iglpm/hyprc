//! Driving macro expansion: resolving macro paths, expanding, and collecting the results.

use crate::cfg;
use crate::macros::builtin::{self, BuiltinMacro, err, str_lit};
use crate::macros::{MacroImpl, mbe};
use crate::paths::{Lookup, PathResult};
use crate::{
    CrateNum, DefId, DefKind, FragmentKind, InvocKind, ItemNode, MacroData, Ns, Res, Resolver,
    ScopeId, TextualScope,
};
use hyprc_span::hygiene::{ExpnData, ExpnId, ExpnKind, Transparency};
use hyprc_span::{Diag, DiagCtxt, Edition, Ident, Span, Symbol, kw};
use hyprc_syntax::Parser;
use hyprc_syntax::ast::{self, ItemKind, P};
use hyprc_syntax::token::{Delim, LitKind, Token, TokenKind};
use std::sync::Arc;

pub(crate) enum MacroLookup {
    Found(DefId),
    NotFound,
    Indeterminate,
}

/// What a built-in produced: tokens to parse in the call's context.
pub(crate) type Expansion = Result<Vec<Token>, Diag>;

impl Resolver<'_> {
    /// Phase 1: imports and item-level macros to a fixed point.
    pub(crate) fn resolve_items(&mut self) {
        let mut forced = false;
        loop {
            let mut progress = self.resolve_imports_round();
            progress |= self.expand_invocations_round(forced);
            if progress {
                forced = false;
                continue;
            }
            if forced {
                break;
            }
            // Nothing moves: what's still unresolved won't resolve by waiting. Report the
            // macros that aren't found (which unblocks scopes waiting on them) and try again.
            forced = true;
        }
        self.report_unresolved_imports();
    }

    /// The textual (`macro_rules!`) scope lookup. Unexpanded calls on the way don't stop
    /// it (a macro-expanded `macro_rules!` may not shadow one found further out, as in
    /// rustc), but make a miss `Indeterminate`.
    pub(crate) fn lookup_textual(&self, name: Symbol, mut scope: ScopeId) -> MacroLookup {
        let mut undetermined = false;
        loop {
            match self.scopes[scope.0 as usize] {
                TextualScope::Empty => {
                    return if undetermined {
                        MacroLookup::Indeterminate
                    } else {
                        MacroLookup::NotFound
                    };
                }
                TextualScope::Def {
                    name: n,
                    mac,
                    parent,
                } => {
                    if n == name {
                        return MacroLookup::Found(mac);
                    }
                    scope = parent;
                }
                TextualScope::Invocation { invoc, parent } => {
                    let inv = &self.invocations[invoc];
                    match inv.output_scope {
                        Some(out) => scope = out,
                        None => {
                            undetermined |= !inv.failed;
                            scope = parent;
                        }
                    }
                }
            }
        }
    }

    /// Resolves a macro path: the textual scope first (for single names), then path-based
    /// scopes and the preludes.
    pub(crate) fn resolve_macro_path(
        &self,
        path: &ast::Path,
        module: DefId,
        scope: ScopeId,
        bang: bool,
    ) -> MacroLookup {
        let segs: Vec<Ident> = path.segments.iter().map(|s| s.ident).collect();
        if segs.len() == 1 {
            let ident = segs[0];
            let mut weak = false;
            if bang {
                match self.lookup_textual(ident.name, scope) {
                    MacroLookup::NotFound => {}
                    MacroLookup::Indeterminate => weak = true,
                    found => return found,
                }
            }
            return match self.resolve_ident_lexical_ext(ident, Ns::Macro, module, weak) {
                Lookup::Found(b) => match b.res {
                    Res::Def(_, d) => MacroLookup::Found(d),
                    _ => MacroLookup::NotFound,
                },
                Lookup::Indeterminate => MacroLookup::Indeterminate,
                Lookup::NotFound => MacroLookup::NotFound,
            };
        }
        match self.resolve_path(&segs, Ns::Macro, module, false) {
            PathResult::NonModule {
                res: Res::Def(DefKind::Macro(_), d),
                unresolved: 0,
            } => MacroLookup::Found(d),
            PathResult::Indeterminate => MacroLookup::Indeterminate,
            _ => MacroLookup::NotFound,
        }
    }

    fn expand_invocations_round(&mut self, forced: bool) -> bool {
        let mut progress = false;
        let mut i = 0;
        while i < self.invocations.len() {
            let inv = &self.invocations[i];
            if inv.done || inv.failed {
                i += 1;
                continue;
            }
            let (path, bang) = match &inv.kind {
                InvocKind::Bang(m) => (m.path.clone(), true),
                InvocKind::Derive { path, .. } => (path.clone(), false),
            };
            let module = inv.module;
            let scope = inv.scope;
            match self.resolve_macro_path(&path, module, scope, bang) {
                MacroLookup::Found(def) => {
                    self.expand_invocation(i, def);
                    progress = true;
                }
                // Forced, an undetermined name is as good as missing (rustc's `force`).
                MacroLookup::NotFound | MacroLookup::Indeterminate if forced => {
                    let name = path_to_string(&path);
                    if !bang {
                        // External procedural derive macro (e.g. `serde::Serialize`, `thiserror::Error`).
                        // Skip gracefully so the struct/enum definition and methods remain intact.
                        self.invocations[i].done = true;
                        self.invocations[i].output_scope = Some(scope);
                        progress = true;
                    } else {
                        let what = "macro";
                        self.sess.dcx.emit(
                            Diag::error(format!("cannot find {what} `{name}` in this scope"))
                                .span(path.span, ""),
                        );
                        self.fail_invocation(i);
                        progress = true;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        progress
    }

    fn fail_invocation(&mut self, i: usize) {
        self.invocations[i].failed = true;
        let m = self.invocations[i].module;
        if let Some(md) = self.modules.get_mut(&m) {
            md.pending_macros = md.pending_macros.saturating_sub(1);
        }
    }

    /// The expansion of a macro (compiling `macro_rules!` on first use).
    pub(crate) fn macro_impl(&mut self, def: DefId) -> (MacroImpl, bool, Edition, CrateNum) {
        if let Some(m) = self.macros.get(&def) {
            return (m.kind.clone(), m.macro_2_0, m.edition, m.krate);
        }
        let krate = self.def(def).krate;
        let (kind, macro_2_0) = match &self.nodes[def.0 as usize] {
            ItemNode::Item(item) => match &item.kind {
                ItemKind::MacroDef(md) => {
                    let builtin = item.attrs.iter().find(|a| {
                        a.name()
                            .is_some_and(|n| n.as_str() == "rustc_builtin_macro")
                    });
                    let kind = if let Some(attr) = builtin {
                        // `#[rustc_builtin_macro]` or `#[rustc_builtin_macro(name)]`.
                        let name = cfg::attr_item(attr)
                            .and_then(|i| match &i.args {
                                ast::AttrArgs::Delimited(a) => {
                                    a.tokens.tokens().first().map(|t| t.sym)
                                }
                                _ => None,
                            })
                            .unwrap_or(item.ident.name);
                        MacroImpl::Builtin(BuiltinMacro::from_name(name.as_str()))
                    } else {
                        match mbe::compile(md.body.tokens.tokens(), self.edition, !md.macro_rules) {
                            Ok(rules) => MacroImpl::Rules(Arc::new(rules)),
                            Err(d) => {
                                self.sess.dcx.emit(d);
                                MacroImpl::Broken
                            }
                        }
                    };
                    (kind, !md.macro_rules)
                }
                _ => (MacroImpl::Broken, false),
            },
            _ => (MacroImpl::Broken, false),
        };
        self.macros.insert(
            def,
            MacroData {
                def,
                kind: kind.clone(),
                krate,
                edition: self.edition,
                macro_2_0,
            },
        );
        (kind, macro_2_0, self.edition, krate)
    }

    /// The transparency of a macro's marks: `#[rustc_macro_transparency]` or the default
    /// for its kind.
    fn macro_transparency(&self, def: DefId, macro_2_0: bool) -> Transparency {
        if let ItemNode::Item(item) = &self.nodes[def.0 as usize]
            && let Some(a) = item.attrs.iter().find(|a| {
                a.name()
                    .is_some_and(|n| n.as_str() == "rustc_macro_transparency")
            })
            && let Some(v) = cfg::attr_str_value(a)
        {
            return match v.as_str() {
                "transparent" => Transparency::Transparent,
                "semitransparent" | "semiopaque" => Transparency::SemiTransparent,
                _ => Transparency::Opaque,
            };
        }
        if macro_2_0 {
            Transparency::Opaque
        } else {
            Transparency::SemiTransparent
        }
    }

    /// Starts an expansion of the macro `def` called at `call_site`.
    pub(crate) fn new_expansion(&mut self, def: DefId, parent: ExpnId, call_site: Span) -> ExpnId {
        let (_, _, edition, krate) = self.macro_impl(def);
        let allow_internal_unstable = matches!(&self.nodes[def.0 as usize], ItemNode::Item(i) if cfg::has_attr(&i.attrs, "allow_internal_unstable"));
        let expn = ExpnId::fresh(ExpnData {
            kind: ExpnKind::Macro,
            name: self.def(def).name,
            parent,
            call_site,
            def_site: self.def(def).span,
            def_crate: krate.0,
            edition,
            allow_internal_unstable,
            macro_def: def.0,
        });
        self.expn_crates.insert(expn, krate);
        expn
    }

    /// Expands a function-like macro call: the tokens of its expansion.
    pub(crate) fn expand_bang(
        &mut self,
        def: DefId,
        mac: &ast::MacCall,
        expn: ExpnId,
        module: DefId,
        scope: ScopeId,
        fragment: FragmentKind,
    ) -> Expansion {
        let (kind, macro_2_0, _, _) = self.macro_impl(def);
        let span = mac.path.span.to(mac.args.close);
        match kind {
            MacroImpl::Rules(rules) => {
                let t = self.macro_transparency(def, macro_2_0);
                rules.expand(mac.args.tokens.tokens(), span, expn, t)
            }
            MacroImpl::Builtin(b) => {
                self.expand_builtin(b, mac, span, expn, module, scope, fragment)
            }
            MacroImpl::Broken => Ok(Vec::new()),
        }
    }

    pub(crate) fn expand_invocation(&mut self, i: usize, def: DefId) {
        let (module, scope, fragment, call_site, parent_expn) = {
            let inv = &self.invocations[i];
            (
                inv.module,
                inv.scope,
                inv.fragment,
                inv.span,
                inv.parent_expn,
            )
        };
        let prev_krate = self.current_krate;
        self.current_krate = self.def(module).krate;
        let kind_is_macro = matches!(self.def_kind(def), DefKind::Macro(_));
        if !kind_is_macro {
            self.sess.dcx.emit(
                Diag::error(format!(
                    "expected macro, found {}",
                    self.def_kind(def).descr()
                ))
                .span(call_site, ""),
            );
            self.fail_invocation(i);
            self.current_krate = prev_krate;
            return;
        }
        let expn = self.new_expansion(def, parent_expn, call_site);
        let tokens = match std::mem::replace(
            &mut self.invocations[i].kind,
            InvocKind::Bang(dummy_mac(call_site)),
        ) {
            InvocKind::Bang(mac) => {
                let r = self.expand_bang(def, &mac, expn, module, scope, fragment);
                self.invocations[i].kind = InvocKind::Bang(mac);
                r
            }
            InvocKind::Derive {
                path,
                item,
                is_const,
            } => {
                let r = self.expand_derive(def, item, call_site, expn, is_const);
                self.invocations[i].kind = InvocKind::Derive {
                    path,
                    item,
                    is_const,
                };
                r
            }
        };
        let derive_of = match self.invocations[i].kind {
            InvocKind::Derive { item, .. } => Some(item),
            InvocKind::Bang(_) => None,
        };
        let tokens = match tokens {
            Ok(t) => t,
            Err(d) => {
                self.sess.dcx.emit(d);
                self.invocations[i].output_scope = Some(scope);
                self.invocations[i].done = true;
                self.fail_pending(module);
                self.current_krate = prev_krate;
                return;
            }
        };
        let (_, _, edition, _) = self.macro_impl(def);
        let out_scope = self.collect_fragment(
            tokens, fragment, module, scope, expn, edition, call_site, derive_of,
        );
        self.invocations[i].output_scope = Some(out_scope);
        self.invocations[i].done = true;
        self.fail_pending(module);
        self.current_krate = prev_krate;
    }

    fn fail_pending(&mut self, module: DefId) {
        if let Some(md) = self.modules.get_mut(&module) {
            md.pending_macros = md.pending_macros.saturating_sub(1);
        }
    }

    /// Parses an item-level expansion and collects what it defines.
    fn collect_fragment(
        &mut self,
        mut tokens: Vec<Token>,
        fragment: FragmentKind,
        module: DefId,
        scope: ScopeId,
        expn: ExpnId,
        edition: Edition,
        call_site: Span,
        derive_of: Option<DefId>,
    ) -> ScopeId {
        tokens.push(Token::new(TokenKind::Eof, call_site.shrink_to_hi()));
        let dcx = &self.sess.dcx;
        let mut p = Parser::new(&tokens, edition, dcx);
        match fragment {
            FragmentKind::Items => {
                let mut items = p.parse_items_until(TokenKind::Eof);
                if let Some(item) = derive_of {
                    crate::derive::finish(self, item, &mut items);
                }
                self.collect_items(module, items, scope, expn)
            }
            FragmentKind::AssocItems(owner) => {
                let in_trait = self.def_kind(owner) == DefKind::Trait;
                let items = p.parse_assoc_items_fragment(in_trait);
                self.collect_assoc_items(owner, module, items, scope, expn);
                scope
            }
            FragmentKind::ForeignItems(owner) => {
                let items = p.parse_foreign_items_fragment();
                self.collect_foreign_items(owner, module, items, scope, expn);
                scope
            }
        }
    }

    fn expand_derive(
        &mut self,
        def: DefId,
        item: DefId,
        span: Span,
        expn: ExpnId,
        is_const: bool,
    ) -> Expansion {
        let (kind, ..) = self.macro_impl(def);
        let MacroImpl::Builtin(b) = kind else {
            return Err(err(
                span,
                "derive macros other than the built-in ones need procedural macro support, which hyprc doesn't have yet",
            ));
        };
        crate::derive::expand(self, b, item, span, expn, is_const)
    }

    /// Built-in function-like macros.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn expand_builtin(
        &mut self,
        b: BuiltinMacro,
        mac: &ast::MacCall,
        span: Span,
        expn: ExpnId,
        module: DefId,
        scope: ScopeId,
        fragment: FragmentKind,
    ) -> Expansion {
        let args = mac.args.tokens.tokens();
        // Tokens the built-in writes belong to its expansion (transparent, like call-site).
        let span = span.with_ctxt(span.ctxt.apply_mark(expn, Transparency::Transparent));
        let _ = fragment;
        match b {
            BuiltinMacro::Stringify => Ok(vec![str_lit(&builtin::tokens_to_string(args), span)]),
            BuiltinMacro::Line | BuiltinMacro::Column | BuiltinMacro::File => {
                let site = self.outermost_call_site(mac.path.span);
                let (file, line, col) = builtin::call_site_loc(site);
                Ok(vec![match b {
                    BuiltinMacro::Line => builtin::lit(LitKind::Integer, &line.to_string(), span),
                    BuiltinMacro::Column => builtin::lit(LitKind::Integer, &col.to_string(), span),
                    _ => str_lit(&file, span),
                }])
            }
            BuiltinMacro::ModulePath => {
                let m = self.parent_module(module);
                Ok(vec![str_lit(&self.def_path_str(m), span)])
            }
            BuiltinMacro::Cfg => {
                let pred = cfg::parse_cfg_pred(args, span)?;
                let holds = pred.eval_with(&self.active_cfg_context());
                Ok(vec![Token::ident(
                    if holds { kw::True } else { kw::False },
                    span,
                )])
            }
            BuiltinMacro::CompileError => {
                let msg = args
                    .first()
                    .and_then(builtin::literal_value)
                    .unwrap_or_default();
                Err(Diag::error(msg).span(mac.path.span.to(mac.args.close), ""))
            }
            BuiltinMacro::Concat => {
                let mut s = String::new();
                for part in cfg::split_commas(args) {
                    match part {
                        [t] => match builtin::literal_value(t) {
                            Some(v) => s.push_str(&v),
                            None => return Err(err(t.span, "expected a literal")),
                        },
                        [m, t] if m.kind == TokenKind::Minus => {
                            s.push('-');
                            s.push_str(&builtin::literal_value(t).unwrap_or_default());
                        }
                        [] => {}
                        _ => {
                            // `concat!(stringify!(x), …)`: nested macro calls are expanded
                            // first (eagerly), like rustc does.
                            let v = self.eager_literal(part, module, scope, expn)?;
                            s.push_str(&v);
                        }
                    }
                }
                Ok(vec![str_lit(&s, span)])
            }
            BuiltinMacro::Env | BuiltinMacro::OptionEnv => {
                let parts = cfg::split_commas(args);
                let name_tok = parts
                    .first()
                    .and_then(|p| p.first())
                    .copied()
                    .ok_or_else(|| err(span, "expected a variable name"))?;
                let name = builtin::literal_value(&name_tok)
                    .ok_or_else(|| err(name_tok.span, "expected string literal"))?;
                let value = std::env::var(&name).ok().or_else(|| match name.as_str() {
                    "STD_ENV_ARCH" => Some("x86_64".to_string()),
                    "TARGET" => Some("x86_64-unknown-linux-gnu".to_string()),
                    "HOST" => Some("x86_64-unknown-linux-gnu".to_string()),
                    _ => None,
                });
                if b == BuiltinMacro::OptionEnv {
                    return Ok(match value {
                        Some(v) => tokens_of(
                            &format!(
                                "::core::option::Option::Some::<&'static str>({})",
                                quote(&v)
                            ),
                            span,
                        ),
                        None => tokens_of("::core::option::Option::None::<&'static str>", span),
                    });
                }
                match value {
                    Some(v) => Ok(vec![str_lit(&v, span)]),
                    None => Err(err(
                        mac.path.span,
                        format!("environment variable `{name}` not defined at compile time"),
                    )),
                }
            }
            BuiltinMacro::IncludeStr | BuiltinMacro::IncludeBytes | BuiltinMacro::Include => {
                let lit_tok = args
                    .first()
                    .copied()
                    .ok_or_else(|| err(span, "expected a file name"))?;
                let rel = match builtin::literal_value(&lit_tok) {
                    Some(v) => v,
                    None => self.eager_literal(args, module, scope, expn)?,
                };
                let base = hyprc_span::source_map()
                    .file_of(self.outermost_call_site(mac.path.span).lo)
                    .and_then(|f| f.path.clone())
                    .and_then(|p| p.parent().map(|d| d.to_path_buf()))
                    .unwrap_or_default();
                let path = base.join(&rel);
                match b {
                    BuiltinMacro::IncludeStr => {
                        let text = std::fs::read_to_string(&path).map_err(|e| {
                            err(span, format!("couldn't read `{}`: {e}", path.display()))
                        })?;
                        Ok(vec![str_lit(&text, span)])
                    }
                    BuiltinMacro::IncludeBytes => {
                        let bytes = std::fs::read(&path).map_err(|e| {
                            err(span, format!("couldn't read `{}`: {e}", path.display()))
                        })?;
                        let mut text = String::with_capacity(bytes.len() * 4);
                        for b in bytes {
                            text.push_str(&format!("\\x{b:02x}"));
                        }
                        Ok(vec![
                            Token::new(TokenKind::And, span),
                            builtin::lit(LitKind::ByteStr, &text, span),
                        ])
                    }
                    _ => {
                        let file = hyprc_span::source_map().load_file(&path).map_err(|e| {
                            err(span, format!("couldn't read `{}`: {e}", path.display()))
                        })?;
                        let dcx = &self.sess.dcx;
                        let mut toks = hyprc_syntax::tokenize(file.src, file.start, dcx);
                        toks.pop();
                        Ok(toks)
                    }
                }
            }
            BuiltinMacro::FormatArgs
            | BuiltinMacro::FormatArgsNl
            | BuiltinMacro::ConstFormatArgs => {
                // `builtin # format_args(…)`; lowering builds `fmt::Arguments` from it.
                let name = match b {
                    BuiltinMacro::FormatArgsNl => "format_args_nl",
                    BuiltinMacro::ConstFormatArgs => "const_format_args",
                    _ => "format_args",
                };
                Ok(builtin_syntax(name, args, span))
            }
            BuiltinMacro::Asm | BuiltinMacro::NakedAsm | BuiltinMacro::GlobalAsm => {
                let name = match b {
                    BuiltinMacro::Asm => "asm",
                    BuiltinMacro::NakedAsm => "naked_asm",
                    _ => "global_asm",
                };
                Ok(builtin_syntax(name, args, span))
            }
            BuiltinMacro::Assert => {
                // `assert!(cond)` / `assert!(cond, fmt…)`. The condition ends where an
                // expression does (`a == f::<B, C>()` has a comma in it).
                let cond = self
                    .leading_expr(args)
                    .unwrap_or_else(|| cfg::split_commas(args).first().copied().unwrap_or(&[]));
                if cond.is_empty() {
                    return Err(err(
                        span,
                        "macro requires a boolean expression as an argument",
                    ));
                }
                let comma_pos = args[cond.len()..]
                    .iter()
                    .position(|t| t.kind == TokenKind::Comma)
                    .map(|p| cond.len() + p);
                let fmt_args = comma_pos.map(|p| &args[p + 1..]).unwrap_or(&[]);
                let has_fmt = fmt_args.iter().any(|t| t.kind != TokenKind::Comma);

                let mut out = tokens_of("if !", span);
                out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                out.extend_from_slice(cond);
                out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                out.push(Token::new(TokenKind::Open(Delim::Brace), span));
                let crate_span =
                    span.with_ctxt(span.ctxt.apply_mark(expn, Transparency::SemiTransparent));
                if has_fmt {
                    out.extend(tokens_of("$crate::panic::panic_2021!", crate_span));
                    out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                    out.extend_from_slice(fmt_args);
                    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                    out.push(Token::new(TokenKind::Semi, span));
                } else {
                    let msg = format!("assertion failed: {}", builtin::tokens_to_string(cond));
                    out.extend(tokens_of("$crate::panicking::panic", crate_span));
                    out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                    out.push(str_lit(&msg, span));
                    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                    out.push(Token::new(TokenKind::Semi, span));
                }
                out.push(Token::new(TokenKind::Close(Delim::Brace), span));
                Ok(out)
            }
            BuiltinMacro::CorePanic | BuiltinMacro::StdPanic => {
                // `panic!` picks the 2015 or 2021 flavor by the caller's edition.
                let edition = mac.path.span.expn_edition().unwrap_or(self.edition);
                let which = if edition >= Edition::E2021 {
                    "panic_2021"
                } else {
                    "panic_2015"
                };
                let crate_span =
                    span.with_ctxt(span.ctxt.apply_mark(expn, Transparency::SemiTransparent));
                let mut out = tokens_of(&format!("$crate::panic::{which}!"), crate_span);
                out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                out.extend_from_slice(args);
                out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                Ok(out)
            }
            BuiltinMacro::PatternType => Ok(args.to_vec()),
            BuiltinMacro::UnreachablePanic => {
                let edition = mac.path.span.expn_edition().unwrap_or(self.edition);
                let which = if edition >= Edition::E2021 {
                    "unreachable_2021"
                } else {
                    "unreachable_2015"
                };
                let crate_span =
                    span.with_ctxt(span.ctxt.apply_mark(expn, Transparency::SemiTransparent));
                let mut out = tokens_of(&format!("$crate::panic::{which}!"), crate_span);
                out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                out.extend_from_slice(args);
                out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                Ok(out)
            }
            BuiltinMacro::CfgSelect => {
                // `cfg_select! { pred => { … } _ => { … } }`: the first branch that holds. An
                // arm can also be an expression or type up to a comma (`pred => x,`).
                let mut i = 0;
                while i < args.len() {
                    let start = i;
                    while i < args.len() && args[i].kind != TokenKind::FatArrow {
                        i += 1;
                    }
                    let pred_tokens = &args[start..i];
                    i += 1;
                    let Some(open) = args.get(i) else { break };
                    let (body, next) = if open.kind == TokenKind::Open(Delim::Brace) {
                        group(args, i)
                    } else {
                        let rest = &args[i..];
                        let n = self.leading_ty_or_expr(rest).map_or_else(
                            || cfg::split_commas(rest).first().map_or(0, |p| p.len()),
                            |t| t.len(),
                        );
                        (&rest[..n], i + n)
                    };
                    i = next;
                    if args.get(i).map(|t| t.kind) == Some(TokenKind::Comma) {
                        i += 1;
                    }
                    let holds = if pred_tokens.len() == 1 && pred_tokens[0].sym == kw::Underscore {
                        true
                    } else {
                        cfg::parse_cfg_pred(pred_tokens, span)?
                            .eval_with(&self.active_cfg_context())
                    };
                    if holds {
                        return Ok(body.to_vec());
                    }
                }
                Ok(Vec::new())
            }
            BuiltinMacro::ConcatIdents => {
                let mut s = String::new();
                for part in cfg::split_commas(args) {
                    for t in part {
                        s.push_str(t.sym.as_str());
                    }
                }
                Ok(vec![Token::ident(Symbol::intern(&s), span)])
            }
            BuiltinMacro::Format => {
                let mut out = Vec::new();
                append_format_call(&mut out, "::alloc::fmt::format", "format_args", args, span);
                Ok(out)
            }
            BuiltinMacro::Println => {
                let mut out = Vec::new();
                append_format_call(&mut out, "::std::io::_print", "format_args_nl", args, span);
                Ok(out)
            }
            BuiltinMacro::Eprintln => {
                let mut out = Vec::new();
                append_format_call(&mut out, "::std::io::_eprint", "format_args_nl", args, span);
                Ok(out)
            }
            BuiltinMacro::Print => {
                let mut out = Vec::new();
                append_format_call(&mut out, "::std::io::_print", "format_args", args, span);
                Ok(out)
            }
            BuiltinMacro::Eprint => {
                let mut out = Vec::new();
                append_format_call(&mut out, "::std::io::_eprint", "format_args", args, span);
                Ok(out)
            }
            BuiltinMacro::Write => {
                let comma_pos = args.iter().position(|t| t.kind == TokenKind::Comma);
                let (dst, rest) = if let Some(pos) = comma_pos {
                    (&args[..pos], &args[pos + 1..])
                } else {
                    (args, &[][..])
                };
                let mut out = Vec::new();
                out.extend_from_slice(dst);
                append_format_call(&mut out, ".write_fmt", "format_args", rest, span);
                Ok(out)
            }
            BuiltinMacro::Writeln => {
                let comma_pos = args.iter().position(|t| t.kind == TokenKind::Comma);
                let (dst, rest) = if let Some(pos) = comma_pos {
                    (&args[..pos], &args[pos + 1..])
                } else {
                    (args, &[][..])
                };
                let mut out = Vec::new();
                out.extend_from_slice(dst);
                append_format_call(&mut out, ".write_fmt", "format_args_nl", rest, span);
                Ok(out)
            }
            BuiltinMacro::Vec => {
                if let Some(pos) = args.iter().position(|t| t.kind == TokenKind::Semi) {
                    let elem = &args[..pos];
                    let len = &args[pos + 1..];
                    let mut out = tokens_of("::alloc::vec::from_elem", span);
                    out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                    out.extend_from_slice(elem);
                    out.push(Token::new(TokenKind::Comma, span));
                    out.extend_from_slice(len);
                    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                    Ok(out)
                } else {
                    let mut out = tokens_of("<[_]>::into_vec(::alloc::boxed::Box::new", span);
                    out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                    out.push(Token::new(TokenKind::Open(Delim::Bracket), span));
                    out.extend_from_slice(args);
                    out.push(Token::new(TokenKind::Close(Delim::Bracket), span));
                    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                    Ok(out)
                }
            }
            BuiltinMacro::Matches => {
                let expr = self
                    .leading_expr(args)
                    .unwrap_or_else(|| cfg::split_commas(args).first().copied().unwrap_or(&[]));
                let comma_pos = args[expr.len()..]
                    .iter()
                    .position(|t| t.kind == TokenKind::Comma)
                    .map(|p| expr.len() + p);
                let pat_and_guard = comma_pos.map(|p| &args[p + 1..]).unwrap_or(&[]);
                let mut out = tokens_of("match", span);
                out.push(Token::new(TokenKind::Open(Delim::Paren), span));
                out.extend_from_slice(expr);
                out.push(Token::new(TokenKind::Close(Delim::Paren), span));
                out.push(Token::new(TokenKind::Open(Delim::Brace), span));
                out.extend_from_slice(pat_and_guard);
                out.extend(tokens_of("=> true, _ => false", span));
                out.push(Token::new(TokenKind::Close(Delim::Brace), span));
                Ok(out)
            }
            BuiltinMacro::Todo => Ok(tokens_of("::core::panic!(\"not yet implemented\")", span)),
            BuiltinMacro::Unimplemented => {
                Ok(tokens_of("::core::panic!(\"not implemented\")", span))
            }
            BuiltinMacro::TraceMacros | BuiltinMacro::LogSyntax => Ok(Vec::new()),
            BuiltinMacro::Unsupported(name) => Err(err(
                span,
                format!("the built-in macro `{name}` isn't supported by hyprc yet"),
            )),
            other => Err(err(
                span,
                format!("`{other:?}` is not a function-like macro"),
            )),
        }
    }

    /// The tokens of the type or expression `args` starts with, if a comma or the end
    /// follows it.
    fn leading_ty_or_expr<'t>(&self, args: &'t [Token]) -> Option<&'t [Token]> {
        let span = args.last().map_or(Span::DUMMY, |t| t.span);
        let mut toks = args.to_vec();
        toks.push(Token::new(TokenKind::Eof, span));
        let dcx = DiagCtxt::buffered();
        let mut p = Parser::new(&toks, self.edition, &dcx);
        if p.parse_ty().is_ok()
            && let Some(n) = p.consumed()
            && n <= args.len()
            && matches!(toks[n].kind, TokenKind::Comma | TokenKind::Eof)
        {
            return Some(&args[..n]);
        }
        self.leading_expr(args)
    }

    /// The tokens of the expression `args` starts with, if a comma or the end follows it.
    fn leading_expr<'t>(&self, args: &'t [Token]) -> Option<&'t [Token]> {
        let span = args.last().map_or(Span::DUMMY, |t| t.span);
        let mut toks = args.to_vec();
        toks.push(Token::new(TokenKind::Eof, span));
        let dcx = DiagCtxt::buffered();
        let mut p = Parser::new(&toks, self.edition, &dcx);
        p.parse_expr().ok()?;
        let n = p.consumed()?;
        (n <= args.len() && matches!(toks[n].kind, TokenKind::Comma | TokenKind::Eof))
            .then(|| &args[..n])
    }

    /// Expands macro calls in a built-in's argument until it is a literal (`concat!` and
    /// `include_str!` accept `concat!(…)`, `stringify!(…)`, `env!(…)`, … as arguments).
    fn eager_literal(
        &mut self,
        tokens: &[Token],
        module: DefId,
        scope: ScopeId,
        parent: ExpnId,
    ) -> Result<String, Diag> {
        let span = tokens.first().map_or(Span::DUMMY, |t| t.span);
        let mut toks = tokens.to_vec();
        toks.push(Token::new(TokenKind::Eof, span));
        let dcx = DiagCtxt::buffered();
        let mut p = Parser::new(&toks, self.edition, &dcx);
        let mut expr = p.parse_expr().map_err(|e| *e.0)?;
        // An expression passed through a macro's `$e:expr` comes in (invisible) parentheses.
        while let ast::ExprKind::Paren(inner) = expr.kind {
            expr = inner;
        }
        match expr.kind {
            ast::ExprKind::Lit(l) => {
                let t = Token {
                    kind: TokenKind::Literal(l.kind),
                    joint: false,
                    sym: l.symbol,
                    suffix: l.suffix,
                    span: l.span,
                };
                builtin::literal_value(&t).ok_or_else(|| err(span, "expected a literal"))
            }
            ast::ExprKind::MacCall(mac) => {
                let def = match self.resolve_macro_path(&mac.path, module, scope, true) {
                    MacroLookup::Found(d) => d,
                    _ => return Err(err(mac.path.span, "cannot find macro in this scope")),
                };
                let expn = self.new_expansion(def, parent, mac.path.span);
                let out = self.expand_bang(def, &mac, expn, module, scope, FragmentKind::Items)?;
                self.eager_literal(&out, module, scope, expn)
            }
            _ => Err(err(span, "expected a literal")),
        }
    }

    /// Expands a built-in macro call in an attribute value to a string literal.
    pub(crate) fn eager_attr_literal(&mut self, mac: P<ast::MacCall>) -> Result<ast::Lit, Diag> {
        let span = mac.path.span;
        let def = match self.resolve_macro_path(&mac.path, self.root, ScopeId::EMPTY, true) {
            MacroLookup::Found(d) => d,
            _ => return Err(err(span, "cannot find the macro in this attribute value")),
        };
        let expn = self.new_expansion(def, ExpnId::ROOT, span);
        let tokens = self.expand_bang(
            def,
            &mac,
            expn,
            self.root,
            ScopeId::EMPTY,
            FragmentKind::Items,
        )?;
        match tokens.as_slice() {
            [t] if matches!(t.kind, TokenKind::Literal(_)) => {
                let TokenKind::Literal(kind) = t.kind else {
                    unreachable!()
                };
                Ok(ast::Lit {
                    kind,
                    symbol: t.sym,
                    suffix: t.suffix,
                    span: t.span,
                })
            }
            _ => Err(err(
                span,
                "expected the macro in this attribute value to expand to a literal",
            )),
        }
    }

    /// The span of the outermost macro call a span came from (`line!()` in a macro reports
    /// the line of the call in source).
    pub(crate) fn outermost_call_site(&self, mut span: Span) -> Span {
        for _ in 0..256 {
            let expn = span.ctxt.outer_expn();
            if expn == ExpnId::ROOT {
                return span;
            }
            span = expn.data().call_site;
        }
        span
    }
}

fn group(tokens: &[Token], pos: usize) -> (&[Token], usize) {
    let mut depth = 0usize;
    for (i, t) in tokens[pos..].iter().enumerate() {
        match t.kind {
            TokenKind::Open(_) => depth += 1,
            TokenKind::Close(_) => {
                depth -= 1;
                if depth == 0 {
                    return (&tokens[pos + 1..pos + i], pos + i + 1);
                }
            }
            _ => {}
        }
    }
    (&tokens[(pos + 1).min(tokens.len())..], tokens.len())
}

fn path_to_string(path: &ast::Path) -> String {
    path.segments
        .iter()
        .map(|s| s.ident.name.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn quote(s: &str) -> String {
    format!("\"{}\"", builtin::escape_str(s))
}

/// Tokenizes compiler-written source; every token gets `span`.
pub(crate) fn tokens_of(src: &str, span: Span) -> Vec<Token> {
    let dcx = DiagCtxt::buffered();
    let mut toks = hyprc_syntax::tokenize(src, 0, &dcx);
    toks.pop();
    // `$crate` in compiler-written code: one identifier.
    let mut out = Vec::with_capacity(toks.len());
    let mut i = 0;
    while i < toks.len() {
        let mut t = toks[i];
        t.span = span;
        if t.kind == TokenKind::Dollar && toks.get(i + 1).is_some_and(|n| n.sym == kw::Crate) {
            out.push(Token {
                kind: TokenKind::Ident,
                sym: kw::DollarCrate,
                span,
                joint: toks[i + 1].joint,
                suffix: kw::Empty,
            });
            i += 2;
            continue;
        }
        out.push(t);
        i += 1;
    }
    out
}

/// `builtin # name(args)`
fn builtin_syntax(name: &str, args: &[Token], span: Span) -> Vec<Token> {
    let mut out = vec![
        Token::ident(kw::Builtin, span),
        Token::new(TokenKind::Pound, span),
        Token::ident(Symbol::intern(name), span),
        Token::new(TokenKind::Open(Delim::Paren), span),
    ];
    out.extend_from_slice(args);
    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
    out
}

/// Appends `callee(builtin # format_name(args))` without asking the lexer to repair an
/// intentionally unfinished delimiter sequence.
fn append_format_call(
    out: &mut Vec<Token>,
    callee: &str,
    format_name: &str,
    args: &[Token],
    span: Span,
) {
    out.extend(tokens_of(callee, span));
    out.push(Token::new(TokenKind::Open(Delim::Paren), span));
    out.push(Token::ident(kw::Builtin, span));
    out.push(Token::new(TokenKind::Pound, span));
    out.push(Token::ident(Symbol::intern(format_name), span));
    out.push(Token::new(TokenKind::Open(Delim::Paren), span));
    out.extend_from_slice(args);
    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
    out.push(Token::new(TokenKind::Close(Delim::Paren), span));
}

fn dummy_mac(span: Span) -> Box<ast::MacCall> {
    Box::new(ast::MacCall {
        path: ast::Path {
            span,
            segments: Vec::new(),
        },
        args: ast::DelimArgs {
            open: span,
            close: span,
            delim: Delim::Paren,
            tokens: Default::default(),
        },
    })
}
