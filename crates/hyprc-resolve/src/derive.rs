//! Built-in derives (`#[derive(Clone, Debug, …)]`, `#[derive_const(…)]`).
//!
//! The impl is written as source text in the shape rustc's derives produce, with a
//! placeholder self type, and parsed. [`finish`] then puts in the item's generics (with the
//! derived trait added to each type parameter's bounds) and its real self type, copied
//! from the item's AST, so types and bounds never have to be printed back to text.

use crate::expand::{Expansion, tokens_of};
use crate::macros::builtin::{BuiltinMacro, err};
use crate::{DefId, ItemNode, Resolver};
use hyprc_span::hygiene::{ExpnId, Transparency};
use hyprc_span::{Ident, Span, Symbol};
use hyprc_syntax::ast::{self, P};
use std::fmt::Write;

/// The self type of a derived impl until [`finish`] replaces it.
const PLACEHOLDER: &str = "__HyprcDeriveSelf";

/// One variant (or the struct itself) as derives see it.
struct Shape {
    /// `Name::Variant` for enum variants, `Name` for structs.
    path: String,
    /// The name printed by `Debug`.
    name: String,
    kind: FieldsKind,
    /// Field names (`a`, or `0` for tuple fields), as written in source.
    fields: Vec<String>,
    is_default: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FieldsKind {
    Named,
    Tuple,
    Unit,
}

enum ItemShape {
    Struct(Shape),
    Enum(Vec<Shape>),
    Union,
}

fn ident_src(i: Ident) -> String {
    if i.name.is_reserved(true) && !i.name.is_path_segment_keyword() {
        format!("r#{}", i.name)
    } else {
        i.name.as_str().to_string()
    }
}

fn shape_of(
    path: String,
    name: String,
    data: &ast::VariantData,
    attrs: &[ast::Attribute],
) -> Shape {
    let (kind, fields) = match data {
        ast::VariantData::Struct { fields } => (
            FieldsKind::Named,
            fields
                .iter()
                .map(|f| f.ident.map_or_else(String::new, ident_src))
                .collect(),
        ),
        ast::VariantData::Tuple(fields, _) => (
            FieldsKind::Tuple,
            (0..fields.len()).map(|i| i.to_string()).collect(),
        ),
        ast::VariantData::Unit(_) => (FieldsKind::Unit, Vec::new()),
    };
    Shape {
        path,
        name,
        kind,
        fields,
        is_default: attrs
            .iter()
            .any(|a| a.name().is_some_and(|n| n.as_str() == "default")),
    }
}

impl Shape {
    /// A pattern binding every field to `{prefix}_{i}`: `Name::V(__self_0, __self_1)`.
    fn pattern(&self, prefix: &str) -> String {
        let binds: Vec<String> = (0..self.fields.len())
            .map(|i| format!("{prefix}_{i}"))
            .collect();
        match self.kind {
            FieldsKind::Unit => self.path.clone(),
            FieldsKind::Tuple => format!("{}({})", self.path, binds.join(", ")),
            FieldsKind::Named => {
                let parts: Vec<String> = self
                    .fields
                    .iter()
                    .zip(&binds)
                    .map(|(f, b)| format!("{f}: {b}"))
                    .collect();
                format!("{} {{ {} }}", self.path, parts.join(", "))
            }
        }
    }

    /// Builds a value of this shape from one expression per field.
    fn construct(&self, values: &[String]) -> String {
        match self.kind {
            FieldsKind::Unit => self.path.clone(),
            FieldsKind::Tuple => format!("{}({})", self.path, values.join(", ")),
            FieldsKind::Named => {
                let parts: Vec<String> = self
                    .fields
                    .iter()
                    .zip(values)
                    .map(|(f, v)| format!("{f}: {v}"))
                    .collect();
                format!("{} {{ {} }}", self.path, parts.join(", "))
            }
        }
    }
}

pub(crate) fn expand(
    r: &mut Resolver<'_>,
    b: BuiltinMacro,
    item: DefId,
    span: Span,
    expn: ExpnId,
    is_const: bool,
) -> Expansion {
    let span = span.with_ctxt(span.ctxt.apply_mark(expn, Transparency::Transparent));
    let ItemNode::Item(it) = &r.nodes[item.0 as usize] else {
        return Err(err(
            span,
            "`derive` may only be applied to `struct`s, `enum`s and `union`s",
        ));
    };
    let name = ident_src(it.ident);
    let (shape, generics) = match &it.kind {
        ast::ItemKind::Struct(data, g) => (
            ItemShape::Struct(shape_of(
                "Self".into(),
                it.ident.name.as_str().to_string(),
                data,
                &[],
            )),
            g,
        ),
        ast::ItemKind::Enum(def, g) => (
            ItemShape::Enum(
                def.variants
                    .iter()
                    .map(|v| {
                        shape_of(
                            format!("{name}::{}", ident_src(v.ident)),
                            v.ident.name.as_str().to_string(),
                            &v.data,
                            &v.attrs,
                        )
                    })
                    .collect(),
            ),
            g,
        ),
        ast::ItemKind::Union(_, g) => (ItemShape::Union, g),
        _ => {
            return Err(err(
                span,
                "`derive` may only be applied to `struct`s, `enum`s and `union`s",
            ));
        }
    };
    let has_ty_params = generics
        .params
        .iter()
        .any(|p| !matches!(p.kind, ast::GenericParamKind::Lifetime));
    let derives_copy = crate::collect::derive_paths(&it.attrs)
        .iter()
        .any(|(p, _)| {
            p.segments
                .last()
                .is_some_and(|s| s.ident.name.as_str() == "Copy")
        });
    let constness = if is_const { "const " } else { "" };
    let header =
        |tr: &str| format!("#[automatically_derived] impl {constness}{tr} for {PLACEHOLDER} ");
    let mut src: String;
    match b {
        BuiltinMacro::DeriveCopy => src = header("::core::marker::Copy") + "{}",
        BuiltinMacro::DeriveEq => src = header("::core::cmp::Eq") + "{}",
        BuiltinMacro::DeriveConstParamTy => src = header("::core::marker::ConstParamTy_") + "{}",
        BuiltinMacro::DeriveClone => {
            let body = match &shape {
                // A `Copy` type (or a union, which must be one): a copy.
                ItemShape::Union => "*self".to_string(),
                _ if derives_copy && !has_ty_params => "*self".to_string(),
                ItemShape::Struct(s) => s.construct(
                    &s.fields
                        .iter()
                        .map(|f| format!("::core::clone::Clone::clone(&self.{f})"))
                        .collect::<Vec<_>>(),
                ),
                ItemShape::Enum(vs) => {
                    let mut m = String::from("match self {");
                    for v in vs {
                        let vals: Vec<String> = (0..v.fields.len())
                            .map(|i| format!("::core::clone::Clone::clone(__self_{i})"))
                            .collect();
                        let _ = write!(m, "{} => {},", v.pattern("__self"), v.construct(&vals));
                    }
                    if vs.is_empty() {
                        m.push_str("_ => match *self {}");
                    }
                    m.push('}');
                    m
                }
            };
            src = header("::core::clone::Clone")
                + &format!("{{ #[inline] fn clone(&self) -> Self {{ {body} }} }}");
        }
        BuiltinMacro::DeriveDebug => {
            let fmt_shape = |s: &Shape, access: &dyn Fn(usize) -> String| -> String {
                let n = s.fields.len();
                match s.kind {
                    // No fields to show (`struct S {}`, `S()`): just the name.
                    FieldsKind::Unit => {
                        format!("::core::fmt::Formatter::write_str(f, \"{}\")", s.name)
                    }
                    _ if n == 0 => format!("::core::fmt::Formatter::write_str(f, \"{}\")", s.name),
                    // The last field goes by `&&` so an unsized last field still coerces.
                    FieldsKind::Tuple if n <= 5 => {
                        let vals: Vec<String> = (0..n)
                            .map(|i| {
                                if i + 1 == n {
                                    format!("&{}", access(i))
                                } else {
                                    access(i)
                                }
                            })
                            .collect();
                        format!(
                            "::core::fmt::Formatter::debug_tuple_field{n}_finish(f, \"{}\", {})",
                            s.name,
                            vals.join(", ")
                        )
                    }
                    FieldsKind::Tuple => {
                        let vals: Vec<String> = (0..n)
                            .map(|i| {
                                if i + 1 == n {
                                    format!("&{}", access(i))
                                } else {
                                    access(i)
                                }
                            })
                            .collect();
                        format!(
                            "::core::fmt::Formatter::debug_tuple_fields_finish(f, \"{}\", &[{}])",
                            s.name,
                            vals.join(", ")
                        )
                    }
                    FieldsKind::Named if n <= 5 => {
                        let mut args = String::new();
                        for (i, fname) in s.fields.iter().enumerate() {
                            let v = if i + 1 == n {
                                format!("&{}", access(i))
                            } else {
                                access(i)
                            };
                            let _ = write!(args, ", \"{}\", {v}", fname.trim_start_matches("r#"));
                        }
                        format!(
                            "::core::fmt::Formatter::debug_struct_field{n}_finish(f, \"{}\"{args})",
                            s.name
                        )
                    }
                    FieldsKind::Named => {
                        let names: Vec<String> = s
                            .fields
                            .iter()
                            .map(|f| format!("\"{}\"", f.trim_start_matches("r#")))
                            .collect();
                        let vals: Vec<String> = (0..n)
                            .map(|i| {
                                if i + 1 == n {
                                    format!("&{}", access(i))
                                } else {
                                    access(i)
                                }
                            })
                            .collect();
                        format!(
                            "{{ let names: &'static _ = &[{}]; let values: &[&dyn core::fmt::Debug] = &[{}]; ::core::fmt::Formatter::debug_struct_fields_finish(f, \"{}\", names, values) }}",
                            names.join(", "),
                            vals.join(", "),
                            s.name
                        )
                    }
                }
            };
            let body = match &shape {
                ItemShape::Union => {
                    return Err(err(span, "this trait cannot be derived for unions"));
                }
                ItemShape::Struct(s) => fmt_shape(s, &|i| format!("&self.{}", s.fields[i])),
                ItemShape::Enum(vs) => {
                    let mut m = String::from("match self {");
                    for v in vs {
                        let _ = write!(
                            m,
                            "{} => {},",
                            v.pattern("__self"),
                            fmt_shape(v, &|i| format!("__self_{i}"))
                        );
                    }
                    if vs.is_empty() {
                        m.push_str("_ => match *self {}");
                    }
                    m.push('}');
                    m
                }
            };
            src = header("::core::fmt::Debug")
                + &format!(
                    "{{ #[inline] fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {{ {body} }} }}"
                );
        }
        BuiltinMacro::DerivePartialEq => {
            let body = match &shape {
                ItemShape::Union => {
                    return Err(err(span, "this trait cannot be derived for unions"));
                }
                ItemShape::Struct(s) => conj(
                    &(0..s.fields.len())
                        .map(|i| format!("self.{0} == other.{0}", s.fields[i]))
                        .collect::<Vec<_>>(),
                ),
                ItemShape::Enum(vs) => enum_pairs(
                    vs,
                    "true",
                    |v| {
                        conj(
                            &(0..v.fields.len())
                                .map(|i| format!("__self_{i} == __arg1_{i}"))
                                .collect::<Vec<_>>(),
                        )
                    },
                    |discr_eq, m| match m {
                        Some(m) => format!("{discr_eq} && {m}"),
                        None => discr_eq.to_string(),
                    },
                ),
            };
            src = header("::core::cmp::PartialEq")
                + &format!("{{ #[inline] fn eq(&self, other: &Self) -> bool {{ {body} }} }}");
            src.push_str(&format!(" #[automatically_derived] impl ::core::marker::StructuralPartialEq for {PLACEHOLDER} {{}}"));
        }
        BuiltinMacro::DeriveHash => {
            let body = match &shape {
                ItemShape::Union => {
                    return Err(err(span, "this trait cannot be derived for unions"));
                }
                ItemShape::Struct(s) => s
                    .fields
                    .iter()
                    .map(|f| format!("::core::hash::Hash::hash(&self.{f}, state);"))
                    .collect::<String>(),
                ItemShape::Enum(vs) => {
                    let mut out = String::new();
                    if vs.len() > 1 {
                        out.push_str("let __self_discr = ::core::intrinsics::discriminant_value(self); ::core::hash::Hash::hash(&__self_discr, state);");
                    }
                    if vs.iter().any(|v| !v.fields.is_empty()) {
                        out.push_str("match self {");
                        for v in vs.iter().filter(|v| !v.fields.is_empty()) {
                            let h: String = (0..v.fields.len())
                                .map(|i| format!("::core::hash::Hash::hash(__self_{i}, state);"))
                                .collect();
                            let _ = write!(out, "{} => {{ {h} }}", v.pattern("__self"));
                        }
                        out.push_str("_ => {} }");
                    }
                    out
                }
            };
            src = header("::core::hash::Hash")
                + &format!(
                    "{{ #[inline] fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) {{ {body} }} }}"
                );
        }
        BuiltinMacro::DerivePartialOrd | BuiltinMacro::DeriveOrd => {
            let partial = b == BuiltinMacro::DerivePartialOrd;
            let (tr, method, ret, equal) = if partial {
                (
                    "::core::cmp::PartialOrd",
                    "partial_cmp",
                    "::core::option::Option<::core::cmp::Ordering>",
                    "::core::option::Option::Some(::core::cmp::Ordering::Equal)",
                )
            } else {
                (
                    "::core::cmp::Ord",
                    "cmp",
                    "::core::cmp::Ordering",
                    "::core::cmp::Ordering::Equal",
                )
            };
            // Lexicographic: the first field that isn't equal decides.
            let chain = |pairs: Vec<(String, String)>| -> String {
                let mut expr = equal.to_string();
                for (a, b) in pairs.into_iter().rev() {
                    expr = if expr == equal {
                        format!("{tr}::{method}({a}, {b})")
                    } else {
                        format!(
                            "match {tr}::{method}({a}, {b}) {{ {equal} => {expr}, cmp => cmp }}"
                        )
                    };
                }
                expr
            };
            let body = match &shape {
                ItemShape::Union => {
                    return Err(err(span, "this trait cannot be derived for unions"));
                }
                ItemShape::Struct(s) => chain(
                    s.fields
                        .iter()
                        .map(|f| (format!("&self.{f}"), format!("&other.{f}")))
                        .collect(),
                ),
                ItemShape::Enum(vs) => {
                    let discr = format!("{tr}::{method}(&__self_discr, &__arg1_discr)");
                    let mut out = String::from(
                        "let __self_discr = ::core::intrinsics::discriminant_value(self); let __arg1_discr = ::core::intrinsics::discriminant_value(other);",
                    );
                    if vs.iter().any(|v| !v.fields.is_empty()) {
                        out.push_str("match (self, other) {");
                        for v in vs.iter().filter(|v| !v.fields.is_empty()) {
                            let c = chain(
                                (0..v.fields.len())
                                    .map(|i| (format!("__self_{i}"), format!("__arg1_{i}")))
                                    .collect(),
                            );
                            let _ = write!(
                                out,
                                "({}, {}) => {c},",
                                v.pattern("__self"),
                                v.pattern("__arg1")
                            );
                        }
                        let _ = write!(out, "_ => {discr} }}");
                    } else {
                        out.push_str(&discr);
                    }
                    out
                }
            };
            src = header(tr)
                + &format!(
                    "{{ #[inline] fn {method}(&self, other: &Self) -> {ret} {{ {body} }} }}"
                );
        }
        BuiltinMacro::DeriveDefault => {
            let body = match &shape {
                ItemShape::Union => {
                    return Err(err(span, "this trait cannot be derived for unions"));
                }
                ItemShape::Struct(s) => s.construct(&vec![
                    "::core::default::Default::default()"
                        .to_string();
                    s.fields.len()
                ]),
                ItemShape::Enum(vs) => match vs.iter().find(|v| v.is_default) {
                    Some(v) if v.kind == FieldsKind::Unit => v.path.clone(),
                    Some(_) => {
                        return Err(err(
                            span,
                            "the `#[default]` attribute may only be used on unit enum variants",
                        ));
                    }
                    None => return Err(err(span, "no default declared").code("E0665")),
                },
            };
            src = header("::core::default::Default")
                + &format!("{{ #[inline] fn default() -> Self {{ {body} }} }}");
        }
        _ => {
            return Err(err(
                span,
                format!("`#[derive({b:?})]` isn't supported by hyprc yet"),
            ));
        }
    }
    Ok(tokens_of(&src, span))
}

/// `a && b && …` (`true` for none).
fn conj(parts: &[String]) -> String {
    if parts.is_empty() {
        "true".into()
    } else {
        parts.join(" && ")
    }
}

/// Comparisons of two enum values: by discriminant, then the fields of equal variants.
/// `field_cmp` compares a variant's bound fields; `combine` joins the discriminant test with
/// the match over variants (`None` when no variant has fields).
fn enum_pairs(
    vs: &[Shape],
    fallback: &str,
    field_cmp: impl Fn(&Shape) -> String,
    combine: impl Fn(&str, Option<String>) -> String,
) -> String {
    let with_fields: Vec<&Shape> = vs.iter().filter(|v| !v.fields.is_empty()).collect();
    let m = (!with_fields.is_empty()).then(|| {
        let mut m = String::from("match (self, other) {");
        for v in &with_fields {
            let _ = write!(
                m,
                "({}, {}) => {},",
                v.pattern("__self"),
                v.pattern("__arg1"),
                field_cmp(v)
            );
        }
        let _ = write!(m, "_ => {fallback} }}");
        m
    });
    if vs.len() <= 1 {
        return m.unwrap_or_else(|| "true".into());
    }
    // The discriminants first, as statements (a leading block would end the expression).
    let lets = "let __self_discr = ::core::intrinsics::discriminant_value(self); let __arg1_discr = ::core::intrinsics::discriminant_value(other);";
    format!("{lets} {}", combine("__self_discr == __arg1_discr", m))
}

/// Puts the derived item's generics and self type into the impls a derive produced.
pub(crate) fn finish(r: &Resolver<'_>, item: DefId, items: &mut [P<ast::Item>]) {
    let ItemNode::Item(it) = &r.nodes[item.0 as usize] else {
        return;
    };
    let generics = match &it.kind {
        ast::ItemKind::Struct(_, g) | ast::ItemKind::Enum(_, g) | ast::ItemKind::Union(_, g) => g,
        _ => return,
    };
    // Field types that are projections of type parameters (`I::Item` in
    // `peeked: Option<I::Item>`) get the derived trait as a where-clause too, as in rustc.
    let ty_params: Vec<Symbol> = generics
        .params
        .iter()
        .filter(|p| matches!(p.kind, ast::GenericParamKind::Type { .. }))
        .map(|p| p.ident.name)
        .collect();
    let mut projections: Vec<P<ast::Ty>> = Vec::new();
    let field_tys: Vec<&P<ast::Ty>> = match &it.kind {
        ast::ItemKind::Struct(d, _) | ast::ItemKind::Union(d, _) => {
            d.fields().iter().map(|f| &f.ty).collect()
        }
        ast::ItemKind::Enum(e, _) => e
            .variants
            .iter()
            .flat_map(|v| v.data.fields().iter().map(|f| &f.ty))
            .collect(),
        _ => Vec::new(),
    };
    for t in field_tys {
        find_param_projections(t, &ty_params, &mut projections);
    }
    let placeholder = Symbol::intern(PLACEHOLDER);
    for imp in items.iter_mut() {
        let ast::ItemKind::Impl(imp) = &mut imp.kind else {
            continue;
        };
        if !matches!(&imp.self_ty.kind, ast::TyKind::Path(None, p) if p.is_ident(placeholder)) {
            continue;
        }
        let span = imp.self_ty.span;
        let bound_path = imp.of_trait.as_ref().map(|t| t.path.clone());
        let mut g = generics.clone();
        let mut args = Vec::with_capacity(g.params.len());
        for p in &mut g.params {
            p.attrs.clear();
            match &mut p.kind {
                ast::GenericParamKind::Lifetime => args.push(ast::AngleBracketedArg::Arg(
                    ast::GenericArg::Lifetime(ast::Lifetime {
                        id: ast::NodeId::DUMMY,
                        ident: p.ident,
                    }),
                )),
                ast::GenericParamKind::Type { default } => {
                    *default = None;
                    // Marker impls with no bound needed (`StructuralPartialEq`) get none.
                    if let Some(path) = &bound_path
                        && !path
                            .segments
                            .last()
                            .is_some_and(|s| s.ident.name.as_str() == "StructuralPartialEq")
                    {
                        p.bounds.push(ast::GenericBound::Trait(ast::PolyTraitRef {
                            bound_generic_params: Vec::new(),
                            modifiers: ast::TraitBoundModifiers::default(),
                            trait_ref: ast::TraitRef {
                                path: path.clone(),
                                ref_id: ast::NodeId::DUMMY,
                            },
                            span,
                            parens: false,
                        }));
                    }
                    args.push(ast::AngleBracketedArg::Arg(ast::GenericArg::Type(path_ty(
                        p.ident,
                    ))));
                }
                ast::GenericParamKind::Const { default, .. } => {
                    *default = None;
                    args.push(ast::AngleBracketedArg::Arg(ast::GenericArg::Type(path_ty(
                        p.ident,
                    ))));
                }
            }
        }
        let mut seg = ast::PathSegment::from_ident(it.ident);
        if !args.is_empty() {
            seg.args = Some(Box::new(ast::GenericArgs::AngleBracketed { args, span }));
        }
        if let Some(path) = &bound_path
            && !path
                .segments
                .last()
                .is_some_and(|s| s.ident.name.as_str() == "StructuralPartialEq")
        {
            for t in &projections {
                g.where_clause.predicates.push(ast::WherePredicate {
                    attrs: Vec::new(),
                    kind: ast::WherePredicateKind::Bound {
                        bound_generic_params: Vec::new(),
                        bounded_ty: t.clone(),
                        bounds: vec![ast::GenericBound::Trait(ast::PolyTraitRef {
                            bound_generic_params: Vec::new(),
                            modifiers: ast::TraitBoundModifiers::default(),
                            trait_ref: ast::TraitRef {
                                path: path.clone(),
                                ref_id: ast::NodeId::DUMMY,
                            },
                            span,
                            parens: false,
                        })],
                    },
                    id: ast::NodeId::DUMMY,
                    span,
                });
            }
        }
        imp.generics = g;
        imp.self_ty = Box::new(ast::Ty {
            id: ast::NodeId::DUMMY,
            kind: ast::TyKind::Path(
                None,
                ast::Path {
                    span,
                    segments: vec![seg],
                },
            ),
            span,
        });
    }
}

fn path_ty(ident: Ident) -> P<ast::Ty> {
    Box::new(ast::Ty {
        id: ast::NodeId::DUMMY,
        kind: ast::TyKind::Path(None, ast::Path::from_ident(ident)),
        span: ident.span,
    })
}

/// Types in a field type that are projections of the item's type parameters: `I::Item`,
/// `<I as Iterator>::Item` (each once).
fn find_param_projections(t: &ast::Ty, params: &[Symbol], out: &mut Vec<P<ast::Ty>>) {
    match &t.kind {
        ast::TyKind::Path(qself, path) => {
            let is_projection = match qself {
                Some(q) => mentions_param(&q.ty, params),
                None => path.segments.len() > 1 && params.contains(&path.segments[0].ident.name),
            };
            if is_projection {
                out.push(Box::new(t.clone()));
            }
            for seg in &path.segments {
                if let Some(args) = &seg.args
                    && let ast::GenericArgs::AngleBracketed { args, .. } = &**args
                {
                    for a in args {
                        if let ast::AngleBracketedArg::Arg(ast::GenericArg::Type(t)) = a {
                            find_param_projections(t, params, out);
                        }
                    }
                }
            }
        }
        ast::TyKind::Ref(_, m) | ast::TyKind::Ptr(m) => find_param_projections(&m.ty, params, out),
        ast::TyKind::Slice(t) | ast::TyKind::Array(t, _) | ast::TyKind::Paren(t) => {
            find_param_projections(t, params, out)
        }
        ast::TyKind::Tup(ts) => ts
            .iter()
            .for_each(|t| find_param_projections(t, params, out)),
        _ => {}
    }
}

fn mentions_param(t: &ast::Ty, params: &[Symbol]) -> bool {
    match &t.kind {
        ast::TyKind::Path(None, p) => p
            .segments
            .first()
            .is_some_and(|s| params.contains(&s.ident.name)),
        ast::TyKind::Path(Some(q), _) => mentions_param(&q.ty, params),
        ast::TyKind::Ref(_, m) | ast::TyKind::Ptr(m) => mentions_param(&m.ty, params),
        _ => false,
    }
}
