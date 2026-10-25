//! MIR as text, for `--hyprc-dump=mir`.

use crate::mir::*;
use std::fmt::Write;

fn operand(o: &Operand) -> String {
    match o {
        Operand::Copy(p) => format!("{p:?}"),
        Operand::Move(p) => format!("move {p:?}"),
        Operand::Constant(c) => match &c.kind {
            ConstValue::Scalar(v) => format!("const {v}_{}", c.ty),
            ConstValue::ZeroSized => format!("const {}", c.ty),
            ConstValue::Bytes(b) => format!("const {:?}", String::from_utf8_lossy(b)),
            ConstValue::StaticRef(d) => format!("const &static {d:?}"),
            ConstValue::Unevaluated(k) => format!("const {k:?}"),
            ConstValue::Item(d, _) => format!("const item {d:?}"),
        },
    }
}

fn rvalue(r: &Rvalue) -> String {
    match r {
        Rvalue::Use(o) => operand(o),
        Rvalue::Repeat(o, n) => format!("[{}; {n:?}]", operand(o)),
        Rvalue::Ref(m, p) => format!(
            "&{}{p:?}",
            if *m == hyprc_hir::Mutability::Mut {
                "mut "
            } else {
                ""
            }
        ),
        Rvalue::RawPtr(m, p) => format!(
            "&raw {} {p:?}",
            if *m == hyprc_hir::Mutability::Mut {
                "mut"
            } else {
                "const"
            }
        ),
        Rvalue::Len(p) => format!("Len({p:?})"),
        Rvalue::Cast(k, o, t) => format!("{} as {t} ({k:?})", operand(o)),
        Rvalue::BinaryOp(op, a, b) => format!("{op:?}({}, {})", operand(a), operand(b)),
        Rvalue::CheckedBinaryOp(op, a, b) => {
            format!("Checked{op:?}({}, {})", operand(a), operand(b))
        }
        Rvalue::UnaryOp(op, a) => format!("{op:?}({})", operand(a)),
        Rvalue::Discriminant(p) => format!("discriminant({p:?})"),
        Rvalue::Aggregate(k, ops) => {
            let ops: Vec<String> = ops.iter().map(operand).collect();
            format!("{k:?} {{ {} }}", ops.join(", "))
        }
        Rvalue::SizeOf(t) => format!("SizeOf({t})"),
        Rvalue::OffsetOf(t, steps) => format!(
            "OffsetOf({t}, {:?})",
            steps.iter().map(|s| (s.0, s.1)).collect::<Vec<_>>()
        ),
        Rvalue::AlignOf(t) => format!("AlignOf({t})"),
        Rvalue::ThreadLocalRef(d) => format!("&thread_local {d:?}"),
        Rvalue::CopyForDeref(p) => format!("deref_copy {p:?}"),
    }
}

pub fn body_to_string(b: &Body) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "fn {:?}({} args) {{", b.source, b.arg_count);
    for (i, l) in b.locals.iter().enumerate() {
        let _ = writeln!(
            s,
            "    let _{i}: {}; {}",
            l.ty,
            l.name.map(|n| format!("// {n}")).unwrap_or_default()
        );
    }
    for (i, bb) in b.blocks.iter().enumerate() {
        let _ = writeln!(s, "  bb{i}: {{");
        for st in &bb.stmts {
            match &st.kind {
                StatementKind::Assign(p, r) => {
                    let _ = writeln!(s, "    {p:?} = {};", rvalue(r));
                }
                StatementKind::SetDiscriminant(p, v) => {
                    let _ = writeln!(s, "    discriminant({p:?}) = {v};");
                }
                StatementKind::StorageLive(l) => {
                    let _ = writeln!(s, "    StorageLive({l:?});");
                }
                StatementKind::StorageDead(l) => {
                    let _ = writeln!(s, "    StorageDead({l:?});");
                }
                StatementKind::Nop => {}
            }
        }
        if let Some(t) = &bb.terminator {
            let text = match &t.kind {
                TerminatorKind::Goto(b) => format!("goto -> {b:?}"),
                TerminatorKind::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                } => {
                    let ts: Vec<String> =
                        targets.iter().map(|(v, b)| format!("{v}: {b:?}")).collect();
                    format!(
                        "switchInt({}) -> [{}, otherwise: {otherwise:?}]",
                        operand(discr),
                        ts.join(", ")
                    )
                }
                TerminatorKind::Return => "return".into(),
                TerminatorKind::Unreachable => "unreachable".into(),
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                } => {
                    let a: Vec<String> = args.iter().map(operand).collect();
                    format!(
                        "{destination:?} = {}({}) -> {target:?}",
                        operand(func),
                        a.join(", ")
                    )
                }
                TerminatorKind::Drop { place, target } => format!("drop({place:?}) -> {target:?}"),
                TerminatorKind::Assert {
                    cond,
                    expected,
                    msg,
                    target,
                } => {
                    format!(
                        "assert({}{}, {msg:?}) -> {target:?}",
                        if *expected { "" } else { "!" },
                        operand(cond)
                    )
                }
                TerminatorKind::InlineAsm { .. } => "asm!(…)".into(),
            };
            let _ = writeln!(s, "    {text};");
        }
        let _ = writeln!(s, "  }}");
    }
    s.push_str("}\n");
    s
}
