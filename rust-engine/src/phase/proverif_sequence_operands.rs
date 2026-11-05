//! ProVerif-backend phase: keep the Rust evaluation order of operands.
//!
//! Two later steps evaluate operands in another order than Rust, which
//! reorders the events of hand-written models, or lets a failure end the trace
//! before an earlier event:
//!  - `HoistSideEffects` lifts the `let`s, `?`s, `return`s and assignments of
//!    an operand above the earlier operands, which it leaves in place;
//!  - `ProverifExpandStructUpdate` builds a record in declaration order, after
//!    binding its base.
//!
//! This phase binds such earlier operands, and every field of such records, to
//! locals in Rust order. The second operand of `&&` and `||`, which may not
//! run, becomes a branch instead. The lowering of `&mut` calls and of
//! assignments reorders and duplicates code too; this phase rejects the code
//! where that may be observable.

use std::collections::{HashMap, HashSet};

use crate::ast::literals::Literal;
use crate::ast::visitors::*;
use crate::ast::*;
use crate::backends::proverif::analysis::fn_decls;
use crate::backends::proverif::generated_local;
use crate::names::rust_primitives::hax::{logical_op_and, logical_op_or};
use crate::phase::Phase;
use crate::phase::proverif_result_soundness::{
    LIBRARY_CRATES, diagnostic, leaves, replace_by_error,
};
use hax_lib_macros_types::AttrPayload;

/// Phase binding operands in Rust evaluation order.
#[derive(Default, Debug)]
pub struct ProverifSequenceOperands;

/// Whether hoisting may move code out of `e`, before what precedes it: a
/// `let` outside a branch or a closure (in a loop body too), or code that
/// leaves or assigns.
pub(crate) fn hoists(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Let { .. }
        | ExprKind::Return { .. }
        | ExprKind::Break { .. }
        | ExprKind::Continue { .. }
        | ExprKind::Assign { .. } => true,
        ExprKind::If {
            condition,
            then,
            else_,
        } => hoists(condition) || leaves(then) || else_.as_ref().is_some_and(leaves),
        ExprKind::Match { scrutinee, arms } => {
            hoists(scrutinee) || arms.iter().any(|a| leaves(&a.body))
        }
        ExprKind::Closure { .. } => false,
        _ => {
            struct Finder(bool);
            impl AstVisitor for Finder {
                fn visit_expr(&mut self, e: &Expr) {
                    self.0 |= hoists(e);
                }
            }
            let mut finder = Finder(false);
            finder.visit_inner(e);
            finder.0
        }
    }
}

/// Whether `e` is a call taking a `&mut`, which the lowering of `&mut` turns
/// into a `let` that updates the borrowed place. A reborrow `&mut *x` is not.
fn is_mut_call(e: &Expr) -> bool {
    matches!(&*e.kind, ExprKind::App { head, args, .. }
        if args.iter().any(borrows_mut)
            && !matches!(&*head.kind, ExprKind::GlobalId(g)
                if *g == crate::names::rust_primitives::hax::deref_op))
}

/// Whether `e` holds a call taking a `&mut` outside a closure, in a branch
/// too.
fn calls_with_mut(e: &Expr) -> bool {
    struct Finder(bool);
    impl AstVisitor for Finder {
        fn visit_expr(&mut self, e: &Expr) {
            match &*e.kind {
                ExprKind::Closure { .. } => {}
                _ if is_mut_call(e) => self.0 = true,
                _ => self.visit_inner(e),
            }
        }
    }
    let mut finder = Finder(false);
    finder.visit_expr(e);
    finder.0
}

/// The index expressions of the place `e`.
fn place_indices(e: &Expr) -> Vec<&Expr> {
    match &*e.kind {
        ExprKind::Ascription { e, .. } | ExprKind::Borrow { inner: e, .. } => place_indices(e),
        ExprKind::App { args, .. } => {
            let mut out: Vec<&Expr> = args.iter().skip(1).collect();
            out.extend(args.first().map(place_indices).unwrap_or_default());
            out
        }
        _ => vec![],
    }
}

/// The operands that a later operand moving up (it hoists or calls a function
/// taking a `&mut`) may overtake: those that call something, or read a
/// variable it writes.
fn hazards(ops: &[&Expr]) -> HashSet<usize> {
    let mut out = HashSet::new();
    for (j, later) in ops.iter().enumerate() {
        if !(hoists(later) || calls_with_mut(later)) {
            continue;
        }
        let written = written_locals(later);
        for (i, earlier) in ops[..j].iter().enumerate() {
            if !trivial(earlier) || written.iter().any(|x| mentions(x, earlier)) {
                out.insert(i);
            }
        }
    }
    out
}

/// The locals that `e` assigns or borrows mutably, outside a closure.
fn written_locals(e: &Expr) -> Vec<LocalId> {
    struct Finder(Vec<LocalId>);
    impl AstVisitor for Finder {
        fn visit_expr(&mut self, e: &Expr) {
            match &*e.kind {
                ExprKind::Closure { .. } => {}
                ExprKind::Borrow {
                    mutable: true,
                    inner,
                } => {
                    self.0.extend(locals(inner));
                    self.visit_inner(e)
                }
                ExprKind::Assign { lhs, .. } => {
                    self.0.extend(lhs_locals(lhs));
                    self.visit_inner(e)
                }
                _ => self.visit_inner(e),
            }
        }
    }
    let mut finder = Finder(vec![]);
    finder.visit_expr(e);
    finder.0
}

/// The local an assignment to `l` updates, if it is one.
fn lhs_root(l: &Lhs) -> Option<&LocalId> {
    match l {
        Lhs::LocalVar { var, .. } => Some(var),
        Lhs::ArrayAccessor { e, .. } | Lhs::FieldAccessor { e, .. } | Lhs::VecRef { e, .. } => {
            lhs_root(e)
        }
        Lhs::ArbitraryExpr(_) => None,
    }
}

/// The locals an assignment to `l` may update: its root, or the locals of a
/// place such as `*p`, which it writes through.
fn lhs_locals(l: &Lhs) -> Vec<LocalId> {
    match l {
        Lhs::LocalVar { var, .. } => vec![var.clone()],
        Lhs::ArrayAccessor { e, .. } | Lhs::FieldAccessor { e, .. } | Lhs::VecRef { e, .. } => {
            lhs_locals(e)
        }
        Lhs::ArbitraryExpr(e) => locals(e),
    }
}

/// The locals that `e` mentions.
fn locals(e: &Expr) -> Vec<LocalId> {
    struct Finder(Vec<LocalId>);
    impl AstVisitor for Finder {
        fn enter_expr_kind(&mut self, kind: &ExprKind) {
            if let ExprKind::LocalId(x) = kind {
                self.0.push(x.clone());
            }
        }
    }
    let mut finder = Finder(vec![]);
    finder.visit_expr(e);
    finder.0
}

/// Whether `e` mentions the local `x`.
fn mentions(x: &LocalId, e: &Expr) -> bool {
    struct Finder<'a>(&'a LocalId, bool);
    impl AstVisitor for Finder<'_> {
        fn enter_expr_kind(&mut self, kind: &ExprKind) {
            self.1 |= matches!(kind, ExprKind::LocalId(y) if y == self.0);
        }
    }
    let mut finder = Finder(x, false);
    finder.visit_expr(e);
    finder.1
}

/// Why the lowering of `&mut` or of assignments may evaluate `e` in another
/// order than Rust, or more than once, if it may.
fn mut_ordering(e: &Expr) -> Option<&'static str> {
    let ops = match &*e.kind {
        ExprKind::App { head, args, .. } => match &*head.kind {
            ExprKind::GlobalId(_) => args.iter().collect(),
            _ => std::iter::once(head).chain(args).collect(),
        },
        ExprKind::Construct { fields, base, .. } => {
            fields.iter().map(|(_, f)| f).chain(base).collect()
        }
        ExprKind::Array(es) => es.iter().collect(),
        _ => vec![],
    };
    // Hoisting moves the bindings of a guard into its arm, after the test.
    if let ExprKind::Match { arms, .. } = &*e.kind
        && arms.iter().any(|a| {
            a.guard.as_ref().is_some_and(|g| {
                let GuardKind::IfLet { rhs, .. } = &g.kind;
                hoists(rhs) || calls_with_mut(rhs)
            })
        })
    {
        return Some(
            "this guard holds a `?`, a `return`, an assignment, a `let` or a call taking a \
             `&mut`, which the model would run after testing the guard; move it out of the \
             guard",
        );
    }
    // Rust reads an indexed place after the index, which the model reads
    // before.
    if let ExprKind::App { head, args, .. } = &*e.kind
        && matches!(&*head.kind, ExprKind::GlobalId(g)
            if [
                crate::names::core::ops::index::Index::index,
                crate::names::core::ops::index::IndexMut::index_mut,
            ]
            .contains(g))
        && let [base, rest @ ..] = &args[..]
        && rest
            .iter()
            .flat_map(written_locals)
            .any(|x| mentions(&x, base))
    {
        return Some(
            "this index assigns, or calls a function taking a `&mut` of, a variable of the \
             indexed place, which the model would read before the index; bind the index with \
             a `let` first",
        );
    }
    if is_mut_call(e) {
        let moving = !hazards(&ops).is_empty();
        let index = ops.iter().any(|o| {
            matches!(&*o.kind, ExprKind::Borrow { mutable: true, inner }
                if is_place(inner) && !place_indices(inner).into_iter().all(trivial))
        });
        if moving {
            return Some(
                "this call takes a `&mut`, so its arguments stay in place, and one that calls \
                 something comes before one that holds a `?`, a `return`, a `break`, a \
                 `continue`, an assignment, a `let` or another such call, which the model would \
                 run first; bind the arguments with `let`s before the call",
            );
        }
        // The lowering evaluates the indices of a `&mut` place before the
        // other arguments, which Rust evaluates first: a computed index needs
        // every other argument to be trivial, `&mut` temporaries included (the
        // `&mut` places are checked by their own indices).
        let computed_index = |o: &&Expr| {
            matches!(&*o.kind, ExprKind::Borrow { mutable: true, inner }
                if is_place(inner) && !place_indices(inner).into_iter().all(is_leaf_index))
        };
        let late_index = ops.iter().any(computed_index) && !ops.iter().all(|o| {
            trivial(o)
                || matches!(&*o.kind, ExprKind::Borrow { mutable: true, inner } if is_place(inner))
        });
        if late_index {
            return Some(
                "this call takes a `&mut` of an element whose index is computed, which the model \
                 evaluates before the other arguments, as Rust does not; bind the index with a \
                 `let` first",
            );
        }
        if index {
            return Some(
                "this call takes a `&mut` of an element whose index calls something that may \
                 be observable, which the model may evaluate twice; bind the index with a `let` \
                 first",
            );
        }
    }
    if let ExprKind::Assign { lhs, value, .. } = &*e.kind {
        // `x += f(&mut ..)` reads `x` before the call, where Rust reads it
        // after.
        // `a[i] = f(&mut i)` too: the place is read before the value.
        fn index_locals(l: &Lhs, out: &mut Vec<LocalId>) {
            match l {
                Lhs::ArrayAccessor { e, index, .. } => {
                    out.extend(locals(index));
                    index_locals(e, out)
                }
                Lhs::FieldAccessor { e, .. } | Lhs::VecRef { e, .. } => index_locals(e, out),
                Lhs::LocalVar { .. } | Lhs::ArbitraryExpr(_) => {}
            }
        }
        let mut place = vec![];
        index_locals(lhs, &mut place);
        place.extend(lhs_locals(lhs));
        let opaque_place = lhs_root(lhs).is_none();
        let updates = |x: &LocalId| mut_borrows(x, value) || assigns(Some(x), value);
        if opaque_place && (calls_with_mut(value) || assigns(None, value))
            || place.iter().any(updates)
        {
            return Some(
                "this assigns a value that assigns, or calls a function taking a `&mut` of, a \
                 variable of the assigned place, which the model may read before; bind the \
                 value with a `let` first",
            );
        }
        fn indices_ok(l: &Lhs) -> bool {
            match l {
                Lhs::ArrayAccessor { e, index, .. } => trivial(index) && indices_ok(e),
                Lhs::FieldAccessor { e, .. } | Lhs::VecRef { e, .. } => indices_ok(e),
                Lhs::LocalVar { .. } | Lhs::ArbitraryExpr(_) => true,
            }
        }
        if !indices_ok(lhs) {
            return Some(
                "this assigns an element whose index calls something that may be observable, \
                 which the model may evaluate twice or out of order; bind the index with a `let` \
                 first",
            );
        }
        // Rust evaluates the value before the index, which may fail.
        fn leaf_indices(l: &Lhs) -> bool {
            match l {
                Lhs::ArrayAccessor { e, index, .. } => is_leaf_index(index) && leaf_indices(e),
                Lhs::FieldAccessor { e, .. } | Lhs::VecRef { e, .. } => leaf_indices(e),
                Lhs::LocalVar { .. } | Lhs::ArbitraryExpr(_) => true,
            }
        }
        if !trivial(value) && !leaf_indices(lhs) {
            return Some(
                "this assigns a value that calls something to an element whose index is computed, \
                 which the model evaluates before the value, as Rust does not; bind the index \
                 with a `let` first",
            );
        }
    }
    None
}

/// Whether `e` assigns the local `x`, or a part of it (any place, without
/// `x`), outside a closure.
fn assigns(x: Option<&LocalId>, e: &Expr) -> bool {
    struct Finder<'a>(Option<&'a LocalId>, bool);
    impl AstVisitor for Finder<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            match &*e.kind {
                ExprKind::Closure { .. } => {}
                ExprKind::Assign { lhs, .. } => {
                    self.1 |= match (lhs_root(lhs), self.0) {
                        (Some(y), Some(x)) => y == x,
                        _ => true,
                    };
                    self.visit_inner(e)
                }
                _ => self.visit_inner(e),
            }
        }
    }
    let mut finder = Finder(x, false);
    finder.visit_expr(e);
    finder.1
}

/// Whether `e` borrows the local `x`, or a part of it, mutably.
fn mut_borrows(x: &LocalId, e: &Expr) -> bool {
    struct Finder<'a>(&'a LocalId, bool);
    impl AstVisitor for Finder<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let ExprKind::Borrow {
                mutable: true,
                inner,
            } = &*e.kind
            {
                self.1 |= mentions(self.0, inner);
            }
            self.visit_inner(e)
        }
    }
    let mut finder = Finder(x, false);
    finder.visit_expr(e);
    finder.1
}

/// Whether `ty` is `()`, or a tuple of one such type, which the lowering of
/// `&mut` treats as `()`.
fn unit_like(ty: &Ty) -> bool {
    *ty.kind() == TyKind::unit()
        || matches!(ty.kind(), TyKind::App { head, args }
            if *head == GlobalId::from(global_id::TupleId::Type { length: 1 })
                && matches!(&args[..], [GenericValue::Ty(t)] if unit_like(t)))
}

/// Whether the index `e` is a local, a literal or a constant, which cannot
/// fail.
fn is_leaf_index(e: &Expr) -> bool {
    matches!(
        &*e.kind,
        ExprKind::LocalId(_) | ExprKind::Literal(_) | ExprKind::GlobalId(_)
    )
}

/// Whether `e` is a `&mut`.
fn borrows_mut(e: &Expr) -> bool {
    matches!(&*e.kind, ExprKind::Borrow { mutable: true, .. })
}

/// Whether evaluating `e` can do nothing observable, so that its place in the
/// evaluation order does not matter: it calls nothing but constructors,
/// projections, dereferences and functions of hax's libraries that are not
/// trait methods, take no impls (either may run an impl of the crate) and take
/// no `&mut`. Such a call may still fail: it stays in place, and the rules on
/// indices and struct-update bases keep the lowering from moving it ahead of
/// an observable operand.
fn trivial(e: &Expr) -> bool {
    struct Finder(bool);
    impl AstVisitor for Finder {
        fn visit_expr(&mut self, e: &Expr) {
            match &*e.kind {
                ExprKind::App {
                    head,
                    args,
                    trait_,
                    bounds_impls,
                    ..
                } => {
                    self.0 &= matches!(&*head.kind, ExprKind::GlobalId(g)
                        if g.is_constructor()
                            || g.is_projector()
                            || *g == crate::names::rust_primitives::hax::deref_op
                            || trait_.is_none()
                                && bounds_impls.is_empty()
                                && LIBRARY_CRATES.contains(&g.krate())
                                // A call taking a `&mut` updates a place.
                                && !args.iter().any(borrows_mut));
                    args.iter().for_each(|a| self.visit_expr(a))
                }
                ExprKind::GlobalId(g) => self.0 &= g.is_constructor(),
                ExprKind::Quote { .. } | ExprKind::Error(_) => self.0 = false,
                _ => self.visit_inner(e),
            }
        }
    }
    let mut finder = Finder(true);
    finder.visit_expr(e);
    finder.0 && !hoists(e)
}

#[derive(Default)]
struct Sequence {
    /// The declared return type of each function of the crate.
    outputs: HashMap<GlobalId, Ty>,
    /// The position of each field of the crate's constructors in the model,
    /// which sorts them by their `Order` attribute, then by declaration.
    field_order: HashMap<GlobalId, HashMap<GlobalId, usize>>,
    /// The number of locals introduced so far in the current item.
    fresh: usize,
}

impl Sequence {
    /// Replaces `operand` by a fresh local, and returns the binding.
    fn bind(&mut self, operand: &mut Expr) -> (LocalId, Expr) {
        let var = generated_local(&format!("hax__operand{}", self.fresh));
        self.fresh += 1;
        let local = ExprKind::LocalId(var.clone()).promote(operand.ty.clone(), operand.meta.span);
        (var, std::mem::replace(operand, local))
    }

    /// Binds the operands of `e` at `indices`, in this order.
    fn bind_operands(&mut self, e: &mut Expr, indices: &[usize]) {
        let mut bindings = vec![];
        {
            let mut operands = operands(e);
            for &i in indices {
                bindings.push(self.bind(operands[i]));
            }
        }
        let (ty, span) = (e.ty.clone(), e.meta.span);
        let mut body = std::mem::replace(
            e,
            ExprKind::Literal(Literal::Bool(false)).promote(ty.clone(), span),
        );
        for (var, rhs) in bindings.into_iter().rev() {
            body = ExprKind::Let {
                lhs: PatKind::var_pat(var).promote(rhs.ty.clone(), span),
                rhs,
                body,
            }
            .promote(ty.clone(), span);
        }
        *e = body;
    }

    /// The indices of the operands of `e` to bind, in Rust order.
    fn to_bind(&self, e: &mut Expr) -> Vec<usize> {
        // A closure does nothing until it is called.
        let bindable = |o: &Expr| {
            !trivial(o)
                && !matches!(
                    &*o.kind,
                    ExprKind::Borrow { mutable: true, .. }
                        | ExprKind::AddressOf { .. }
                        | ExprKind::Closure { .. }
                )
        };
        // The lowering of `&mut` needs the operands of a call taking one to
        // stay in place; the check rejects those that this reorders.
        if matches!(&*e.kind, ExprKind::App { args, .. } if args.iter().any(borrows_mut)) {
            return vec![];
        }
        let ops = operands(e);
        // An operand must be bound when it calls something, or when it reads a
        // variable that a later operand that moves up writes.
        let hazards = hazards(&ops.iter().map(|o| &**o).collect::<Vec<_>>());
        let nontrivial: Vec<usize> = (0..ops.len())
            .filter(|i| {
                !matches!(
                    &*ops[*i].kind,
                    ExprKind::Borrow { mutable: true, .. }
                        | ExprKind::AddressOf { .. }
                        | ExprKind::Closure { .. }
                ) && (bindable(ops[*i]) || hazards.contains(i))
            })
            .collect();
        let mut out: Vec<usize> = nontrivial
            .iter()
            .copied()
            .filter(|i| hazards.contains(i))
            .collect();
        if let ExprKind::Construct {
            constructor,
            fields,
            base,
            ..
        } = &*e.kind
            && constructor.expect_tuple().is_none()
        {
            // A base whose fields are all overwritten is dropped later, but
            // still evaluated in Rust, after the fields.
            let base_evaluated = base
                .as_ref()
                .is_some_and(|b| !matches!(&*b.kind, ExprKind::LocalId(_)));
            let order = self.field_order.get(constructor);
            let positions: Vec<Option<usize>> = fields
                .iter()
                .map(|(f, _)| order.and_then(|o| o.get(f).copied()))
                .collect();
            let in_order = positions
                .windows(2)
                .all(|w| matches!(w, [Some(i), Some(j)] if i < j));
            // The base is read after the fields, which may update it.
            let field_moves =
                base.is_some() && fields.iter().any(|(_, f)| hoists(f) || calls_with_mut(f));
            if base_evaluated
                || field_moves
                || nontrivial.len() > 1 && (!in_order || base.is_some())
            {
                out = nontrivial;
            }
        }
        out
    }
}

/// Whether `e` is a place: a local, or a field, an element or the target of a
/// place, possibly reborrowed.
fn is_place(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::LocalId(_) => true,
        ExprKind::Ascription { e, .. } | ExprKind::Borrow { inner: e, .. } => is_place(e),
        ExprKind::App { head, args, .. } => {
            matches!(&*head.kind, ExprKind::GlobalId(g)
                if g.is_projector()
                    || [
                        crate::names::core::ops::index::Index::index,
                        crate::names::core::ops::index::IndexMut::index_mut,
                        crate::names::core::ops::deref::Deref::deref,
                        crate::names::core::ops::deref::DerefMut::deref_mut,
                        crate::names::rust_primitives::hax::deref_op,
                    ]
                    .contains(g))
                && args.first().is_some_and(is_place)
        }
        _ => false,
    }
}

/// The operands of `e`, in Rust evaluation order: the arguments of a call,
/// after its head if that is not a function name; the fields of a record, then
/// its base; the elements of an array.
fn operands(e: &mut Expr) -> Vec<&mut Expr> {
    match &mut *e.kind {
        ExprKind::App { head, args, .. } => match &*head.kind {
            ExprKind::GlobalId(_) => args.iter_mut().collect(),
            _ => std::iter::once(head).chain(args.iter_mut()).collect(),
        },
        ExprKind::Construct { fields, base, .. } => fields
            .iter_mut()
            .map(|(_, f)| f)
            .chain(base.iter_mut())
            .collect(),
        ExprKind::Array(es) => es.iter_mut().collect(),
        _ => vec![],
    }
}

/// The position of each field of the crate's constructors in the model.
fn field_order(items: &[Item]) -> HashMap<GlobalId, HashMap<GlobalId, usize>> {
    let mut out = HashMap::new();
    for item in items {
        if let ItemKind::Type { variants, .. } = &item.kind {
            for v in variants {
                let mut fields: Vec<(i32, GlobalId)> = v
                    .arguments
                    .iter()
                    .enumerate()
                    .map(|(i, (field, _, attrs))| {
                        let order =
                            crate::attributes::hax_attributes(attrs).find_map(|a| match a {
                                AttrPayload::Order(o) => Some(*o),
                                _ => None,
                            });
                        (order.unwrap_or(i as i32), *field)
                    })
                    .collect();
                fields.sort_by_key(|(o, _)| *o);
                let positions = fields.into_iter().enumerate().map(|(i, (_, f))| (f, i));
                out.insert(v.name, positions.collect());
            }
        }
    }
    out
}

impl AstVisitorMut for Sequence {
    fn visit_expr(&mut self, e: &mut Expr) {
        self.visit_inner(e);
        if let ExprKind::App { head, args, .. } = &mut *e.kind
            && let ExprKind::GlobalId(g) = &*head.kind
            && (*g == logical_op_and || *g == logical_op_or)
            && args.len() == 2
            && (hoists(&args[1]) || calls_with_mut(&args[1]))
        {
            let (ty, span) = (e.ty.clone(), e.meta.span);
            let lit = |b: bool| ExprKind::Literal(Literal::Bool(b)).promote(ty.clone(), span);
            let and = *g == logical_op_and;
            let second = args.pop().unwrap();
            let first = args.pop().unwrap();
            let (then, else_) = if and {
                (second, lit(false))
            } else {
                (lit(true), second)
            };
            *e = ExprKind::If {
                condition: first,
                then,
                else_: Some(else_),
            }
            .promote(ty, span);
            return;
        }
        if let Some(what) = mut_ordering(e).or_else(|| self.unit_instance(e)) {
            let d = diagnostic(
                e.clone(),
                e.meta.span,
                stringify!(ProverifSequenceOperands),
                what.into(),
            );
            return replace_by_error(e, vec![d]);
        }
        let indices = self.to_bind(e);
        if !indices.is_empty() {
            self.bind_operands(e, &indices);
        }
    }
}

impl Sequence {
    /// Why the call `e`, which takes a `&mut`, returns `()` only as an
    /// instance of a generic return type: its lowering expects the function to
    /// return `()`, which it does not.
    fn unit_instance(&self, e: &Expr) -> Option<&'static str> {
        let ExprKind::App {
            head, generic_args, ..
        } = &*e.kind
        else {
            return None;
        };
        let ExprKind::GlobalId(g) = &*head.kind else {
            return None;
        };
        let generic = match self.outputs.get(g) {
            Some(output) => !unit_like(output),
            None => generic_args
                .iter()
                .any(|a| matches!(a, GenericValue::Ty(t) if unit_like(t))),
        };
        (is_mut_call(e) && unit_like(&e.ty) && generic).then_some(
            "this call takes a `&mut` and returns `()` as an instance of a generic return type, \
             which the lowering of `&mut` mistakes for a function returning `()`",
        )
    }
}

impl Phase for ProverifSequenceOperands {
    fn apply(&self, items: &mut Vec<Item>) {
        let mut sequence = Sequence {
            outputs: fn_decls(items)
                .map(|d| (d.name, d.body.ty.clone()))
                .collect(),
            field_order: field_order(items),
            ..Default::default()
        };
        // Names restart with each item, so that an item's model does not
        // depend on the others.
        for item in items.iter_mut() {
            sequence.fresh = 0;
            sequence.visit_item(item);
        }
    }
}
