//! ProVerif-backend checks that keep each `Result` model sound. They run
//! before the control flow is rewritten, on code close to the Rust source.
//!
//! The default model ends the trace on every `Err`. [`ProverifRejectRecovery`]
//! makes the extracted code use `Result` as an exception: a `Result` is
//! returned or consumed at once (by `?`, a `match`, or a few library methods),
//! and every arm that may see an `Err` returns one or panics, calling nothing
//! that may be observable on the way.
//!
//! Under `--result-errors`, the `Err` of a function whose body is not
//! extracted is a term of its model, not the Rust error value.
//! [`ProverifRejectUnknownErrors`] makes the extracted code treat such a
//! `Result` the same way, except that an arm may recover from its `Err` as long
//! as it does not read the error.
//!
//! `#[hax_lib::pv_unchecked_results]` exempts a function from both checks; its
//! model is then marked with a `HAX WARNING`.

use std::collections::{HashMap, HashSet};

use crate::ast::fragment::Fragment;
use crate::ast::identifiers::global_id::view::{AnyKind, PathSegment, PathSegmentPayload};
use crate::ast::span::Span;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::backends::is_late_skip;
use crate::backends::proverif::analysis::{
    body_is_hidden, fn_decls, quote_text, scan_declared_names,
};
use crate::backends::proverif::{is_kept_call, render_id, warning_attribute};
use crate::names::core::result::Result::Err;
use crate::names::rust_primitives::hax::never_to_any;
use crate::phase::Phase;
use crate::phase::proverif_flatten_binding_subpatterns::is_irrefutable;
use crate::symbol::Symbol;
use hax_lib_macros_types::AttrPayload;
use hax_types::cli_options::Namespace;

/// What a library function does with the `Result` it receives as its first
/// argument.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LibCall {
    /// Returns it, possibly converted, with the same `Err`.
    KeepErr,
    /// Maps the error through its second argument.
    MapErr,
    /// `Option::map`, whose second argument returns a `Result`, at once.
    MapOption,
    /// Panics on an `Err`.
    PanicOnErr,
    /// Reads whether it is an `Err`, and the `Ok` payload.
    ReadOk,
    /// Reads the error.
    ReadErr,
}

/// The method `method` of an inherent impl of the library module `module`,
/// if `g` is one, whatever the impl's number.
fn inherent_method(g: &GlobalId, module: &str, method: &str) -> bool {
    let view = g.view();
    let (modules, rest) = view.split_at_module();
    g.krate() == "core"
        && matches!(rest, [m] if matches!(m.kind(), AnyKind::AssocItem { .. }))
        && modules
            .last()
            .is_some_and(|m| segment_name(m).as_deref() == Some(module))
        && method_name(g).as_deref() == Some(method)
}

/// The name of a path segment, if it has one.
fn segment_name(segment: &PathSegment) -> Option<String> {
    match segment.payload() {
        PathSegmentPayload::Named(s) => Some(s.to_string()),
        PathSegmentPayload::Unnamed(_) => None,
    }
}

/// The name of the method `g`.
fn method_name(g: &GlobalId) -> Option<String> {
    segment_name(g.view().last())
}

/// The methods of each impl of the crate, by name.
fn impl_methods(items: &[Item]) -> HashMap<GlobalId, HashMap<String, GlobalId>> {
    items
        .iter()
        .filter_map(|item| match &item.kind {
            ItemKind::Impl { items, .. } => Some((
                item.ident,
                items
                    .iter()
                    .filter(|ii| matches!(ii.kind, ImplItemKind::Fn { .. }))
                    .filter_map(|ii| Some((method_name(&ii.ident)?, ii.ident)))
                    .collect(),
            )),
            _ => None,
        })
        .collect()
}

/// The method of an impl of the crate that a call of the trait method `g`
/// dispatches to through `impl_`, when that impl is known and defines it.
fn dispatch(
    impls: &HashMap<GlobalId, HashMap<String, GlobalId>>,
    g: &GlobalId,
    impl_: Option<&ImplExpr>,
) -> Option<GlobalId> {
    match &*impl_?.kind {
        ImplExprKind::Concrete(goal) => impls.get(&goal.trait_)?.get(&method_name(g)?).copied(),
        // A generic impl, applied to the impls of its bounds.
        ImplExprKind::ImplApp { impl_, .. } => dispatch(impls, g, Some(impl_)),
        _ => None,
    }
}

/// The impls a generic impl `i` is applied to, which its methods may call.
fn impl_args(i: &ImplExpr) -> Vec<&ImplExpr> {
    match &*i.kind {
        ImplExprKind::ImplApp { impl_, args } => args.iter().chain(impl_args(impl_)).collect(),
        _ => vec![],
    }
}

/// The library function `g` that handles `Result`s, if it is one, applied to
/// `args`; `ty` is the type of the call.
fn lib_call(g: &GlobalId, args: &[Expr], ty: &Ty, types: &ResultTypes) -> Option<LibCall> {
    let result = |methods: &[&str]| methods.iter().any(|m| inherent_method(g, "result", m));
    let convert = [
        crate::names::core::convert::From::from,
        crate::names::core::convert::Into::into,
    ];
    Some(if convert.contains(g) {
        // Only the identity conversion of a `Result` is the library's; any
        // other one is an impl of the crate, which may read the `Err`.
        (is_result(ty) && args.first().is_some_and(|a| a.ty == *ty)).then_some(LibCall::KeepErr)?
    } else if inherent_method(g, "option", "map") {
        types.holds(ty, false).then_some(LibCall::MapOption)?
    // Only the methods hax's libraries model.
    } else if result(&["map"]) || inherent_method(g, "option", "transpose") {
        LibCall::KeepErr
    } else if result(&["map_err"]) {
        LibCall::MapErr
    } else if result(&["unwrap", "expect"]) {
        LibCall::PanicOnErr
    } else if result(&["is_ok", "is_err", "ok", "unwrap_or"]) {
        LibCall::ReadOk
    } else if result(&["err", "unwrap_err", "expect_err"]) {
        LibCall::ReadErr
    } else {
        return None;
    })
}

/// The crates whose functions hax's libraries model, with no event and no
/// table.
const LIBRARY_CRATES: &[&str] = &["alloc", "core", "hax_lib", "rust_primitives", "std"];

/// Whether the model extracts the function with these `meta` and `body`.
fn is_extracted(meta: &Metadata, body: &Expr) -> bool {
    let dropped = matches!(&*body.kind, ExprKind::GlobalId(g)
        if *g == crate::names::rust_primitives::hax::dropped_body);
    !is_late_skip(meta) && !body_is_hidden(meta) && quoted_body(body).is_none() && !dropped
}

/// The verbatim body of a function, as `replace_body` makes it.
fn quoted_body(body: &Expr) -> Option<&Quote> {
    match &*body.kind {
        ExprKind::Quote { contents } => Some(contents),
        ExprKind::Block { body, .. } => quoted_body(body),
        _ => None,
    }
}

/// Whether the function with these `meta` renders as a `fun`.
fn renders_as_fun(meta: &Metadata) -> bool {
    meta.hax_attributes()
        .any(|a| matches!(a, AttrPayload::Erased | AttrPayload::PVConstructor))
}

/// Whether the function with these `meta` is exempt from the checks.
fn unchecked(meta: &Metadata) -> bool {
    meta.hax_attributes()
        .any(|a| matches!(a, AttrPayload::PVUncheckedResults))
}

/// The `HAX WARNING` of a function exempt from the checks.
const UNCHECKED_WARNING: &str = "`pv_unchecked_results`: the uses of `Result` in this function \
     are not checked against the Result model";

/// Applies `f` to the name and body of every function the model extracts,
/// and marks those exempt from the checks.
fn for_each_checked_fn(items: &mut [Item], mut f: impl FnMut(GlobalId, &mut Expr)) {
    let mut one = |name: GlobalId, meta: &mut Metadata, body: &mut Expr| {
        if !is_extracted(meta, body) {
        } else if unchecked(meta) {
            meta.attributes
                .push(warning_attribute(UNCHECKED_WARNING, meta.span));
        } else {
            f(name, body)
        }
    };
    for item in items.iter_mut() {
        match &mut item.kind {
            ItemKind::Fn { name, body, .. } => one(*name, &mut item.meta, body),
            ItemKind::Impl { items, .. } => {
                for ii in items.iter_mut() {
                    if let ImplItemKind::Fn { body, .. } = &mut ii.kind {
                        one(ii.ident, &mut ii.meta, body)
                    }
                }
            }
            _ => {}
        }
    }
}

/// Which types may hold a `Result`.
#[derive(Default)]
struct ResultTypes {
    /// The crate's types with a field that may hold a `Result`.
    holding: HashSet<GlobalId>,
}

impl ResultTypes {
    fn new(items: &[Item]) -> Self {
        let mut types = Self::default();
        let local: HashSet<&str> = items.iter().map(|item| item.ident.krate()).collect();
        // A type holds what its fields hold, and what the associated types of
        // its impls do (`Iterator::Item`), which generic code may return.
        let type_fields: Vec<(GlobalId, Vec<Ty>)> = items
            .iter()
            .filter_map(|item| match &item.kind {
                ItemKind::Type { name, variants, .. } => Some((
                    *name,
                    variants
                        .iter()
                        .flat_map(|v| v.arguments.iter().map(|(_, ty, _)| ty.clone()))
                        .collect(),
                )),
                ItemKind::Impl { self_ty, items, .. } => match peel_refs(self_ty).kind() {
                    TyKind::App { head, .. } if local.contains(head.krate()) => Some((
                        *head,
                        items
                            .iter()
                            .filter_map(|ii| match &ii.kind {
                                ImplItemKind::Type { ty, .. } => Some(ty.clone()),
                                _ => None,
                            })
                            .collect(),
                    )),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        loop {
            let new: Vec<GlobalId> = type_fields
                .iter()
                .filter(|(name, tys)| {
                    !types.holding.contains(name) && tys.iter().any(|ty| types.holds(ty, true))
                })
                .map(|(name, _)| *name)
                .collect();
            if new.is_empty() {
                return types;
            }
            types.holding.extend(new);
        }
    }

    /// Whether a value of type `ty` may hold a `Result`; with `arrows`, also
    /// a closure that may return one.
    fn holds(&self, ty: &Ty, arrows: bool) -> bool {
        match ty.kind() {
            TyKind::App { head, args } => {
                *head == crate::names::core::result::Result
                    || self.holding.contains(head)
                    || args
                        .iter()
                        .any(|a| matches!(a, GenericValue::Ty(t) if self.holds(t, arrows)))
            }
            TyKind::Ref { inner, .. } | TyKind::Slice(inner) => self.holds(inner, arrows),
            TyKind::Array { ty, .. } => self.holds(ty, arrows),
            TyKind::Arrow { output, .. } => arrows && self.holds(output, arrows),
            _ => false,
        }
    }
}

/// `ty` without its references.
fn peel_refs(ty: &Ty) -> &Ty {
    match ty.kind() {
        TyKind::Ref { inner, .. } => peel_refs(inner),
        _ => ty,
    }
}

/// Whether `ty` is a `Result`, possibly behind references.
fn is_result(ty: &Ty) -> bool {
    match ty.kind() {
        TyKind::App { head, .. } => *head == crate::names::core::result::Result,
        TyKind::Ref { inner, .. } => is_result(inner),
        _ => false,
    }
}

/// A diagnostic of the rejection of `node`, in the phase `context`.
fn diagnostic(node: impl Into<Fragment>, span: Span, context: &str, details: String) -> Diagnostic {
    let info = DiagnosticInfo {
        context: Context::Phase(context.into()),
        span,
        kind: DiagnosticInfoKind::Unimplemented {
            issue_id: None,
            details: Some(details),
        },
    };
    Diagnostic::new(node, info)
}

/// Replaces `e` by an error node reporting `diagnostics`, and those of the
/// error nodes inside `e`, which it hides.
fn replace_by_error(e: &mut Expr, mut diagnostics: Vec<Diagnostic>) {
    struct Finder(Vec<Diagnostic>);
    impl AstVisitor for Finder {
        fn enter_expr_kind(&mut self, kind: &ExprKind) {
            if let ExprKind::Error(node) = kind {
                self.0.extend(node.diagnostics.iter().cloned());
            }
        }
    }
    let mut finder = Finder(vec![]);
    finder.visit_expr(e);
    diagnostics.extend(finder.0);
    *e.kind = ExprKind::Error(ErrorNode {
        fragment: Box::new(e.clone().into()),
        diagnostics,
    });
}

/// The locals that `pat` binds.
fn binders(pat: &Pat) -> Vec<LocalId> {
    struct Finder(Vec<LocalId>);
    impl AstVisitor for Finder {
        fn enter_pat_kind(&mut self, kind: &PatKind) {
            if let PatKind::Binding { var, .. } = kind {
                self.0.push(var.clone());
            }
        }
    }
    let mut finder = Finder(vec![]);
    finder.visit_pat(pat);
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

/// Whether `pat`, matched against a `Result`, may match an `Err`.
fn may_match_err(pat: &Pat) -> bool {
    match &*pat.kind {
        PatKind::Construct { constructor, .. } => *constructor == Err::Constructor,
        PatKind::Binding {
            sub_pat: Some(p), ..
        }
        | PatKind::Ascription { pat: p, .. }
        | PatKind::Deref { sub_pat: p } => may_match_err(p),
        PatKind::Or { sub_pats } => sub_pats.iter().any(may_match_err),
        _ => true,
    }
}

/// Whether `pat`, matched against a `Result`, matches every `Err`.
fn covers_err(pat: &Pat) -> bool {
    match &*pat.kind {
        PatKind::Construct {
            constructor,
            fields,
            ..
        } => *constructor == Err::Constructor && fields.iter().all(|(_, p)| is_irrefutable(p)),
        PatKind::Binding {
            sub_pat: Some(p), ..
        }
        | PatKind::Ascription { pat: p, .. }
        | PatKind::Deref { sub_pat: p } => covers_err(p),
        PatKind::Or { sub_pats } => sub_pats.iter().any(covers_err),
        _ => is_irrefutable(pat),
    }
}

/// Whether every path through `e` yields an `Err`, returns one, or diverges.
fn err_certain(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Construct { constructor, .. } => *constructor == Err::Constructor,
        // A diverging expression returns an `Err` or panics, unless it
        // leaves another way.
        ExprKind::App { head, args, .. } => {
            matches!(&*head.kind, ExprKind::GlobalId(g) if *g == never_to_any)
                && args.iter().all(diverges_with_err)
        }
        ExprKind::Return { value } => err_certain(value),
        ExprKind::Let { body, .. } => err_certain(body),
        ExprKind::If {
            then,
            else_: Some(else_),
            ..
        } => err_certain(then) && err_certain(else_),
        ExprKind::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|a| err_certain(&a.body))
        }
        ExprKind::Block { body: e, .. } | ExprKind::Ascription { e, .. } => err_certain(e),
        _ => false,
    }
}

/// Whether `e`, of type `!`, returns an `Err` or panics.
fn diverges_with_err(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Return { .. }
        | ExprKind::Let { .. }
        | ExprKind::If { .. }
        | ExprKind::Match { .. }
        | ExprKind::Block { .. }
        | ExprKind::Ascription { .. } => err_certain(e),
        ExprKind::App { head, .. } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == never_to_any) => {
            err_certain(e)
        }
        // A panic, whose arguments do not leave.
        ExprKind::App { .. } => !leaves(e),
        _ => false,
    }
}

/// Whether `e` holds a `return`, a `break`, a `continue` or an assignment,
/// outside a closure.
fn leaves(e: &Expr) -> bool {
    struct Finder(bool);
    impl AstVisitor for Finder {
        fn visit_expr(&mut self, e: &Expr) {
            match &*e.kind {
                ExprKind::Closure { .. } => {}
                ExprKind::Return { .. }
                | ExprKind::Break { .. }
                | ExprKind::Continue { .. }
                | ExprKind::Assign { .. } => self.0 = true,
                _ => self.visit_inner(e),
            }
        }
    }
    let mut finder = Finder(false);
    finder.visit_expr(e);
    finder.0
}

/// Whether `e` may leave other than by returning an `Err`: by a `return` of
/// something else, or a `break` or `continue` out of `e`.
fn escapes(e: &Expr) -> bool {
    struct Finder(Vec<Option<Symbol>>, bool);
    impl AstVisitor for Finder {
        fn visit_expr(&mut self, e: &Expr) {
            match &*e.kind {
                // A `return` there leaves the closure.
                ExprKind::Closure { .. } => {}
                ExprKind::Return { value } => {
                    self.1 |= !err_certain(value);
                    self.visit_expr(value)
                }
                ExprKind::Break { label, .. } | ExprKind::Continue { label, .. } => {
                    self.1 |= match label {
                        None => self.0.is_empty(),
                        Some(l) => !self.0.iter().any(|m| m.as_ref() == Some(l)),
                    };
                    self.visit_inner(e)
                }
                ExprKind::Loop { label, .. } => {
                    self.0.push(label.clone());
                    self.visit_inner(e);
                    self.0.pop();
                }
                _ => self.visit_inner(e),
            }
        }
    }
    let mut finder = Finder(vec![], false);
    finder.visit_expr(e);
    finder.1
}

/// Which calls cannot be observable: those of hax's libraries, and of the
/// crate's functions that only make such calls. A hand-written model may emit
/// events or insert in tables, so it may be observable; so may a kept trait
/// call, which calls the hand-written model of the trait item.
#[derive(Default)]
pub(crate) struct Quiet {
    /// The crate's functions.
    crate_fns: HashSet<GlobalId>,
    /// The crate's functions that cannot be observable.
    fns: HashSet<GlobalId>,
    /// The methods of each impl of the crate, by name.
    impls: HashMap<GlobalId, HashMap<String, GlobalId>>,
    /// The type each impl of the crate is for.
    self_types: HashMap<GlobalId, Ty>,
    /// The names of the library trait methods that some impl of the crate
    /// implements with a call that may be observable.
    noisy_methods: HashSet<String>,
    /// The `--keep-trait-calls` paths.
    kept: Vec<Namespace>,
}

impl Quiet {
    /// The quiet calls of `items`, with the `--keep-trait-calls` paths `kept`;
    /// a later phase finds the kept calls by their attribute instead.
    pub(crate) fn new(items: &[Item], kept: &[String]) -> Self {
        let mut quiet = Quiet {
            crate_fns: fn_decls(items).map(|d| d.name).collect(),
            fns: fn_decls(items)
                .filter(|d| is_extracted(d.meta, d.body) || renders_as_fun(d.meta))
                .map(|d| d.name)
                .collect(),
            impls: impl_methods(items),
            self_types: items
                .iter()
                .filter_map(|item| match &item.kind {
                    ItemKind::Impl { self_ty, .. } => Some((item.ident, self_ty.clone())),
                    _ => None,
                })
                .collect(),
            noisy_methods: HashSet::new(),
            kept: kept.iter().cloned().map(Namespace::from).collect(),
        };
        let library_impls: Vec<GlobalId> = items
            .iter()
            .flat_map(|item| match &item.kind {
                ItemKind::Impl { of_trait, .. }
                    if LIBRARY_CRATES.contains(&of_trait.trait_.krate()) =>
                {
                    quiet.impls[&item.ident].values().copied().collect()
                }
                _ => vec![],
            })
            .collect();
        // Only removals from `fns` and additions to `noisy_methods`, so this
        // terminates.
        loop {
            let noisy: Vec<GlobalId> = fn_decls(items)
                .filter(|d| {
                    quiet.fns.contains(&d.name)
                        && is_extracted(d.meta, d.body)
                        && !quiet.expr(d.body)
                })
                .map(|d| d.name)
                .collect();
            let methods: Vec<String> = library_impls
                .iter()
                .filter(|g| !quiet.fns.contains(g))
                .filter_map(method_name)
                .filter(|m| !quiet.noisy_methods.contains(m))
                .collect();
            if noisy.is_empty() && methods.is_empty() {
                return quiet;
            }
            for g in noisy {
                quiet.fns.remove(&g);
            }
            quiet.noisy_methods.extend(methods);
        }
    }

    /// Whether calling or reading `g` cannot be observable; `impl_` is the
    /// impl a trait method call dispatches to.
    fn global(&self, g: &GlobalId, impl_: Option<&ImplExpr>, bounds: &[ImplExpr]) -> bool {
        if *g == never_to_any || g.is_constructor() || g.is_projector() {
            return true;
        }
        if self.is_kept(g) {
            return false;
        }
        if self.crate_fns.contains(g) {
            return self.fns.contains(g);
        }
        // A library function may call any method of the impls it is given.
        let bounds = bounds.iter().all(|b| self.impl_(b));
        if let Some(m) = dispatch(&self.impls, g, impl_) {
            let args = impl_.is_none_or(|i| impl_args(i).into_iter().all(|a| self.impl_(a)));
            return self.fns.contains(&m) && bounds && args;
        }
        LIBRARY_CRATES.contains(&g.krate()) && impl_.is_none_or(|i| self.impl_(i)) && bounds
    }

    /// Whether `g` is a trait item that `--keep-trait-calls` keeps.
    fn is_kept(&self, g: &GlobalId) -> bool {
        self.kept.iter().any(|k| g.matches_namespace(k))
    }

    /// Whether no method of the impl `i` can be observable.
    fn impl_(&self, i: &ImplExpr) -> bool {
        match &*i.kind {
            // Library code may also call the impls of the supertraits, so
            // every impl for the same type must be quiet.
            ImplExprKind::Concrete(goal) => match self.self_types.get(&goal.trait_) {
                Some(ty) => self
                    .self_types
                    .iter()
                    .filter(|(_, t)| *t == ty)
                    .all(|(i, _)| self.impls[i].values().all(|m| self.fns.contains(m))),
                None => LIBRARY_CRATES.contains(&goal.trait_.krate()),
            },
            ImplExprKind::ImplApp { impl_, args } => {
                self.impl_(impl_) && args.iter().all(|a| self.impl_(a))
            }
            ImplExprKind::Parent { impl_, .. } | ImplExprKind::Projection { impl_, .. } => {
                self.impl_(impl_)
            }
            ImplExprKind::Builtin(_) => true,
            // The impl is not known here: it may be any of the crate's.
            _ => self.noisy_methods.is_empty(),
        }
    }

    /// Whether evaluating `e` cannot be observable.
    pub(crate) fn expr(&self, e: &Expr) -> bool {
        struct Finder<'a>(&'a Quiet, bool);
        impl AstVisitor for Finder<'_> {
            fn visit_expr(&mut self, e: &Expr) {
                match &*e.kind {
                    ExprKind::App {
                        head,
                        args,
                        trait_,
                        bounds_impls,
                        ..
                    } => {
                        self.1 &= !is_kept_call(&e.meta);
                        self.1 &= match &*head.kind {
                            ExprKind::GlobalId(g) => {
                                self.0
                                    .global(g, trait_.as_ref().map(|(i, _)| i), bounds_impls)
                            }
                            _ => false,
                        };
                        for arg in args {
                            self.visit_expr(arg);
                        }
                    }
                    ExprKind::GlobalId(g) => self.1 &= self.0.global(g, None, &[]),
                    // A function value may be applied to anything.
                    ExprKind::LocalId(_) => self.1 &= !matches!(e.ty.kind(), TyKind::Arrow { .. }),
                    ExprKind::Quote { .. } | ExprKind::Error(_) => self.1 = false,
                    _ => self.visit_inner(e),
                }
            }
        }
        let mut finder = Finder(self, true);
        finder.visit_expr(e);
        finder.1
    }
}

/// Where a value goes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Pos {
    /// Into a binding, a field, an argument or a condition.
    Value,
    /// To a consumer that propagates its `Err`: `?`, a `match`, `unwrap`.
    Consumed,
    /// Out of the function.
    Tail,
}

/// The two checks (see the module documentation).
struct Check {
    /// Whether the model is `--result-errors`.
    errors: bool,
    types: ResultTypes,
    quiet: Quiet,
    /// The functions the model extracts.
    extracted: HashSet<GlobalId>,
    /// The methods of each impl of the crate.
    impls: HashMap<GlobalId, HashMap<String, GlobalId>>,
    /// The crates the items come from.
    local_crates: HashSet<&'static str>,
    /// The impls of [`hidden_result_impls`].
    hidden_impls: HashSet<GlobalId>,
    /// Under `--result-errors`, the extracted functions whose `Err` may be
    /// that of a hand-written model.
    opaque_fns: HashSet<GlobalId>,
    /// The function being checked.
    current: Option<GlobalId>,
    /// Under `--result-errors`, the locals bound to the error of a
    /// hand-written model.
    err_binders: HashSet<LocalId>,
    /// The label and the position of each enclosing loop.
    loops: Vec<(Option<Symbol>, Pos)>,
    /// Whether to reject, or only to compute `opaque_fns`.
    reject: bool,
    /// Whether `opaque_fns` grew.
    changed: bool,
    context: &'static str,
    hint: &'static str,
}

/// What the default Result model cannot express, for the error messages.
const RECOVERY_HINT: &str = "the default Result model ends the trace on every `Err`: \
     return or consume a `Result` at once (`?`, `match`, `unwrap`), and return or panic on an \
     `Err`; or pass `--result-errors`, or mark the function `#[hax_lib::pv_unchecked_results]`";

/// Why an unknown error must not be inspected, for the error messages.
const UNKNOWN_HINT: &str = "the `Err` of a function whose body is not extracted is a term \
     of its model, not the Rust error value: return or consume such a `Result` at once, and only \
     propagate its error or match it with `Err(_)`; or mark the function \
     `#[hax_lib::pv_unchecked_results]`";

impl Check {
    fn reject(&self, e: &mut Expr, what: &str) {
        if self.reject {
            let d = diagnostic(
                e.clone(),
                e.meta.span,
                self.context,
                format!("{what}: {}", self.hint),
            );
            replace_by_error(e, vec![d]);
        }
    }

    /// Rejects `e`, which holds the patterns `pats` that are rejected.
    fn reject_pats(&self, e: &mut Expr, pats: Vec<(Pat, &str)>) {
        if self.reject && !pats.is_empty() {
            let diagnostics = pats
                .into_iter()
                .map(|(p, what)| {
                    let span = p.meta.span;
                    diagnostic(p, span, self.context, format!("{what}: {}", self.hint))
                })
                .collect();
            replace_by_error(e, diagnostics);
        }
    }

    /// Under `--result-errors`, whether the `Err` of `e` may be that of a
    /// hand-written model.
    fn opaque(&self, e: &Expr) -> bool {
        let call = |g: &GlobalId| {
            if self.extracted.contains(g) {
                self.opaque_fns.contains(g)
            } else {
                *g != never_to_any && !g.is_constructor() && !g.is_projector()
            }
        };
        let holds = self.types.holds(&e.ty, false);
        match &*e.kind {
            ExprKind::Block { body: e, .. }
            | ExprKind::Ascription { e, .. }
            | ExprKind::Borrow { inner: e, .. }
            | ExprKind::AddressOf { inner: e, .. }
            | ExprKind::Let { body: e, .. } => self.opaque(e),
            ExprKind::If { then, else_, .. } => {
                self.opaque(then) || else_.as_ref().is_some_and(|e| self.opaque(e))
            }
            // An arm may also put back the unknown error it binds.
            ExprKind::Match { scrutinee, arms } => {
                arms.iter().any(|a| self.opaque(&a.body))
                    || holds && is_result(&scrutinee.ty) && self.opaque(scrutinee)
            }
            ExprKind::App {
                head, args, trait_, ..
            } => match &*head.kind {
                ExprKind::GlobalId(g) => match lib_call(g, args, &e.ty, &self.types) {
                    Some(LibCall::KeepErr | LibCall::PanicOnErr) => self.opaque(&args[0]),
                    // Mapping the error keeps the `Ok` payload, which may hold
                    // another unknown error.
                    Some(LibCall::MapErr) => {
                        self.opaque(&args[0])
                            && (!args.get(1).is_some_and(ignores_param)
                                || self.ok_payload_holds(&e.ty))
                    }
                    Some(LibCall::MapOption) => match args.get(1).map(|f| &*f.kind) {
                        // A `?` in the closure returns its error from the
                        // closure.
                        Some(ExprKind::Closure { body, .. }) => self.opaque(body) || leaves(body),
                        Some(ExprKind::GlobalId(f)) => call(f),
                        _ => holds,
                    },
                    // The `Ok` payload may hold another unknown error.
                    Some(LibCall::ReadOk) => holds && self.opaque(&args[0]),
                    Some(LibCall::ReadErr) => false,
                    // A kept trait call calls the hand-written model of the
                    // trait item.
                    None if self.quiet.is_kept(g) => holds,
                    None => {
                        let impl_ = trait_.as_ref().map(|(i, _)| i);
                        holds && call(&dispatch(&self.impls, g, impl_).unwrap_or(*g))
                    }
                },
                _ => holds,
            },
            ExprKind::GlobalId(g) => holds && call(g),
            ExprKind::Construct {
                constructor,
                fields,
                ..
            } => *constructor == Err::Constructor && fields.iter().any(|(_, f)| self.err_of(f)),
            ExprKind::LocalId(_) | ExprKind::Literal(_) | ExprKind::Closure { .. } => false,
            _ => holds,
        }
    }

    /// Whether the impl `i` is, or uses, one of `hidden_impls`.
    fn uses_hidden(&self, i: &ImplExpr) -> bool {
        match &*i.kind {
            ImplExprKind::Concrete(goal) => self.hidden_impls.contains(&goal.trait_),
            ImplExprKind::ImplApp { impl_, args } => {
                self.uses_hidden(impl_) || args.iter().any(|a| self.uses_hidden(a))
            }
            ImplExprKind::Parent { impl_, .. } | ImplExprKind::Projection { impl_, .. } => {
                self.uses_hidden(impl_)
            }
            _ => false,
        }
    }

    /// Whether the `Ok` payload of the `Result` type `ty` may hold a `Result`.
    fn ok_payload_holds(&self, ty: &Ty) -> bool {
        matches!(ty.kind(), TyKind::App { args, .. }
            if matches!(args.first(), Some(GenericValue::Ty(t)) if self.types.holds(t, true)))
    }

    /// Whether `e` is a local bound to an unknown error, possibly converted
    /// to its own type.
    fn err_of(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::LocalId(x) => self.err_binders.contains(x),
            ExprKind::App { head, args, .. } => {
                matches!(&*head.kind, ExprKind::GlobalId(g)
                    if [
                        crate::names::core::convert::From::from,
                        crate::names::core::convert::Into::into,
                    ]
                    .contains(g))
                    && args.len() == 1
                    && args[0].ty == e.ty
                    && self.err_of(&args[0])
            }
            _ => false,
        }
    }

    /// Checks a leaf `e` in position `pos`; whether it was rejected.
    fn leaf(&mut self, e: &mut Expr, pos: Pos) -> bool {
        if !self.types.holds(&e.ty, true) {
            return false;
        }
        let bad = if self.errors {
            let opaque = self.opaque(e);
            if opaque && pos == Pos::Tail {
                let current = self.current.unwrap();
                self.changed |= self.opaque_fns.insert(current);
            }
            opaque && pos == Pos::Value
        } else {
            pos == Pos::Value
        };
        if bad {
            self.reject(e, "a `Result` used here is not propagated");
        }
        bad
    }

    /// Checks the children of `e`, as values.
    fn children(&mut self, e: &mut Expr) {
        struct Children<'a>(&'a mut Check);
        impl AstVisitorMut for Children<'_> {
            fn visit_expr(&mut self, e: &mut Expr) {
                self.0.expr(e, Pos::Value)
            }
        }
        Children(self).visit_inner(e)
    }

    /// Checks `e`, whose value goes to `pos`.
    fn expr(&mut self, e: &mut Expr, pos: Pos) {
        match &mut *e.kind {
            ExprKind::Block { body: inner, .. }
            | ExprKind::Ascription { e: inner, .. }
            | ExprKind::Borrow { inner, .. }
            | ExprKind::AddressOf { inner, .. } => self.expr(inner, pos),
            ExprKind::Let { rhs, body, .. } => {
                self.expr(rhs, Pos::Value);
                self.expr(body, pos);
            }
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.expr(condition, Pos::Value);
                self.expr(then, pos);
                if let Some(else_) = else_ {
                    self.expr(else_, pos);
                }
            }
            ExprKind::Match { .. } => self.match_(e, pos),
            ExprKind::Return { value } => self.expr(value, Pos::Tail),
            ExprKind::Loop { body, label, .. } => {
                self.loops.push((label.clone(), pos));
                self.expr(body, Pos::Value);
                self.loops.pop();
                // The condition, the iterator and the state.
                let ExprKind::Loop { kind, state, .. } = &mut *e.kind else {
                    unreachable!()
                };
                match &mut **kind {
                    LoopKind::WhileLoop { condition } => self.expr(condition, Pos::Value),
                    LoopKind::ForLoop { iterator, .. } => self.expr(iterator, Pos::Value),
                    LoopKind::ForIndexLoop { start, end, .. } => {
                        self.expr(start, Pos::Value);
                        self.expr(end, Pos::Value);
                    }
                    _ => {}
                }
                if let Some(state) = state {
                    self.expr(&mut state.init, Pos::Value);
                }
            }
            ExprKind::Break {
                value,
                state,
                label,
                ..
            } => {
                let pos = self
                    .loops
                    .iter()
                    .rev()
                    .find(|(l, _)| label.is_none() || l == label)
                    .map_or(Pos::Value, |(_, pos)| *pos);
                self.expr(value, pos);
                if let Some(state) = state {
                    self.expr(state, Pos::Value);
                }
            }
            ExprKind::App { .. } => self.app(e, pos),
            ExprKind::Construct { .. } => {
                if self.leaf(e, pos) {
                    return;
                }
                let errors = self.errors;
                let ExprKind::Construct {
                    constructor,
                    fields,
                    base,
                    ..
                } = &mut *e.kind
                else {
                    unreachable!()
                };
                let is_err = *constructor == Err::Constructor;
                for (_, field) in fields {
                    // An unknown error may be put back in an `Err`.
                    if !(errors && is_err && self.err_of(field)) {
                        self.expr(field, Pos::Value);
                    }
                }
                if let Some(base) = base {
                    self.expr(base, Pos::Value);
                }
            }
            ExprKind::LocalId(x) => {
                if self.err_binders.contains(x) {
                    self.reject(e, "this reads the error of a hand-written model");
                } else {
                    self.leaf(e, pos);
                }
            }
            ExprKind::GlobalId(_) | ExprKind::Quote { .. } | ExprKind::Closure { .. } => {
                if !self.leaf(e, pos) {
                    self.children(e)
                }
            }
            ExprKind::Error(_) => {}
            _ => self.children(e),
        }
    }

    /// Checks the application `e`, whose value goes to `pos`.
    fn app(&mut self, e: &mut Expr, pos: Pos) {
        if self.leaf(e, pos) {
            return;
        }
        let ExprKind::App {
            head,
            args,
            bounds_impls,
            generic_args,
            trait_,
        } = &mut *e.kind
        else {
            unreachable!()
        };
        let lib = match &*head.kind {
            ExprKind::GlobalId(g) => lib_call(g, args, &e.ty, &self.types),
            _ => {
                self.expr(head, Pos::Value);
                None
            }
        };
        // Another library function has no model of what it does with a
        // `Result`.
        let unmodelled = lib.is_none()
            && matches!(&*head.kind, ExprKind::GlobalId(g)
                if !self.local_crates.contains(g.krate())
                    && !g.is_constructor()
                    && *g != never_to_any)
            && args.iter().any(|a| self.types.holds(&a.ty, true));
        if unmodelled {
            return self.reject(
                e,
                "this library function, which takes a `Result`, has no model",
            );
        }
        // A generic function hides the `Result`s of its instantiation from
        // these checks, and its trait calls do not resolve to the impls.
        let generic_result = lib.is_none()
            && generic_args
                .iter()
                .any(|g| matches!(g, GenericValue::Ty(t) if self.types.holds(t, true)));
        if generic_result {
            return self.reject(
                e,
                "this generic function is instantiated with a type that holds a `Result`",
            );
        }
        let hidden =
            (bounds_impls.iter().chain(trait_.iter().map(|(i, _)| i))).any(|i| self.uses_hidden(i));
        if hidden {
            return self.reject(
                e,
                "this call uses an impl for a type that is not a type of the crate, whose \
                 associated types hold a `Result`, which the checks cannot follow",
            );
        }
        // How the first argument is used.
        let first = match lib {
            Some(LibCall::KeepErr | LibCall::MapErr | LibCall::PanicOnErr) => Pos::Consumed,
            Some(LibCall::ReadOk) if self.errors => Pos::Consumed,
            _ => Pos::Value,
        };
        // The model applies the mapping after the trait calls are resolved and
        // the functions are inlined: a function value, such as a trait method
        // like `E::from` or an inlined function, would miss the impl or the
        // body Rust runs. Only closures and constructors map an error.
        fn peel(e: &Expr) -> &Expr {
            match &*e.kind {
                ExprKind::Borrow { inner: e, .. }
                | ExprKind::Block { body: e, .. }
                | ExprKind::Ascription { e, .. } => peel(e),
                _ => e,
            }
        }
        let by_path = lib == Some(LibCall::MapErr)
            && args.get(1).is_some_and(|f| {
                !matches!(&*peel(f).kind, ExprKind::Closure { .. })
                    && !matches!(&*peel(f).kind, ExprKind::GlobalId(g) if g.is_constructor())
            });
        if by_path {
            return self.reject(
                e,
                "this maps an `Err` by a function value, which the model may call without the \
                 impl or the inlined body Rust runs; use a closure or a constructor",
            );
        }
        // The mapping runs while an `Err` is pending, on its error.
        let mapping_ok = lib != Some(LibCall::MapErr)
            || args.len() != 2
            || if self.errors {
                !self.opaque(&args[0]) || ignores_param(&args[1]) || is_constructor(&args[1])
            } else {
                self.quiet.expr(&args[1])
            };
        if !mapping_ok {
            let what = if self.errors {
                "this maps the error of a hand-written model by reading it"
            } else {
                "this maps an `Err` by a call that may be observable"
            };
            return self.reject(e, what);
        }
        // Under the default model, the other arguments of a consumer run after
        // its `Result`, which may be an `Err`; a function value runs later, if
        // at all.
        let pending_ok = self.errors
            || first != Pos::Consumed
            || args.iter().skip(1).all(|a| {
                matches!(
                    *a.kind,
                    ExprKind::Closure { .. } | ExprKind::LocalId(_) | ExprKind::GlobalId(_)
                ) || self.quiet.expr(a) && !escapes(a)
            });
        if !pending_ok {
            return self.reject(
                e,
                "an argument of this call may be observable, and runs after a `Result` that may \
                 be an `Err`",
            );
        }
        for (i, arg) in args.iter_mut().enumerate() {
            match &mut *arg.kind {
                // The function is applied at once, and its `Result` goes
                // where the `Option` does.
                ExprKind::Closure { body, .. } if i == 1 && lib == Some(LibCall::MapOption) => {
                    self.expr(body, pos)
                }
                ExprKind::GlobalId(_) if i == 1 && lib == Some(LibCall::MapOption) => {}
                _ => self.expr(arg, if i == 0 { first } else { Pos::Value }),
            }
        }
    }

    /// Checks the match `e`, whose value goes to `pos`.
    fn match_(&mut self, e: &mut Expr, pos: Pos) {
        let ExprKind::Match { scrutinee, arms } = &mut *e.kind else {
            unreachable!()
        };
        if !is_result(&scrutinee.ty) {
            self.expr(scrutinee, Pos::Value);
            for arm in arms.iter_mut() {
                let before = self.err_binders.clone();
                if let Some(guard) = &mut arm.guard {
                    let GuardKind::IfLet { rhs, lhs } = &mut guard.kind;
                    self.guard(lhs, rhs);
                }
                self.expr(&mut arm.body, pos);
                self.err_binders = before;
            }
            return;
        }
        // Under the default model, a `Result` inside an `Ok` would be bound
        // as a value, which may be an `Err`.
        if !self.errors && self.ok_payload_holds(&scrutinee.ty) {
            return self.reject(e, "this matches a `Result` whose `Ok` holds a `Result`");
        }
        let opaque = self.errors && self.opaque(scrutinee);
        self.expr(scrutinee, Pos::Consumed);
        let mut rejected: Vec<(Pat, &str)> = vec![];
        let mut err_taken = false;
        for arm in arms.iter_mut() {
            let bound = if self.errors {
                if opaque {
                    self.opaque_pat(&arm.pat, &mut rejected)
                } else {
                    vec![]
                }
            } else {
                if !err_taken && may_match_err(&arm.pat) {
                    if arm.guard.is_some() {
                        rejected
                            .push((arm.pat.clone(), "this arm, with a guard, may see an `Err`"));
                    } else if !err_certain(&arm.body) || escapes(&arm.body) {
                        rejected.push((
                            arm.pat.clone(),
                            "this arm may see an `Err`, and goes on without returning one",
                        ));
                    } else if !self.quiet.expr(&arm.body) {
                        rejected.push((
                            arm.pat.clone(),
                            "this arm may see an `Err`, and may do something observable before \
                             returning it",
                        ));
                    }
                }
                err_taken |= arm.guard.is_none() && covers_err(&arm.pat);
                vec![]
            };
            let before = self.err_binders.clone();
            self.err_binders.extend(bound);
            if let Some(guard) = &mut arm.guard {
                let GuardKind::IfLet { rhs, lhs } = &mut guard.kind;
                self.guard(lhs, rhs);
            }
            self.expr(&mut arm.body, pos);
            self.err_binders = before;
        }
        self.reject_pats(e, rejected);
    }

    /// Checks the `if let` guard `lhs = rhs`.
    fn guard(&mut self, lhs: &Pat, rhs: &mut Expr) {
        if self.errors && is_result(&rhs.ty) && self.opaque(rhs) {
            let mut rejected = vec![];
            let bound = self.opaque_pat(lhs, &mut rejected);
            self.expr(rhs, Pos::Consumed);
            self.err_binders.extend(bound);
            self.reject_pats(rhs, rejected);
        } else {
            self.expr(rhs, Pos::Value);
        }
    }

    /// Checks `pat`, matched against a `Result` whose `Err` is unknown: it may
    /// bind the error but not inspect it. Returns the locals bound to it.
    fn opaque_pat(&self, pat: &Pat, rejected: &mut Vec<(Pat, &str)>) -> Vec<LocalId> {
        match &*pat.kind {
            PatKind::Construct {
                constructor,
                fields,
                ..
            } if *constructor == Err::Constructor => match fields.as_slice() {
                [(_, p)] if matches!(*p.kind, PatKind::Wild) => vec![],
                [(_, p)] if matches!(&*p.kind, PatKind::Binding { sub_pat: None, .. }) => {
                    binders(p)
                }
                _ => {
                    rejected.push((
                        pat.clone(),
                        "this pattern inspects the error of a hand-written model",
                    ));
                    vec![]
                }
            },
            PatKind::Construct { fields, .. } => {
                // The `Ok` payload may hold a `Result` in turn.
                if fields.iter().any(|(_, p)| self.types.holds(&p.ty, false)) {
                    rejected.push((
                        pat.clone(),
                        "this pattern reads a `Result` of a hand-written model",
                    ));
                }
                vec![]
            }
            PatKind::Wild => vec![],
            PatKind::Ascription { pat: p, .. } | PatKind::Deref { sub_pat: p } => {
                self.opaque_pat(p, rejected)
            }
            PatKind::Or { sub_pats } => sub_pats
                .iter()
                .flat_map(|p| self.opaque_pat(p, rejected))
                .collect(),
            _ => {
                rejected.push((
                    pat.clone(),
                    "this pattern binds a `Result` of a hand-written model",
                ));
                vec![]
            }
        }
    }

    /// Checks the function `name`, of body `body`.
    fn function(&mut self, name: GlobalId, body: &mut Expr) {
        self.current = Some(name);
        self.err_binders.clear();
        self.expr(body, Pos::Tail);
    }
}

/// Whether the closure `e` ignores its parameters.
fn ignores_param(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Closure { params, body, .. } => {
            params.iter().flat_map(binders).all(|x| !mentions(&x, body))
        }
        _ => false,
    }
}

/// Whether `e` is a constructor, which wraps the error without reading it.
fn is_constructor(e: &Expr) -> bool {
    matches!(&*e.kind, ExprKind::GlobalId(g) if g.is_constructor())
}

impl Check {
    fn new(items: &[Item], errors: bool, kept: &[String]) -> Self {
        let types = ResultTypes::new(items);
        Check {
            errors,
            hidden_impls: hidden_result_impls(items, &types),
            types,
            quiet: Quiet::new(items, kept),
            extracted: fn_decls(items)
                .filter(|d| is_extracted(d.meta, d.body))
                .map(|d| d.name)
                .collect(),
            impls: impl_methods(items),
            local_crates: items.iter().map(|item| item.ident.krate()).collect(),
            opaque_fns: HashSet::new(),
            current: None,
            err_binders: HashSet::new(),
            loops: vec![],
            reject: true,
            changed: false,
            context: if errors {
                stringify!(ProverifRejectUnknownErrors)
            } else {
                stringify!(ProverifRejectRecovery)
            },
            hint: if errors { UNKNOWN_HINT } else { RECOVERY_HINT },
        }
    }
}

/// Phase rejecting, under the default Result model, the code that may go on
/// after an `Err` (see the module documentation).
pub struct ProverifRejectRecovery<'a> {
    /// The `--keep-trait-calls` paths.
    pub kept: &'a [String],
}

/// The impls of the crate for a type that is not a type of the crate, and
/// whose associated types hold a `Result`, which the checks cannot follow.
fn hidden_result_impls(items: &[Item], types: &ResultTypes) -> HashSet<GlobalId> {
    let local: HashSet<&str> = items.iter().map(|item| item.ident.krate()).collect();
    items
        .iter()
        .filter(|item| match &item.kind {
            ItemKind::Impl { items, self_ty, .. } => !matches!(peel_refs(self_ty).kind(),
                    TyKind::App { head, .. } if local.contains(head.krate()))
                && items.iter().any(
                    |ii| matches!(&ii.kind, ImplItemKind::Type { ty, .. } if types.holds(ty, true)),
                ),
            _ => false,
        })
        .map(|item| item.ident)
        .collect()
}

/// What an impl of [`hidden_result_impls`] is rejected for.
const HIDDEN_RESULT: &str = "this impl is for a type that is not a type of the crate, and its \
     associated types hold a `Result`, which the checks cannot follow";

/// Rejects the methods of the impls `hidden`; their uses are rejected by the
/// checks.
fn reject_hidden_results(items: &mut [Item], hidden: &HashSet<GlobalId>, context: &str) {
    for item in items.iter_mut() {
        let ItemKind::Impl { items, .. } = &mut item.kind else {
            continue;
        };
        if !hidden.contains(&item.ident) {
            continue;
        }
        for ii in items.iter_mut() {
            if let ImplItemKind::Fn { body, .. } = &mut ii.kind {
                let d = diagnostic(body.clone(), body.meta.span, context, HIDDEN_RESULT.into());
                replace_by_error(body, vec![d]);
            }
        }
    }
}

impl Phase for ProverifRejectRecovery<'_> {
    fn apply(&self, items: &mut Vec<Item>) {
        let mut check = Check::new(items, false, self.kept);
        reject_hidden_results(items, &check.hidden_impls, check.context);
        for_each_checked_fn(items, |name, body| check.function(name, body));
    }
}

/// Phase rejecting, under `--result-errors`, the code that would read the
/// error of a hand-written model as a Rust error value (see the module
/// documentation), and the models whose `Result` is neither `Ok` nor `Err`.
pub struct ProverifRejectUnknownErrors<'a> {
    /// The `--keep-trait-calls` paths.
    pub kept: &'a [String],
}

/// Wraps each verbatim term of type `Result` (as `replace_body`,
/// `pv_extern` and `pv_inverse_of` make them), so that its value is one: an
/// `Ok` or an `Err` is kept, any other value becomes an `Ok`, and a failure an
/// `Err`, with an unknown error. A verbatim term of another type holding a
/// `Result` cannot be normalised, and is rejected.
#[setup_error_handling_struct]
#[derive(Default)]
struct WrapQuotes {
    types: ResultTypes,
}

impl VisitorWithContext for WrapQuotes {
    fn context(&self) -> Context {
        Context::Phase(stringify!(ProverifRejectUnknownErrors).to_string())
    }
}

impl AstVisitorMut for WrapQuotes {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        self.visit_inner(expr);
        let is_result = matches!(expr.ty.kind(), TyKind::App { head, .. }
            if *head == crate::names::core::result::Result);
        let holds = self.types.holds(&expr.ty, false);
        if let ExprKind::Quote { contents } = &mut *expr.kind {
            if is_result {
                contents
                    .0
                    .insert(0, QuoteContent::Verbatim("let hax__model = (".into()));
                contents.0.push(QuoteContent::Verbatim(
                    ") in (let core__result__Result__Ok(hax__v) = hax__model in hax__model \
                     else let core__result__Result__Err(hax__v) = hax__model in hax__model \
                     else hax_result_ok(hax__model)) \
                     else hax_result_err(rust_primitives__hax__Tuple0__Tuple0)"
                        .into(),
                ));
            } else if holds || matches!(expr.ty.kind(), TyKind::Param(_)) {
                self.error(
                    expr.clone(),
                    DiagnosticInfoKind::Unimplemented {
                        issue_id: None,
                        details: Some(
                            "under `--result-errors`, a verbatim model of a value holding a \
                             `Result` cannot be checked to build each `Result` as `Ok` or `Err`; \
                             model each `Result` by a function of its own"
                                .into(),
                        ),
                    },
                )
            }
        }
    }
}

/// The libraries an extraction with `--result-errors` is checked against.
const RESULT_ERRORS_LIBRARIES: &[&str] = &[
    crate::backends::proverif::PRIMITIVES_PVL,
    crate::backends::proverif::RESULT_ERRORS_PVL,
    include_str!("../backends/proverif/libs/cryptolib.pvl"),
];

/// Rejects the uses of the crate's functions returning a `Result` that render
/// as a `fun`: neither `Ok(..)` nor `Err(..)` matches their value, so both
/// paths would be lost. A library function without a model is declared as a
/// `fun` in `missingdecl.pvl`, for the user to replace, so its uses are
/// warned of.
#[setup_error_handling_struct]
#[derive(Default)]
struct FunResults {
    types: ResultTypes,
    /// The crate's functions.
    crate_fns: HashSet<GlobalId>,
    /// The crate's functions that render as a `fun`.
    funs: HashSet<GlobalId>,
    /// The names the libraries and the crate's verbatim ProVerif declare.
    declared: HashSet<String>,
    /// The methods of each impl of the crate.
    impls: HashMap<GlobalId, HashMap<String, GlobalId>>,
    /// The `--keep-trait-calls` paths.
    kept: Vec<Namespace>,
    /// The warnings of the function being visited, which go to its item: the
    /// later phases do not keep the attributes of expressions.
    pending: Vec<String>,
}

impl FunResults {
    fn warn(&mut self, message: String) {
        if !self.pending.contains(&message) {
            self.pending.push(message);
        }
    }

    /// Visits every function, and marks it with its warnings.
    fn visit_fns(&mut self, items: &mut [Item]) {
        let flush = |funs: &mut Self, meta: &mut Metadata| {
            for w in std::mem::take(&mut funs.pending) {
                meta.attributes.push(warning_attribute(&w, meta.span));
            }
        };
        for item in items.iter_mut() {
            match &mut item.kind {
                ItemKind::Impl { items, .. } => {
                    for ii in items.iter_mut() {
                        self.visit(ii);
                        flush(self, &mut ii.meta);
                    }
                }
                _ => {
                    self.visit(item);
                    flush(self, &mut item.meta);
                }
            }
        }
    }
}

impl VisitorWithContext for FunResults {
    fn context(&self) -> Context {
        Context::Phase(stringify!(ProverifRejectUnknownErrors).to_string())
    }
}

impl AstVisitorMut for FunResults {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        self.visit_inner(expr);
        // A trait method call names the impl's method, when it is known.
        let name = match &*expr.kind {
            ExprKind::App { head, trait_, .. } => match &*head.kind {
                ExprKind::GlobalId(g) if self.kept.iter().any(|k| g.matches_namespace(k)) => {
                    Some(*g)
                }
                ExprKind::GlobalId(g) => {
                    let impl_ = trait_.as_ref().map(|(i, _)| i);
                    Some(dispatch(&self.impls, g, impl_).unwrap_or(*g))
                }
                _ => None,
            },
            // A constant may be referred to unapplied.
            ExprKind::GlobalId(g) if *g != crate::names::rust_primitives::hax::dropped_body => {
                Some(*g)
            }
            _ => None,
        };
        let Some(g) = name.filter(|g| {
            !(*g == never_to_any || g.is_constructor() || g.is_projector())
                && self.types.holds(&expr.ty, false)
        }) else {
            return;
        };
        let args = match &*expr.kind {
            ExprKind::App { args, .. } => args.clone(),
            _ => vec![],
        };
        let rendered = render_id(&g);
        if self.kept.iter().any(|k| g.matches_namespace(k)) {
            self.warn(format!(
                "`{rendered}` is a kept trait call returning a `Result`: unless its hand-written \
                 model returns `hax_result_ok(..)` or `hax_result_err(..)`, every path through \
                 its uses is lost"
            ));
        } else if self.funs.contains(&g) {
            self.error(
                expr.clone(),
                DiagnosticInfoKind::Unimplemented {
                    issue_id: None,
                    details: Some(format!(
                        "`{rendered}` returns a `Result`, but it is opaque or a \
                         `pv_constructor`, so its value is neither `Ok(..)` nor `Err(..)` under \
                         `--result-errors`; give it a `replace_body` model"
                    )),
                },
            )
        } else if !self.crate_fns.contains(&g)
            && !matches!(
                &*expr.kind,
                ExprKind::App {
                    trait_: Some(_),
                    ..
                }
            )
            && lib_call(&g, &args, &expr.ty, &self.types).is_none()
            && !self.declared.contains(&rendered)
        {
            self.warn(format!(
                "`{rendered}` returns a `Result` but has no model: unless its declaration in \
                 missingdecl.pvl is replaced by one returning `hax_result_ok(..)` or \
                 `hax_result_err(..)`, every path through its uses is lost"
            ));
        }
    }
}

impl Phase for ProverifRejectUnknownErrors<'_> {
    fn apply(&self, items: &mut Vec<Item>) {
        let declared: HashSet<String> = items
            .iter()
            .filter_map(|item| match &item.kind {
                ItemKind::Quote { quote, .. } => Some(quote_text(quote)),
                _ => None,
            })
            .chain(RESULT_ERRORS_LIBRARIES.iter().map(|lib| lib.to_string()))
            .flat_map(|text| scan_declared_names(&text))
            .collect();
        let crate_fns: HashSet<GlobalId> = fn_decls(items).map(|d| d.name).collect();
        let funs = fn_decls(items)
            .filter(|d| renders_as_fun(d.meta))
            .map(|d| d.name)
            .collect();
        let mut check = Check::new(items, true, self.kept);
        reject_hidden_results(items, &check.hidden_impls, check.context);
        let mut wrap = WrapQuotes {
            types: std::mem::take(&mut check.types),
            ..Default::default()
        };
        wrap.visit(items);
        let mut funs = FunResults {
            types: wrap.types,
            crate_fns,
            funs,
            declared,
            impls: impl_methods(items),
            kept: self.kept.iter().cloned().map(Namespace::from).collect(),
            ..Default::default()
        };
        funs.visit_fns(items);
        check.types = funs.types;
        // An unchecked function may return an unknown error.
        check.opaque_fns = fn_decls(items)
            .filter(|d| unchecked(d.meta))
            .map(|d| d.name)
            .collect();
        // `opaque_fns` only grows, so this terminates. Without rejecting, the
        // check leaves the items unchanged.
        check.reject = false;
        check.changed = true;
        let mut bodies: Vec<(GlobalId, Expr)> = fn_decls(items)
            .filter(|d| is_extracted(d.meta, d.body) && !unchecked(d.meta))
            .map(|d| (d.name, d.body.clone()))
            .collect();
        while check.changed {
            check.changed = false;
            for (name, body) in &mut bodies {
                check.function(*name, body);
            }
        }
        check.reject = true;
        for_each_checked_fn(items, |name, body| check.function(name, body));
    }
}
