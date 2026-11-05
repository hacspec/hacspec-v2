//! ProVerif-backend phase: reject the `for` loops that the model gets wrong.
//!
//! ProVerif has no loops: the printer unrolls a `for` loop over a list
//! `LOOP_BOUND` times and skips the later iterations, and it runs no iteration
//! over an iterator that is not a list, such as a range with a variable bound
//! or an adapter like `enumerate`. The events and table inserts of a body
//! would then be lost, and the variables the loop updates would be terms that
//! match no pattern and equal no value, which loses the traces that test them.

use crate::ast::visitors::*;
use crate::ast::*;
use crate::backends::is_late_skip;
use crate::phase::Phase;
use crate::phase::proverif_result_soundness::{Quiet, diagnostic, replace_by_error};

/// Phase rejecting the `for` loops that update variables or whose body may be
/// observable.
#[derive(Default, Debug)]
pub struct ProverifRejectLoops;

struct RejectLoops {
    quiet: Quiet,
}

impl AstVisitorMut for RejectLoops {
    fn visit_expr(&mut self, e: &mut Expr) {
        self.visit_inner(e);
        let ExprKind::Loop {
            body, kind, state, ..
        } = &*e.kind
        else {
            return;
        };
        if !matches!(**kind, LoopKind::ForLoop { .. }) {
            return;
        }
        // A body holding an error node is rejected, but the model may still
        // print the loop, as when it drops the arm holding it.
        let what = if state.is_some() {
            "this loop updates variables, but the model runs a bounded number of iterations, \
             and none over an iterator that is not a list, after which their values match no \
             pattern; compute them without a loop, or model the function by hand"
        } else if !self.quiet.expr(body) {
            "the body of this loop may be observable, but the model runs a bounded number of \
             iterations, and none over an iterator that is not a list; move the observable \
             calls out of the loop"
        } else {
            return;
        };
        let d = diagnostic(
            e.clone(),
            e.meta.span,
            stringify!(ProverifRejectLoops),
            what.into(),
        );
        replace_by_error(e, vec![d]);
    }
}

impl Phase for ProverifRejectLoops {
    fn apply(&self, items: &mut Vec<Item>) {
        let mut visitor = RejectLoops {
            quiet: Quiet::new(items, &[]),
        };
        // An inlined function is not printed; its copies are checked.
        for item in items.iter_mut() {
            match &mut item.kind {
                ItemKind::Impl { items, .. } => {
                    for ii in items.iter_mut().filter(|ii| !is_late_skip(&ii.meta)) {
                        visitor.visit_impl_item(ii);
                    }
                }
                _ if is_late_skip(&item.meta) => {}
                _ => visitor.visit_item(item),
            }
        }
    }
}
