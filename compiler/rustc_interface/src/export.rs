use std::fs::File;
use std::io::{self, BufWriter, Write};

use rustc_ast_pretty::pprust::PrintState;
use rustc_hir as hir;
use rustc_hir_pretty::{AnnNode, Nested, PpAnn, State};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::{OutFileName, OutputType};

struct InterfaceAnn<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> PpAnn for InterfaceAnn<'tcx> {
    // FIXME: modify `State` instead?
    fn pre(&self, state: &mut State<'_>, _node: AnnNode<'_>) {
        state.word_nbsp("pub");
    }

    // Do not print fn bodies.
    fn nested(&self, state: &mut State<'_>, nested: Nested) {
        // TODO: check body kind, what about consts?
        if let Nested::Body(_) = nested {
            return;
        }
        self.tcx.nested(state, nested);
    }

    // Insert empty fn bodies.
    fn post(&self, state: &mut State<'_>, node: AnnNode<'_>) {
        let AnnNode::Item(item) = node else {
            return;
        };

        let hir::ItemKind::Fn(..) = item.kind else {
            return;
        };

        state.word_nbsp("{ loop {} }");
    }
}

pub fn write_interface<'tcx>(tcx: TyCtxt<'tcx>) {
    let sess = tcx.sess;
    if !sess.opts.output_types.contains_key(&OutputType::Interface) {
        return;
    }
    let _timer = sess.timer("write_interface");
    let outputs = tcx.output_filenames(());

    let ann = InterfaceAnn { tcx };
    let attrs = |id| tcx.hir().attrs(id);
    let mut state = State::new(None, &attrs, &ann);

    // TODO: is it ok to use `attr_id_generator` here?
    state.print_fake_attr(sess.edition(), &sess.psess.attr_id_generator);
    let krate = rustc_hir_pretty::print_crate_with_state(state, tcx.hir().root_module(), &attrs);

    let export_output = outputs.path(OutputType::Interface);
    // TODO: error handling
    match export_output {
        OutFileName::Stdout => {
            let mut file = BufWriter::new(io::stdout());
            let _ = write!(file, "{}", krate);
        }
        OutFileName::Real(ref path) => {
            let mut file = File::create_buffered(path).unwrap();
            let _ = write!(file, "{}", krate);
        }
    }
}
