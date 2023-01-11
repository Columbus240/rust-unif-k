extern crate generator;
use generator::BasicFineFormIter;
use generator::BasicFineFormNNFIter;
use generator::NNF;

fn main() {
    let num_variables = 0;
    let mut iter_nnf = BasicFineFormNNFIter::new(num_variables);
    let mut iter_ff = BasicFineFormIter::new(num_variables);

    let mut i: usize = 0;
    while i < 32 {
        let ff = iter_ff.next().unwrap();
        let nnf = iter_nnf.next().unwrap();
        let ff_nnf_simpl = ff.to_nnf().simpl();
        let nnf_simpl = nnf.simpl();
        println!(
            "index {}, level_ff {}, level_nnf {}, ff {}, nnf {}, equiv {}",
            i,
            iter_ff.get_curr_level(),
            iter_nnf.get_curr_level(),
            ff_nnf_simpl.display_beautiful(),
            nnf_simpl.display_beautiful(),
            NNF::equiv_dec(&ff_nnf_simpl, &nnf_simpl)
        );
        i += 1;
    }
}
