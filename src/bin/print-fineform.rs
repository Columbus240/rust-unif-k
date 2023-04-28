extern crate generator;
use generator::BasicFineFormIter;
use generator::BasicFineFormNNFIter;
use generator::FineFormNNFIter;
use generator::NNF;

fn main() {
    let num_variables = 0;
    let mut iter_nnf = FineFormNNFIter::new(num_variables);
    let mut iter_ff = BasicFineFormIter::new(num_variables);

    let mut i: usize = 0;
    loop {
        let ff = iter_ff.next().unwrap();
        let nnf = iter_nnf.next().unwrap();
        if iter_nnf.get_curr_level() > 2 {
            break;
        }

        println!(
            "index {}, level_nnf {}, nnf {}",
            i,
            iter_nnf.get_curr_level(),
            nnf.display_beautiful()
        );
        i += 1;
    }
}
