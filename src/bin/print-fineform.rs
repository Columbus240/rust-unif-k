extern crate generator;
use generator::BasicFineFormIter;
use generator::BasicFineFormNNFIter;
use generator::NNF;

fn main() {
    let num_variables = 1;
    let mut iter_ff = BasicFineFormIter::new(num_variables);

    let mut i: usize = 0;
    loop {
        let ff = iter_ff.next().unwrap();
        println!(
            "index {}, level_ff {}, ff {}",
            i,
            iter_ff.get_curr_level(),
            ff
        );
        i += 1;

	if iter_ff.get_curr_level() > 2 {
		break;
	}
    }
}
