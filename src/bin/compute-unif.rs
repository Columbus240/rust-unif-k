//! Go through all normal forms and decide unifiability.
extern crate generator;
use generator::FineFormIter;

fn main() {
    let mut dec_false: usize = 0;
    let mut dec_true: usize = 0;
    let mut undecidable: usize = 0;
    for (i, nnf) in FineFormIter::new(1).enumerate().skip(8000) {
	    if i > 8100 {
		    return;
	    }
        let nnf_simpl = nnf.clone().simpl();
        let deg = nnf_simpl.degree();
        let nnf_simpl_unif = nnf_simpl.check_unifiable();
        //println!("formula: {}", nnf.display_beautiful());
        match nnf_simpl_unif {
            Ok(b) => {
                if b {
                    dec_true += 1;
                } else {
                    dec_false += 1;
                }
                println!("index {}, degree {}, unifiable: {}", i, deg, b);
            }
            Err(e) => {
                undecidable += 1;
                println!(
                    "index {}, degree {}, gets stuck at:\n{}",
                    i,
                    deg,
                    e.display_beautiful()
                )
            }
        }
        println!(
            "stuck {} vs. dec true {} dec false {}",
            undecidable, dec_true, dec_false
        );
    }
}
