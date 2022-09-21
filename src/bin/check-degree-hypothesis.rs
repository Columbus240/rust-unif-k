extern crate generator;
use generator::FineFormIter;
//fineform_correct::FineFormIter;
//use generator::nnf::NNF;

fn main() {
    'a: for (i, nnf) in FineFormIter::new(1).enumerate() {
        let nnf_simpl = nnf.simpl();
        if let Ok(b) = nnf_simpl.clone().check_unifiable() {
            if !b {
                println!("index {}, nonunif", i);
                continue 'a;
            }
            let deg = nnf_simpl.degree();
            let mut unif_iter = FineFormIter::new(0);
            while unif_iter.get_curr_level() <= deg {
                let subst = nnf_simpl.clone().substitute_all(&unif_iter.next().unwrap());
                if subst.is_valid() {
                    println!("index {}, unif ok", i);
                    continue 'a;
                }
            }
            panic!("index {}, formula {}", i, nnf_simpl.display_beautiful());
        } else {
            println!("index {}, non-dec", i);
        }
    }
}
