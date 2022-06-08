// States of the TriplePowersetIterator
#[derive(Clone)]
enum TpiState<'a, T> {
    Empty(&'a T),
    Pos(&'a T, Vec<(bool, T)>),
    Neg(&'a T, Vec<(bool, T)>),
    NearlyDone,
    Done,
}

#[derive(Clone)]
pub struct TriplePowersetIterator<'a, T: Clone> {
    state: TpiState<'a, T>,
    prev_level: Option<Box<TriplePowersetIterator<'a, T>>>,
}

impl<'a, T: Clone> TriplePowersetIterator<'a, T> {
    pub fn new(input: &'a [T]) -> TriplePowersetIterator<'a, T> {
        if input.is_empty() {
            TriplePowersetIterator {
                state: TpiState::NearlyDone,
                prev_level: None,
            }
        } else {
            TriplePowersetIterator {
                state: TpiState::Empty(&input[0]),
                prev_level: Some(Box::new(TriplePowersetIterator::new(&input[1..]))),
            }
        }
    }
}

impl<'a, T: Clone> Iterator for TriplePowersetIterator<'a, T> {
    type Item = Vec<(bool, T)>;
    fn next(&mut self) -> Option<Vec<(bool, T)>> {
        match &mut self.state {
            TpiState::Empty(hd) => {
                if let Some(v) = {
                    if let Some(prev_level) = &mut self.prev_level {
                        prev_level.next()
                    } else {
                        None
                    }
                } {
                    self.state = TpiState::Pos(hd, v.clone());
                    Some(v)
                } else {
                    // be done
                    self.state = TpiState::NearlyDone;
                    self.prev_level = None;
                    None
                }
            }
            TpiState::Pos(hd, v) => {
                let mut v2 = v.clone();
                v2.push((true, hd.clone()));
                self.state = TpiState::Neg(hd, v.clone());
                Some(v2)
            }
            TpiState::Neg(hd, v) => {
                let mut v2 = v.clone();
                v2.push((false, hd.clone()));
                self.state = TpiState::Empty(hd);
                Some(v2)
            }
            TpiState::NearlyDone => {
                self.state = TpiState::Done;
                self.prev_level = None;
                Some(vec![])
            }
            TpiState::Done => {
                self.prev_level = None;
                None
            }
        }
    }
}
