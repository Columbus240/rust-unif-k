use super::NNF;

impl NNF {
    pub fn display_beautiful<'a>(&'a self) -> DisplayBeautiful<'a> {
        DisplayBeautiful { nnf: self }
    }

    pub fn display_latex<'a>(&'a self) -> DisplayLaTeX<'a> {
        DisplayLaTeX { nnf: self }
    }

    pub fn display_spartacus<'a>(&'a self) -> DisplaySpartacus<'a> {
        DisplaySpartacus { nnf: self }
    }
}

pub struct DisplayBeautiful<'a> {
    nnf: &'a NNF,
}

impl<'a> std::fmt::Display for DisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.nnf {
            NNF::Top => write!(f, "⊤"),
            NNF::Bot => write!(f, "⊥"),
            NNF::AtomPos(i) => write!(f, "p{}", i),
            NNF::AtomNeg(i) => write!(f, "¬p{}", i),
            NNF::And(s) => {
                write!(f, "(")?;

                let mut set_iter = s.iter();

                match set_iter.next() {
                    None => write!(f, "⊤")?,
                    Some(x) => write!(f, "{}", x.display_beautiful())?,
                }

                for phi in set_iter {
                    write!(f, "∧{}", phi.display_beautiful())?;
                }

                write!(f, ")")
            }
            NNF::Or(s) => {
                write!(f, "(")?;

                let mut set_iter = s.iter();

                match set_iter.next() {
                    None => write!(f, "⊥")?,
                    Some(x) => write!(f, "{}", x.display_beautiful())?,
                }

                for phi in set_iter {
                    write!(f, "∨{}", phi.display_beautiful())?;
                }

                write!(f, ")")
            }
            NNF::NnfBox(phi0) => {
                write!(f, "□{}", phi0.display_beautiful())
            }
            NNF::NnfDia(phi0) => {
                write!(f, "◇{}", phi0.display_beautiful())
            }
        }
    }
}

pub struct DisplayLaTeX<'a> {
    nnf: &'a NNF,
}

impl<'a> std::fmt::Display for DisplayLaTeX<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.nnf {
            NNF::Top => write!(f, "\\top{{}}"),
            NNF::Bot => write!(f, "\\bot{{}}"),
            NNF::AtomPos(i) => write!(f, "p_{{{}}}", i),
            NNF::AtomNeg(i) => write!(f, "\\neg{{}}p_{{{}}}", i),
            NNF::And(s) => {
                write!(f, "(")?;

                let mut set_iter = s.iter();

                match set_iter.next() {
                    None => write!(f, "\\top{{}}")?,
                    Some(x) => write!(f, "{}", x.display_latex())?,
                }

                for phi in set_iter {
                    write!(f, "\\land{{}}{}", phi.display_latex())?;
                }

                write!(f, ")")
            }
            NNF::Or(s) => {
                write!(f, "(")?;

                let mut set_iter = s.iter();

                match set_iter.next() {
                    None => write!(f, "\\bot{{}}")?,
                    Some(x) => write!(f, "{}", x.display_latex())?,
                }

                for phi in set_iter {
                    write!(f, "\\lor{{}}{}", phi.display_latex())?;
                }

                write!(f, ")")
            }
            NNF::NnfBox(phi0) => {
                write!(f, "\\Box{{}}{}", phi0.display_latex())
            }
            NNF::NnfDia(phi0) => {
                write!(f, "\\Dia{{}}{}", phi0.display_latex())
            }
        }
    }
}

pub struct DisplaySpartacus<'a> {
    nnf: &'a NNF,
}

impl<'a> std::fmt::Display for DisplaySpartacus<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.nnf {
            NNF::Top => write!(f, "1"),
            NNF::Bot => write!(f, "0"),
            NNF::AtomPos(i) => write!(f, "p{}", i),
            NNF::AtomNeg(i) => write!(f, "~p{}", i),
            NNF::And(s) => {
                write!(f, "(")?;

                let mut set_iter = s.iter();

                match set_iter.next() {
                    None => write!(f, "1")?,
                    Some(x) => write!(f, "{}", x.display_spartacus())?,
                }

                for phi in set_iter {
                    write!(f, "&{}", phi.display_spartacus())?;
                }

                write!(f, ")")
            }
            NNF::Or(s) => {
                write!(f, "(")?;

                let mut set_iter = s.iter();

                match set_iter.next() {
                    None => write!(f, "0")?,
                    Some(x) => write!(f, "{}", x.display_spartacus())?,
                }

                for phi in set_iter {
                    write!(f, "|{}", phi.display_spartacus())?;
                }

                write!(f, ")")
            }
            NNF::NnfBox(phi0) => {
                write!(f, "[a]{}", phi0.display_spartacus())
            }
            NNF::NnfDia(phi0) => {
                write!(f, "<a>{}", phi0.display_spartacus())
            }
        }
    }
}
