use std::ops::{Add, Mul, BitXor};
use std::string::ToString;

// #[macro_use]
use cnf::List;
use cnf::Cnf;
use cnf::Cnf::{Atom,Polynom};
use cnf::OmegaPow;

trait ToCnf {
    fn to_cnf(&self) -> Cnf;
}

pub enum Ordinal {
    Num(u32),
    Sum(Box<Ordinal>, Box<Ordinal>),
    Prod(Box<Ordinal>, Box<Ordinal>),
    Exp(Box<Ordinal>, Box<Ordinal>),
    Omega,
}

impl Add for Ordinal {
    type Output = Ordinal;

    fn add(self, other: Ordinal) -> Ordinal {
        Ordinal::Sum(Box::new(self), Box::new(other))
    }
}

impl Mul for Ordinal {
    type Output = Ordinal;

    fn mul(self, other: Ordinal) -> Ordinal {
        Ordinal::Prod(Box::new(self), Box::new(other))
    }
}

impl BitXor for Ordinal {
    type Output = Ordinal;

    fn bitxor(self, other: Ordinal) -> Ordinal {
        Ordinal::Exp(Box::new(self), Box::new(other))
    }
}

impl PartialEq for Ordinal {
    fn eq(&self, other: &Ordinal) -> bool {
        self.to_cnf() == other.to_cnf()
    }
}

impl ToString for Ordinal {
    fn to_string(&self) -> String {
        match self {
            &Ordinal::Num(n) => n.to_string(),
            &Ordinal::Omega => "w".to_string(),
            &Ordinal::Sum(ref a, ref b) => {
                "(".to_string() + &a.to_string() + "+" + &b.to_string() + ")"
            }
            &Ordinal::Prod(ref a, ref b) => {
                "(".to_string() + &a.to_string() + "*" + &b.to_string() + ")"
            }
            &Ordinal::Exp(ref a, ref b) => {
                "(".to_string() + &a.to_string() + "^" + &b.to_string() + ")"
            }
        }
    }
}

impl ToCnf for Ordinal {
    fn to_cnf(&self) -> Cnf {
        match self {
            &Ordinal::Num(n) => Atom(n),
            &Ordinal::Omega => Polynom(list![OmegaPow{exp: Atom(1), coeff: 1}], 0),
            &Ordinal::Sum(ref a, ref b) => a.to_cnf() + b.to_cnf(),
            &Ordinal::Prod(ref a, ref b) => a.to_cnf() * b.to_cnf(),
            &Ordinal::Exp(ref a, ref b) => a.to_cnf() ^ b.to_cnf(),
        }
    }
}
