use std::ops::{Add, Mul, BitXor};
use std::cmp::Ordering;

#[derive(Clone, PartialEq)]
pub struct List<T> {
    pub head: Box<T>, // non-empty
    pub tail: Option<Box<List<T>>>,
}

#[macro_export]
macro_rules! list[
    ($x:expr)                => (List{head: Box::new($x), tail: None});
    ($x:expr, $($xs:expr),+) => (List(head: Box::new($x), tail: Some(list!($($xs),+))));
];

#[derive(Clone, PartialEq)]
pub struct OmegaPow {
    pub exp: Cnf,
    pub coeff: u32,
}

#[derive(Clone, PartialEq)]
pub enum Cnf {
    Atom(u32),
    Polynom(List<OmegaPow>, u32),
}

impl Cnf {
    fn tail(&self) -> Cnf {
        match self {
            &Cnf::Polynom(List { tail: Some(ref t), .. }, n) => Cnf::Polynom(*t.clone(), n),
            &Cnf::Polynom(_, n) => Cnf::Atom(n),
            _ => panic!("only polynoms have .tail()"),
        }
    }
    fn greatest_pow(&self) -> OmegaPow {
        match self {
            &Cnf::Atom(n) => {
                OmegaPow {
                    exp: Cnf::Atom(0),
                    coeff: n,
                }
            }
            &Cnf::Polynom(List { ref head, .. }, ..) => *head.clone(),
        }
    }
    fn is_finite(&self) -> bool {
        match self {
            &Cnf::Atom(0) => true,
            &Cnf::Atom(_) => false,
            &Cnf::Polynom(..) => self.tail().is_finite(),
        }
    }
    fn natural_part(&self) -> u32 {
        match self {
            &Cnf::Atom(n) => n,
            &Cnf::Polynom(..) => self.tail().natural_part(),
        }
    }
    fn greatest_finite_subordinal(&self) -> Cnf {
        match self {
            &Cnf::Atom(_) => Cnf::Atom(0),
            &Cnf::Polynom(List { ref head, .. }, ..) => {
                match self.tail().greatest_finite_subordinal() {
                    Cnf::Atom(n) => Cnf::Polynom(list![*head.clone()], n),
                    Cnf::Polynom(l, n) => {
                        Cnf::Polynom(List {
                                         head: head.clone(),
                                         tail: Some(Box::new(l)),
                                     }, n)
                    }
                }
            }
        }
    }
}

fn dec(cnf: &Cnf) -> Cnf {
    match cnf {
        &Cnf::Atom(n) => Cnf::Atom(n - 1),
        _ => cnf.clone(),
    }
}

fn finite_pow_cnf(mant: u32, exp: &Cnf) -> Cnf {
    match exp {
        &Cnf::Polynom(List {
                          head: ref h,
                          tail: None,
                      }, f) => {
            let new_exp = match h.exp {
                Cnf::Atom(1) => Cnf::Atom(h.coeff),
                _ => {
                    Cnf::Polynom(list![OmegaPow {
                                           exp: dec(&h.exp),
                                           coeff: h.coeff,
                                       }], 0)
                }
            };
            Cnf::Polynom(list![OmegaPow {
                                   exp: new_exp,
                                   coeff: mant.pow(f),
                               }], 0)
        }
        &Cnf::Polynom(List {
                          head: ref h,
                          tail: Some(ref t),
                      }, f) => {
            let c = finite_pow_cnf(mant, &Cnf::Polynom(*t.clone(), f));
            let new_exp = match c {
                Cnf::Polynom(List { ref head, .. }, ..) => dec(&head.exp),
                _ => dec(&c),
            };
            Cnf::Polynom(list![OmegaPow {
                                   exp: Cnf::Polynom(list![OmegaPow {
                                                               exp: new_exp,
                                                               coeff: h.coeff,
                                                           }], 0) +
                                        c.greatest_pow().exp,
                                   coeff: c.greatest_pow().coeff,
                               }], 0)
        }
        _ => panic!("exp expected to be non-finite"),
    }
}

fn limit_pow_finite(mant: &Cnf, exp: u32) -> Cnf {
    match exp {
        1 => mant.clone(),
        _ => {
            Cnf::Polynom(list![OmegaPow {
                                   exp: mant.greatest_pow().exp * Cnf::Atom(exp - 1),
                                   coeff: 1,
                               }],
                         0) * mant.clone()
        }
    }
}

fn cnf_pow_finite(mant: &Cnf, exp: u32) -> Cnf {
    match exp {
        0 => Cnf::Atom(1),
        1 => mant.clone(),
        _ if mant.is_finite() => limit_pow_finite(mant, exp),
        _ => cnf_pow_finite(mant, exp - 1) * mant.clone(),
    }
}

fn cnf_pow_cnf(mant: &Cnf, exp: &Cnf) -> Cnf {
    Cnf::Polynom(list![OmegaPow {
                           exp: mant.greatest_pow().exp * exp.greatest_finite_subordinal(),
                           coeff: 1,
                       }],
                 0) * cnf_pow_finite(mant, exp.natural_part())
}

impl PartialOrd for Cnf {
    fn partial_cmp(&self, other: &Cnf) -> Option<Ordering> {
        match (self, other) {
            (&Cnf::Atom(a), &Cnf::Atom(b)) => a.partial_cmp(&b),
            (&Cnf::Atom(_), _) => Some(Ordering::Less),
            (&Cnf::Polynom(..), &Cnf::Atom(_)) => Some(Ordering::Greater),
            (&Cnf::Polynom(..), &Cnf::Polynom(..)) if self.greatest_pow().exp !=
                                                      other.greatest_pow().exp => {
                self.greatest_pow().exp
                    .partial_cmp(&other.greatest_pow().exp)
            }
            _ if self.greatest_pow().coeff != other.greatest_pow().coeff => {
                self.greatest_pow().coeff
                    .partial_cmp(&other.greatest_pow().coeff)
            }
            _ => self.tail().partial_cmp(&other.tail()),
        }
    }
}

impl OmegaPow {
    fn add(self, other: Cnf) -> Cnf {
        match other {
            Cnf::Atom(n) => Cnf::Polynom(list![self], n),
            Cnf::Polynom(els, n) => {
                Cnf::Polynom(List {
                                 head: Box::new(self),
                                 tail: Some(Box::new(els)),
                             }, n)
            }
        }
    }
}

impl Add for Cnf {
    type Output = Cnf;

    fn add(self, other: Cnf) -> Cnf {
        match (&self, &other) {
            (&Cnf::Atom(n), &Cnf::Atom(m)) => Cnf::Atom(n + m),
            _ => {
                let h1 = self.greatest_pow();
                let h2 = other.greatest_pow();
                if h1.exp < h2.exp {
                    other
                } else if h1.exp == h2.exp {
                    OmegaPow {
                            exp: h1.exp,
                            coeff: h1.coeff + h2.coeff,
                        }.add(other.tail())
                } else {
                    OmegaPow {
                            exp: h1.exp,
                            coeff: h1.coeff,
                        }.add(self.tail() + other)
                }
            }
        }
    }
}

impl Mul for Cnf {
    type Output = Cnf;

    fn mul(self, other: Cnf) -> Cnf {
        match (&self, &other) {
            (&Cnf::Atom(0), _) => Cnf::Atom(0),
            (_, &Cnf::Atom(0)) => Cnf::Atom(0),
            (&Cnf::Atom(n), &Cnf::Atom(m)) => Cnf::Atom(n * m),
            (_, &Cnf::Atom(m)) => {
                OmegaPow {
                        exp: self.greatest_pow().exp,
                        coeff: self.greatest_pow().coeff * m,
                    }.add(self.tail())
            }
            _ => {
                OmegaPow {
                        exp: self.greatest_pow().exp + other.greatest_pow().exp,
                        coeff: other.greatest_pow().coeff,
                    }.add(self * other.tail())
            }
        }
    }
}

impl BitXor for Cnf {
    type Output = Cnf;

    fn bitxor(self, other: Cnf) -> Cnf {
        match (&self, &other) {
            (&Cnf::Atom(0), _) => Cnf::Atom(0),
            (&Cnf::Atom(1), _) => Cnf::Atom(1),
            (_, &Cnf::Atom(0)) => Cnf::Atom(1),
            (&Cnf::Atom(n), &Cnf::Atom(m)) => Cnf::Atom(n.pow(m)),
            (&Cnf::Atom(n), _) => finite_pow_cnf(n, &other),
            (_, &Cnf::Atom(n)) => cnf_pow_finite(&self, n),
            _ => cnf_pow_cnf(&self, &other),
        }
    }
}
