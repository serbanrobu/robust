use crate::{Level, Name};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Nameless {
    ImplicitLambda(Box<Lambda>),
    ImplicitPiType(Box<Nameless>, Box<Lambda>),
    Lambda(Box<Lambda>),
    Neutral(Box<Neutral>),
    PiType(Box<Nameless>, Box<Lambda>),
    UniverseType(Level),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Neutral {
    Application(Box<Neutral>, Nameless),
    ImplicitApplication(Box<Neutral>, Nameless),
    Variable(usize, Level),
    Free(Name, Level),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lambda(pub Nameless);
