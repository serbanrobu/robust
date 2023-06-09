#![feature(never_type, unwrap_infallible, box_patterns, box_syntax)]

mod nameless;

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Report, Result,
};
use nameless::Nameless;
use thiserror::Error;

#[derive(Clone, Debug, Error)]
#[error("hole")]
pub struct Hole;

pub type Context = HashMap<Name, Type<Hole>>;

#[derive(Clone, Debug)]
pub enum Expression<H> {
    Application(Box<Self>, Box<Self>),
    Hole(H),
    ImplicitApplication(Box<Self>, Box<Self>),
    ImplicitLambda(Box<Lambda<Self>>),
    ImplicitPiType(Box<Self>, Box<Lambda<Self>>),
    Lambda(Box<Lambda<Self>>),
    Lift(Level, Box<Self>),
    PiType(Box<Self>, Box<Lambda<Self>>),
    Substitution(Box<Self>, Box<Self>, Name),
    UniverseType(Level),
    Variable(Name, Level),
}

impl Expression<Hole> {
    pub fn check(
        self,
        r#type: Type<Hole>,
        context: Cow<Context>,
    ) -> Result<(Expression<!>, Type<!>)> {
        match self {
            Self::ImplicitLambda(lambda) => {
                let Type::ImplicitPi(a_type, b_type) = r#type else {
                    return Err(eyre!(""));
                };

                lambda.check(*a_type, b_type, context)
            }
            Self::ImplicitPiType(a_type, b_type) | Self::PiType(a_type, b_type) => {
                let Type::Universe(i) = a_type.check(r#type, context.clone())? else {
                    return Err(eyre!(""));
                };

                b_type.check(
                    a_type.as_ref().to_owned().evaluate()?.try_into()?,
                    Lambda {
                        name: None,
                        body: Self::UniverseType(i),
                    },
                    context,
                )
            }
            Self::Lambda(lambda) => {
                let Type::Pi(a_type, b_type) = r#type else {
                    return Err(eyre!(""));
                };

                lambda.check(*a_type, b_type, context)
            }
            &Self::UniverseType(i) => {
                if let Type::Universe(j) = r#type {
                    if i >= j {
                        return Err(eyre!(""));
                    }

                    return Ok(Type::Universe(j));
                }

                Ok(Type::Universe(i.checked_add(1).wrap_err("")?))
            }

            // infer
            Self::Application(f, a) => {
                let f_type = f.check(Type::Hole(Hole), context.clone())?;

                match f_type {
                    Type::ImplicitPi(a_type, b_type) => {
                        todo!()
                    }
                    Type::Pi(box a_type, b_type) => {
                        a.check(a_type.into(), context)?;
                        b_type.apply(a.as_ref().to_owned()).evaluate()?.try_into()
                    }
                    _ => Err(eyre!("")),
                }
            }
            Self::ImplicitApplication(f, a) => {
                todo!()
            }
            Self::Lift(i, a) => a.as_ref().to_owned().lift(*i)?.check(r#type, context),
            Self::Substitution(a, b, x) => a
                .as_ref()
                .to_owned()
                .substitute(b.as_ref().to_owned(), x.to_owned())?
                .check(r#type, context),
            Self::Variable(x, i) => {
                let r#type: Type<!> = context.get(&x).cloned().wrap_err("not found")?.try_into()?;
                r#type.lift(i)
            }
        }
    }

    pub fn lift(self, i: Level) -> Result<Self> {
        match self {
            Self::Application(f, a) => Ok(Self::Application(
                Box::new(Self::Lift(i, f)),
                Box::new(Self::Lift(i, a)),
            )),
            e @ Self::Hole(_) => Ok(e),
            Self::ImplicitApplication(f, a) => Ok(Self::ImplicitApplication(
                Box::new(Self::Lift(i, f)),
                Box::new(Self::Lift(i, a)),
            )),
            Self::ImplicitLambda(lambda) => Ok(Self::ImplicitLambda(Box::new(lambda.lift(i)?))),
            Self::ImplicitPiType(a_type, b_type) => Ok(Self::ImplicitPiType(
                Box::new(a_type.lift(i)?),
                Box::new(b_type.lift(i)?),
            )),
            Self::Lambda(lambda) => Ok(Self::Lambda(Box::new(lambda.lift(i)?))),
            Self::Lift(j, a) => Ok(Self::Lift(i.checked_add(j).wrap_err("")?, a)),
            Self::PiType(a_type, b_type) => Ok(Self::PiType(
                Box::new(a_type.lift(i)?),
                Box::new(b_type.lift(i)?),
            )),
            Self::Substitution(a, b, x) => Ok(Self::Substitution(
                Box::new(a.lift(i)?),
                Box::new(b.lift(i)?),
                x,
            )),
            Self::UniverseType(j) => Ok(Self::UniverseType(i.checked_add(j).wrap_err("")?)),
            Self::Variable(x, j) => Ok(Self::Variable(x, i.checked_add(j).wrap_err("")?)),
        }
    }

    pub fn normalize(self, names: Cow<HashSet<Name>>) -> Result<Normal> {
        self.evaluate()?.normalize(names)
    }

    pub fn substitute(self, a: Self, x: Name) -> Result<Self> {
        match self {
            Self::Application(f, b) => Ok(Self::Application(
                Box::new(Self::Substitution(f, Box::new(a.clone()), x.clone())),
                Box::new(Self::Substitution(b, Box::new(a), x)),
            )),
            Self::ImplicitApplication(f, b) => Ok(Self::ImplicitApplication(
                Box::new(Self::Substitution(f, Box::new(a.clone()), x.clone())),
                Box::new(Self::Substitution(b, Box::new(a), x)),
            )),
            Self::ImplicitLambda(lambda) => {
                Ok(Self::ImplicitLambda(Box::new(lambda.substitute(a, x))))
            }
            Self::ImplicitPiType(a_type, b_type) => Ok(Self::ImplicitPiType(
                Box::new(Self::Substitution(a_type, Box::new(a.clone()), x.clone())),
                Box::new(b_type.substitute(a, x)),
            )),
            Self::Lambda(lambda) => Ok(Self::Lambda(Box::new(lambda.substitute(a, x)))),
            Self::Lift(i, e) => e.lift(i),
            Self::PiType(a_type, b_type) => Ok(Self::PiType(
                Box::new(Self::Substitution(a_type, Box::new(a.clone()), x.clone())),
                Box::new(b_type.substitute(a, x)),
            )),
            Self::Substitution(b, c, y) => Ok(Self::Substitution(
                Box::new(b.substitute(a.clone(), x.clone())?),
                Box::new(c.substitute(a, x)?),
                y,
            )),
            e @ Self::UniverseType(_) => Ok(e),
            Self::Variable(y, i) => {
                if x == y {
                    a.lift(i)
                } else {
                    Ok(Self::Variable(y, i))
                }
            }
        }
    }
}

impl<H> Expression<H> {
    pub fn evaluate(self) -> Result<Value<H>> {
        match self {
            Self::Application(f, a) => match f.evaluate()? {
                Value::ImplicitLambda(lambda) => todo!(),
                Value::Lambda(lambda) => lambda.apply(*a).evaluate(),
                Value::Neutral(f) => Ok(Value::Neutral(Box::new(Neutral::Application(
                    f,
                    a.evaluate()?,
                )))),
                _ => Err(eyre!("invalid application")),
            },
            Self::Hole(hole) => Ok(Value::Neutral(Box::new(Neutral::Hole(hole)))),
            Self::ImplicitApplication(f, a) => match f.evaluate()? {
                Value::ImplicitLambda(lambda) => lambda.apply(*a).evaluate(),
                Value::Neutral(f) => Ok(Value::Neutral(Box::new(Neutral::Application(
                    f,
                    a.evaluate()?,
                )))),
                _ => Err(eyre!("invalid application")),
            },
            Self::ImplicitLambda(lambda) => Ok(Value::ImplicitLambda(*lambda)),
            Self::ImplicitPiType(a_type, b_type) => {
                Ok(Value::ImplicitPiType(Box::new(a_type.evaluate()?), *b_type))
            }
            Self::Substitution(a, b, x) => a.substitute(*b, x)?.evaluate(),
            Self::Lambda(lambda) => Ok(Value::Lambda(*lambda)),
            Self::Lift(i, e) => e.lift(i)?.evaluate(),
            Self::PiType(a_type, b_type) => {
                Ok(Value::PiType(Box::new(a_type.evaluate()?), *b_type))
            }
            Self::UniverseType(i) => Ok(Value::UniverseType(i)),
            Self::Variable(x, i) => Ok(Value::Neutral(Box::new(Neutral::Variable(x, i)))),
        }
    }
}

pub fn freshen(mut name: Name, names: &HashSet<Name>) -> Name {
    if names.contains(&name) {
        name.push('\'');
        freshen(name, names)
    } else {
        name
    }
}

#[derive(Clone, Debug)]
pub struct Lambda<T> {
    pub name: Option<Name>,
    pub body: T,
}

impl<H> Lambda<Expression<H>> {
    pub fn apply(self, a: Expression<H>) -> Expression<H> {
        match self.name {
            None => self.body,
            Some(x) => Expression::Substitution(Box::new(self.body), Box::new(a), x),
        }
    }

    pub fn check(
        &self,
        a_type: Type<H>,
        b_type: Lambda<Expression<H>>,
        mut context: Cow<Context>,
    ) -> Result<(Expression<!>, Type<!>)> {
        let b_type = if let Some(x) = &self.name {
            context.to_mut().insert(x.to_owned(), a_type);
            b_type.apply(Expression::Variable(x.to_owned(), 0))
        } else {
            if let Some(x) = b_type.name {
                context.to_mut().insert(x, a_type);
            }

            b_type.body
        };

        self.body.check(b_type.evaluate()?.try_into()?, context)
    }

    pub fn lift(self, i: Level) -> Result<Self> {
        Ok(Self {
            body: self.body.lift(i)?,
            ..self
        })
    }

    pub fn normalize(self, mut names: Cow<HashSet<Name>>) -> Result<Lambda<Normal>> {
        Ok(Lambda {
            name: self.name.map(|x| {
                if names.contains(&x) {
                    let x = freshen(x, &names);
                    names.to_mut().insert(x.clone());
                    x
                } else {
                    x
                }
            }),
            body: self.body.normalize(names)?,
        })
    }

    pub fn substitute(self, a: Expression<H>, x: Name) -> Self {
        Self {
            name: self.name,
            body: Expression::Substitution(Box::new(self.body), Box::new(a), x),
        }
    }
}

impl Lambda<Normal> {
    pub fn nameless(self, i: usize, mut names: Cow<HashMap<Name, usize>>) -> nameless::Lambda {
        if let Some(x) = self.name {
            names.to_mut().insert(x, i);
        }

        nameless::Lambda(self.body.nameless(i + 1, names))
    }
}

pub type Level = u8;

pub type Name = String;

#[derive(Clone, Debug)]
pub enum Normal {
    ImplicitLambda(Box<Lambda<Normal>>),
    ImplicitPiType(Box<Normal>, Box<Lambda<Normal>>),
    Lambda(Box<Lambda<Normal>>),
    Neutral(Box<Neutral<Normal>>),
    PiType(Box<Normal>, Box<Lambda<Normal>>),
    UniverseType(Level),
}

impl Normal {
    pub fn alpha_eq(self, other: Self) -> bool {
        self.nameless(0, Cow::Owned(HashMap::new()))
            == other.nameless(0, Cow::Owned(HashMap::new()))
    }

    pub fn nameless(self, i: usize, names: Cow<HashMap<Name, usize>>) -> Nameless {
        match self {
            Self::ImplicitLambda(lambda) => {
                Nameless::ImplicitLambda(Box::new(lambda.nameless(i, names)))
            }
            Self::ImplicitPiType(a_type, b_type) => Nameless::ImplicitPiType(
                Box::new(a_type.nameless(i, names.clone())),
                Box::new(b_type.nameless(i, names)),
            ),
            Self::Lambda(lambda) => Nameless::Lambda(Box::new(lambda.nameless(i, names))),
            Self::Neutral(neutral) => Nameless::Neutral(Box::new(neutral.nameless(i, names))),
            Self::PiType(a_type, b_type) => Nameless::PiType(
                Box::new(a_type.nameless(i, names.clone())),
                Box::new(b_type.nameless(i, names)),
            ),
            Self::UniverseType(i) => Nameless::UniverseType(i),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Neutral<H, T> {
    Application(Box<Self>, T),
    Hole(H),
    ImplicitApplication(Box<Self>, T),
    Variable(Name, Level),
}

impl<H> Neutral<H, Value> {
    fn lift(self, i: Level) -> Result<Self> {
        match self {
            Self::Application(f, a) => Ok(Self::Application(Box::new(f.lift(i)?), a.lift(i)?)),
            Self::ImplicitApplication(f, a) => {
                Ok(Self::ImplicitApplication(Box::new(f.lift(i)?), a.lift(i)?))
            }
            Self::Variable(x, j) => Ok(Self::Variable(x, i.checked_add(j).wrap_err("")?)),
        }
    }

    fn normalize(self, names: Cow<HashSet<Name>>) -> Result<Neutral<Normal>> {
        match self {
            Self::Application(f, a) => Ok(Neutral::Application(
                Box::new(f.normalize(names.clone())?),
                a.normalize(names)?,
            )),
            Self::ImplicitApplication(f, a) => Ok(Neutral::ImplicitApplication(
                Box::new(f.normalize(names.clone())?),
                a.normalize(names)?,
            )),
            Self::Variable(x, i) => Ok(Neutral::Variable(x, i)),
        }
    }
}

impl Neutral<Normal> {
    fn nameless(self, i: usize, names: Cow<HashMap<Name, usize>>) -> nameless::Neutral {
        match self {
            Self::Application(f, a) => nameless::Neutral::Application(
                Box::new(f.nameless(i, names.clone())),
                a.nameless(i, names),
            ),
            Self::ImplicitApplication(f, a) => nameless::Neutral::ImplicitApplication(
                Box::new(f.nameless(i, names.clone())),
                a.nameless(i, names),
            ),
            Self::Variable(x, j) => names.get(&x).cloned().map_or_else(
                || nameless::Neutral::Free(x, j),
                |k| nameless::Neutral::Variable(k, j),
            ),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Type<H> {
    ImplicitPi(Box<Self>, Lambda<Expression<H>>),
    Pi(Box<Self>, Lambda<Expression<H>>),
    Neutral(Neutral<H, Value<H>>),
    Universe(Level),
}

impl Type<!> {
    pub fn lift(self, i: Level) -> Result<Self> {
        match self {
            Self::Hole(_) => unreachable!(),
            Self::ImplicitPi(a, b) => Ok(Self::ImplicitPi(Box::new(a.lift(i)?), b.lift(i)?)),
            Self::Pi(a, b) => Ok(Self::Pi(Box::new(a.lift(i)?), b.lift(i)?)),
            Self::Neutral(n) => Ok(Self::Neutral(n.lift(i)?)),
            Self::Universe(j) => Ok(Self::Universe(j.checked_add(i).wrap_err("")?)),
        }
    }
}

impl From<Type<!>> for Type<Hole> {
    fn from(value: Type<!>) -> Self {
        match value {
            Type::Hole(_) => unreachable!(),
            Type::ImplicitPi(a_type, b_type) => {
                Self::ImplicitPi(Box::new(Self::from(*a_type)), b_type)
            }
            Type::Pi(a_type, b_type) => Self::Pi(Box::new(Self::from(*a_type)), b_type),
            Type::Neutral(neutral) => Self::Neutral(neutral),
            Type::Universe(i) => Self::Universe(i),
        }
    }
}

impl TryFrom<Type<Hole>> for Type<!> {
    type Error = Hole;

    fn try_from(value: Type<Hole>) -> Result<Self, Self::Error> {
        match value {
            Type::Hole(hole) => Err(hole),
            Type::ImplicitPi(box a_type, b_type) => {
                Ok(Self::ImplicitPi(Box::new(a_type.try_into()?), b_type))
            }
            Type::Pi(box a, b) => Ok(Self::Pi(box a.try_into()?, b)),
            Type::Neutral(neutral) => Ok(Self::Neutral(neutral)),
            Type::Universe(i) => Ok(Self::Universe(i)),
        }
    }
}

impl<E> TryFrom<Value> for Type<E> {
    type Error = Report;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::ImplicitLambda(_) => Err(eyre!("not a type")),
            Value::ImplicitPiType(a_type, b_type) => {
                Ok(Self::ImplicitPi(Box::new(Self::try_from(*a_type)?), b_type))
            }
            Value::Lambda(_) => Err(eyre!("not a type")),
            Value::Neutral(neutral) => Ok(Self::Neutral(*neutral)),
            Value::PiType(a_type, b_type) => {
                Ok(Self::Pi(Box::new(Self::try_from(*a_type)?), b_type))
            }
            Value::UniverseType(i) => Ok(Self::Universe(i)),
        }
    }
}

impl From<Type<!>> for Value {
    fn from(value: Type<!>) -> Self {
        match value {
            Type::Hole(_) => unreachable!(),
            Type::ImplicitPi(a_type, b_type) => {
                Self::ImplicitPiType(Box::new(Self::from(*a_type)), b_type)
            }
            Type::Pi(a_type, b_type) => Self::PiType(Box::new(Self::from(*a_type)), b_type),
            Type::Neutral(neutral) => Self::Neutral(Box::new(neutral)),
            Type::Universe(i) => Self::UniverseType(i),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value<H> {
    ImplicitLambda(Lambda<Expression<H>>),
    ImplicitPiType(Box<Self>, Lambda<Expression<H>>),
    Lambda(Lambda<Expression<H>>),
    Neutral(Box<Neutral<H, Self>>),
    PiType(Box<Self>, Lambda<Expression>),
    UniverseType(Level),
}

impl Value {
    pub fn lift(self, i: Level) -> Result<Self> {
        match self {
            Self::ImplicitLambda(lambda) => Ok(Self::ImplicitLambda(lambda.lift(i)?)),
            Self::ImplicitPiType(a_type, b_type) => Ok(Self::ImplicitPiType(
                Box::new(a_type.lift(i)?),
                b_type.lift(i)?,
            )),
            Self::Lambda(lambda) => Ok(Self::Lambda(lambda.lift(i)?)),
            Self::Neutral(neutral) => Ok(Self::Neutral(Box::new(neutral.lift(i)?))),
            Self::PiType(a_type, b_type) => {
                Ok(Self::PiType(Box::new(a_type.lift(i)?), b_type.lift(i)?))
            }
            Self::UniverseType(j) => Ok(Self::UniverseType(i.checked_add(j).wrap_err("")?)),
        }
    }

    pub fn normalize(self, names: Cow<HashSet<Name>>) -> Result<Normal> {
        match self {
            Self::ImplicitLambda(lambda) => {
                Ok(Normal::ImplicitLambda(Box::new(lambda.normalize(names)?)))
            }
            Self::ImplicitPiType(a_type, b_type) => Ok(Normal::ImplicitPiType(
                Box::new(a_type.normalize(names.clone())?),
                Box::new(b_type.normalize(names)?),
            )),
            Self::Lambda(lambda) => Ok(Normal::Lambda(Box::new(lambda.normalize(names)?))),
            Self::Neutral(neutral) => Ok(Normal::Neutral(Box::new(neutral.normalize(names)?))),
            Self::PiType(a_type, b_type) => Ok(Normal::PiType(
                Box::new(a_type.normalize(names.clone())?),
                Box::new(b_type.normalize(names)?),
            )),
            Self::UniverseType(i) => Ok(Normal::UniverseType(i)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() -> Result<()> {
        let e = Expression::Application(
            Box::new(Expression::Lambda(Box::new(Lambda {
                name: Some(Name::from("x")),
                body: Expression::Lambda(Box::new(Lambda {
                    name: Some(Name::from("y")),
                    body: Expression::Variable(Name::from("x"), 0),
                })),
            }))),
            Box::new(Expression::Variable(Name::from("y"), 0)),
        );

        let names = Cow::Owned(HashSet::from([Name::from("y")]));
        let e = e.normalize(names)?;
        let nameless = e.clone().nameless(0, Cow::Owned(HashMap::new()));

        dbg!(&e, &nameless);

        Ok(())
    }

    #[test]
    fn lifting() -> Result<()> {
        let e = Expression::PiType(
            Box::new(Expression::UniverseType(0)),
            Box::new(Lambda {
                name: None,
                body: Expression::Application(
                    Box::new(Expression::Variable(Name::from("x"), 10)),
                    Box::new(Expression::UniverseType(5)),
                ),
            }),
        );

        // let e = e.lift(5)?;
        let context = Context::from([(
            Name::from("x"),
            Type::Pi(
                Box::new(Type::Universe(0)),
                Lambda {
                    name: None,
                    body: Expression::UniverseType(0),
                },
            ),
        )]);

        e.check(Type::Universe(10), Cow::Owned(context))?;

        dbg!(&e);

        Ok(())
    }

    #[test]
    fn universes() -> Result<()> {
        let e = Expression::PiType(
            box Expression::UniverseType(4),
            box Lambda {
                name: None,
                body: Expression::UniverseType(3),
            },
        );

        let r#type = e.check(Type::Hole(Hole), Cow::Owned(HashMap::new()))?;

        dbg!(&r#type);

        Ok(())
    }
}
