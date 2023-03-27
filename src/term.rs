use std::cmp::Ordering;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum TermInner {
	Kind(usize),
	Variable(usize),
	Lambda {input: Term, body: Term},
	Forall {input: Term, body: Term},
	Application {left: Term, right: Term},
}

pub type Term = Rc<TermInner>;

#[derive(Debug)]
enum ContextStack<'a> {
	Level {
		value: Term,
		next: &'a ContextStack<'a>,
	},
	End,
}

#[derive(Debug)]
pub enum Error {
	VariableUndefined,
	InputFailedToBeKind,
	BodyFailedToBeKind,
	CannotCallNonLambda,
	TypeMismatch,
}

pub fn evaluate(term: &Term) -> Result<(Term, Term), Error> {
	evaluate_helper(term, &ContextStack::End)
}

fn evaluate_helper(
	term: &Term,
	stack: &ContextStack<'_>,
) -> Result<(Term, Term), Error> {
	Ok(match &**term {
		&TermInner::Kind(x) => (
			term.clone(),
			Rc::new(TermInner::Kind(x + 1)),
		),
		&TermInner::Variable(x) => {
			let mut stack = stack;

			for _ in 0 .. x {
				stack = match stack {
					ContextStack::Level {next, ..} => next,
					ContextStack::End => return Err(Error::VariableUndefined),
				};
			}

			let term_type = match stack {
				ContextStack::Level {value, ..} => value,
				ContextStack::End => return Err(Error::VariableUndefined),
			};

			(term.clone(), abstract_term_by(term_type, x + 1))
		},
		TermInner::Lambda {input, body} => {
			let (input, input_kind) = evaluate_helper(input, stack)?;

			if !is_kind(&input_kind) {
				return Err(Error::InputFailedToBeKind);
			}

			let stack = &ContextStack::Level {
				value: input.clone(),
				next: stack,
			};

			let (body, body_type) = evaluate_helper(body, stack)?;

			(
				Rc::new(TermInner::Lambda {input: input.clone(), body}),
				Rc::new(TermInner::Forall {input, body: body_type}),
			)
		},
		TermInner::Forall {input, body} => {
			let (input, input_kind) = evaluate_helper(input, stack)?;

			if !is_kind(&input_kind) {
				return Err(Error::InputFailedToBeKind);
			}

			let stack = &ContextStack::Level {
				value: input.clone(),
				next: stack,
			};

			let (body, body_kind) = evaluate_helper(body, stack)?;

			if !is_kind(&body_kind) {
				return Err(Error::BodyFailedToBeKind);
			}

			(
				Rc::new(TermInner::Forall {input, body}),
				body_kind,
			)
		},
		TermInner::Application {left, right} => {
			let (left, left_type) = evaluate_helper(left, stack)?;

			let (left_expects, left_provides) = match &*left_type {
				TermInner::Forall {input, body} => (input, body),
				_ => return Err(Error::CannotCallNonLambda),
			};

			let (right, right_type) = evaluate_helper(right, stack)?;

			if left_expects != &right_type {
				return Err(Error::TypeMismatch);
			}

			let value_type = substitute(&left_provides, &right);

			let value = match &*left {
				TermInner::Lambda {body: left_body, ..} => substitute(
					&left_body,
					&right,
				),
				_ => term.clone(),
			};

			(value, value_type)
		},
	})
}

fn is_kind(term: &Term) -> bool {
	matches!(&**term, TermInner::Kind(_))
}

fn substitute(base: &Term, replacement: &Term) -> Term {
	substitute_helper(base, replacement, 0)
}

fn substitute_helper(
	base: &Term,
	replacement: &Term,
	level: usize,
) -> Term {
	match &**base {
		&TermInner::Kind(x) => Rc::new(TermInner::Kind(x)),
		&TermInner::Variable(x) => match x.cmp(&level) {
			Ordering::Equal => abstract_term_by(replacement, level),
			Ordering::Less => Rc::new(TermInner::Variable(x)),
			Ordering::Greater => Rc::new(TermInner::Variable(x - 1)),
		},
		TermInner::Lambda {input, body} => Rc::new(TermInner::Lambda {
			input: substitute_helper(input, replacement, level),
			body: substitute_helper(body, replacement, level + 1),
		}),
		TermInner::Forall {input, body} => Rc::new(TermInner::Forall {
			input: substitute_helper(input, replacement, level),
			body: substitute_helper(body, replacement, level + 1),
		}),
		TermInner::Application {left, right} => {
			let left = substitute_helper(left, replacement, level);
			let right = substitute_helper(right, replacement, level);

			match &*left {
				TermInner::Lambda {body, ..} => substitute(body, &right),
				_ => Rc::new(TermInner::Application {left, right}),
			}
		},
	}
}

fn abstract_term_by(term: &Term, amount: usize) -> Term {
	if amount == 0 {
		return term.clone();
	}

	abstract_term_by_helper(term, amount, 0)
}

fn abstract_term_by_helper(term: &Term, amount: usize, level: usize) -> Term {
	Rc::new(match &**term {
		&TermInner::Kind(x) => TermInner::Kind(x),
		&TermInner::Variable(x) => TermInner::Variable(if x >= level {
			x + amount
		} else {
			x
		}),
		TermInner::Lambda {input, body} => TermInner::Lambda {
			input: abstract_term_by_helper(input, amount, level),
			body: abstract_term_by_helper(body, amount, level + 1),
		},
		TermInner::Forall {input, body} => TermInner::Forall {
			input: abstract_term_by_helper(input, amount, level),
			body: abstract_term_by_helper(body, amount, level + 1),
		},
		TermInner::Application {left, right} => TermInner::Application {
			left: abstract_term_by_helper(left, amount, level),
			right: abstract_term_by_helper(right, amount, level),
		},
	})
}

pub fn lift_by(term: &Term, amount: usize) -> Term {
	match &**term {
		&TermInner::Kind(x) => Rc::new(TermInner::Kind(x + amount)),
		&TermInner::Variable(_) => term.clone(),
		TermInner::Lambda {input, body} => Rc::new(TermInner::Lambda {
			input: lift_by(input, amount),
			body: lift_by(body, amount),
		}),
		TermInner::Forall {input, body} => Rc::new(TermInner::Forall {
			input: lift_by(input, amount),
			body: lift_by(body, amount),
		}),
		TermInner::Application {left, right} => Rc::new(TermInner::Application {
			left: lift_by(left, amount),
			right: lift_by(right, amount),
		}),
	}
}

#[cfg(test)]
mod test {
	use super::*;

	// once we have proper parsing, these tests can become a lot nicer-looking
	// because right now constructing the correct terms is horrifying

	fn kind(level: usize) -> Term {
		Rc::new(TermInner::Kind(level))
	}

	fn variable(level: usize) -> Term {
		Rc::new(TermInner::Variable(level))
	}

	fn lambda(input: &Term, body: &Term) -> Term {
		Rc::new(TermInner::Lambda {input: input.clone(), body: body.clone()})
	}

	fn forall(input: &Term, body: &Term) -> Term {
		Rc::new(TermInner::Forall {input: input.clone(), body: body.clone()})
	}

	fn apply(left: &Term, right: &Term) -> Term {
		Rc::new(TermInner::Application {
			left: left.clone(),
			right: right.clone(),
		})
	}

	#[test]
	fn test_id_and_unit() {
		let id = lambda(&kind(0), &lambda(&variable(0), &variable(0)));
		let unit = forall(&kind(0), &forall(&variable(0), &variable(1)));

		let (should_be_id, should_be_unit) = evaluate(&id).unwrap();

		assert_eq!(should_be_id, id);
		assert_eq!(should_be_unit, unit);

		let (should_be_unit, should_be_kind_0) = evaluate(&unit).unwrap();

		assert_eq!(should_be_unit, unit);
		assert_eq!(should_be_kind_0, kind(0));

		let (should_be_id, should_be_unit) = evaluate(
			&apply(&apply(&id, &unit), &id),
		).unwrap();

		assert_eq!(should_be_id, id);
		assert_eq!(should_be_unit, unit);
	}

	#[test]
	fn test_int() {
		fn make_number(number: usize) -> Term {
			let mut body = variable(0);

			for _ in 0 .. number {
				body = apply(&variable(1), &body);
			}

			lambda(
				&kind(0),
				&lambda(
					&forall(&variable(0), &variable(1)),
					&lambda(
						&variable(1),
						&body,
					),
				),
			)
		}

		let int = forall(
			&kind(0),
			&forall(
				&forall(&variable(0), &variable(1)),
				&forall(
					&variable(1),
					&variable(2),
				),
			),
		);

		let (should_be_int, should_be_kind_0) = evaluate(&int).unwrap();

		assert_eq!(should_be_int, int);
		assert_eq!(should_be_kind_0, kind(0));

		for i in 0 .. 10 {
			let number = make_number(i);

			let (should_be_number, should_be_int) = evaluate(&number).unwrap();

			assert_eq!(should_be_number, number);
			assert_eq!(should_be_int, int);
		}

		let succ = lambda(
			&int,
			&lambda(
				&kind(0),
				&lambda(
					&forall(&variable(0), &variable(1)),
					&lambda(
						&variable(1),
						&apply(
							&variable(1),
							&apply(
								&apply(
									&apply(
										&variable(3),
										&variable(2),
									),
									&variable(1),
								),
								&variable(0),
							),
						),
					),
				),
			),
		);

		let (should_be_succ, should_be_int_to_int) = evaluate(&succ).unwrap();

		assert_eq!(should_be_succ, succ);
		assert_eq!(should_be_int_to_int, forall(&int, &int));

		let (should_be_20, should_be_int) = evaluate(
			&apply(
				&apply(
					&apply(
						&make_number(10),
						&int,
					),
					&succ,
				),
				&make_number(10),
			),
		).unwrap();

		assert_eq!(should_be_20, make_number(20));
		assert_eq!(should_be_int, int);

		let (should_be_100, should_be_int) = evaluate(
			&apply(
				&apply(
					&apply(
						&make_number(10),
						&int,
					),
					&apply(
						&apply(
							&make_number(10),
							&int,
						),
						&succ,
					),
				),
				&make_number(0),
			),
		).unwrap();

		assert_eq!(should_be_100, make_number(100));
		assert_eq!(should_be_int, int);
	}
}
