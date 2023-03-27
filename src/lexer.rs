#[derive(Debug)]
pub enum Token {
	Identifier(String),
	Lambda,
	Forall,
	Kind,
	Lift,
	LeftParen,
	RightParen,
	LeftBrace,
	RightBrace,
	Assignment,
	HasType,
	CheckEquality,
	EndStatement,
	ReturnFromBlock,
}

fn identifier_start(c: char) -> bool {
	matches!(c, 'a' ..= 'z' | 'A' ..= 'Z' | '_')
}

fn identifier_continue(c: char) -> bool {
	matches!(c, 'a' ..= 'z' | 'A' ..= 'Z' | '0' ..= '9' | '_')
}

fn is_whitespace(c: char) -> bool {
	matches!(c, ' ' | '\t' | '\n')
}

#[derive(Debug)]
pub enum Error {
	MalformedComment,
	InvalidCharacter,
}

pub fn lex(input: &str) -> Result<Vec<Token>, Error> {
	let mut out = Vec::new();

	let mut iterator = input.chars().peekable();

	while let Some(char) = iterator.next() {
		if identifier_start(char) {
			let mut identifier = String::new();
			identifier.push(char);

			while let Some(&char) = iterator.peek() {
				if !identifier_continue(char) {
					break;
				}

				iterator.next();
				identifier.push(char);
			}

			out.push(Token::Identifier(identifier));

			continue;
		}

		if is_whitespace(char) {
			continue;
		}

		if char == '/' {
			if iterator.peek() != Some(&'/') {
				return Err(Error::MalformedComment);
			}

			iterator.next();

			loop {
				let maybe_char = iterator.next();

				match maybe_char {
					None | Some('\n') => break,
					_ => {},
				}
			}

			continue;
		}

		out.push(match char {
			'!' => Token::Lambda,
			'@' => Token::Forall,
			'#' => Token::Kind,
			'\'' => Token::Lift,
			'(' => Token::LeftParen,
			')' => Token::RightParen,
			'{' => Token::LeftBrace,
			'}' => Token::RightBrace,
			'=' => Token::Assignment,
			':' => Token::HasType,
			'~' => Token::CheckEquality,
			';' => Token::EndStatement,
			'%' => Token::ReturnFromBlock,
			_ => return Err(Error::InvalidCharacter),
		});
	}

	Ok(out)
}
