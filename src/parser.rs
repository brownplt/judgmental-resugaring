use combine::*;
use combine::char::{char, letter, lower, upper, space};



pub fn parse<I : Stream<Item = char>>(input: I) -> ParseResult<String, I> {
    (many(letter()), char('\n'), eof()).map(|(word, _, _)| { word })
        .parse_stream(input)
}

fn lid<I : Stream<Item = char>>(input: I) -> ParseResult<String, I> {
    (lower(), many(letter())).map(|(x, y): (char, String)| {
        x.to_string() + &y
    }).parse_stream(input)
}    

fn uid<I : Stream<Item = char>>(input: I) -> ParseResult<String, I> {
    (upper(), many(letter())).map(|(x, y): (char, String)| {
        x.to_string() + &y
    }).parse_stream(input)
}

fn ws<I : Stream<Item = char>>(input: I) -> ParseResult<(), I> {
    many(space()).map(|_: String| ()).parse_stream(input)
}

type Var = String;

struct MVar {
    name: String,
    id: usize
}

enum Context {
    CVal(String),
    CHole(MVar),
    CVar(Var),
    CStx(String, Vec<Context>)
}
use self::Context::*;

fn context<I : Stream<Item = char>>(input: I) -> ParseResult<Context, I> {
    let mut val = (char('"'), many(satisfy(|c| c != '"')), char('"'))
        .map(|(_, x, _)| CVal(x));
    let mut stx = (char('('), ws, uid, ws, context, ws, char(')')) /* */
        .map(|(_, _, head, _, body, _, _)| CStx(head, vec!(body)));
    val
        .or(stx)
        .parse_stream(input)
}

/*
context:
  | LITERAL {
    let s = $1 in
    Term.CVal(String.sub s 1 (String.length(s) - 2))
  }
  | LID {
    Term.CHole(Term.new_mvar($1))
  }
  | UID {
    Term.CVar($1)
  }
  | LPAREN UID contexts RPAREN {
    Term.CStx($2, $3)
  }
;
contexts:
  |                  { [] }
  | context contexts { $1 :: $2 }
;
*/


#[cfg(test)]
mod parser_tests {
    use combine::*;
    use super::*;
    
    #[test]
    fn it_works() {
        let result = parse(State::new("hello\n world"));
        match result {
            Ok(_)    => (),
            Err(err) => {
                println!("{}", err.as_ref());
            }
        }
    }
}
