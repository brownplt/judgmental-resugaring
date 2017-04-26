use nom::IResult;

named!(pub parens, delimited!(tag_s!("("), is_not_s!(")"), tag_s!(")")));

pub fn go() {
    match parens(b"ok") {
        IResult::Error(err) => println!("? {}", err),
        IResult::Done(i, o) => (),
        IResult::Incomplete(n) => println!("? {:?}", n)
    }
}
