use aterms::base::{parse_term_from_file, parse_term_from_string};
use tecs::{parse_tecs_file, Interpreter};

#[test]
fn test_1() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File()").unwrap();
    let res = interp.run(term, "FileOk_1");

    assert!(res.is_ok());
}

#[test]
fn test_2() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File(1, 2)").unwrap();

    let res = interp.run(term.clone(), "FileOk_2");
    assert!(res.is_ok());

    let res = interp.run(term, "FileOk_1");
    assert!(res.is_err());
}

#[test]
fn test_3() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File()").unwrap();

    let res = interp.run(term.clone(), "FileOk_3");
    assert!(res.is_ok());
}

#[test]
fn test_4() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File()").unwrap();

    let res = interp.run(term.clone(), "FileOk_4");
    assert!(res.is_ok());
}

#[test]
fn test_5() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File(Decl(\"a\"), Ref(\"a\"))").unwrap();

    let res = interp.run(term.clone(), "FileOk_5");
    assert!(res.is_ok());
}

#[test]
fn test_6() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File(Decl(\"a\"), [Ref(\"a\"), Ref(\"a\")])").unwrap();

    let res = interp.run(term.clone(), "FileOk_6");
    assert!(res.is_ok());
}

#[test]
fn test_7() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File(Decl(\"a\"), Decl(\"a\"))").unwrap();
    let term2 = parse_term_from_string("File(Decl(\"a\"), Decl(\"b\"))").unwrap();

    let res = interp.run(term.clone(), "FileOk_7");
    assert!(res.is_err());

    let res = interp.run(term2.clone(), "FileOk_7");
    assert!(res.is_ok());
}

#[test]
fn test_8() {
    let interp = Interpreter::new("tests/test.tcs");
    let term = parse_term_from_string("File(Int(\"1\"), Int(\"1\"))").unwrap();

    let res = interp.run(term.clone(), "FileOk_8");
    assert!(res.is_ok());
}

#[test]
fn test_b() {
    let interp = Interpreter::new("tests/test_with_ters.tcs");
    let term = parse_term_from_string(r#"File(Decl("a", Int()), Ref("a", Int()))"#).unwrap();
    let res = interp.run(term.clone(), "FileOk");
    assert!(res.is_ok());
}
