//! Parser and AST for Kaitai Struct expression language.

//TODO: Describe the language

peg::parser! {
  /// Contains generated parser for Kaitai Struct expression language.
  pub grammar parser() for str {
    /// Entry point for parsing expressions in `if`, `io`, `pos`, `repeat-expr`, `repeat-until`, `size`, `switch-on`, `valid.min`, `valid.max`, `valid.expr`, `value`.
    pub rule parse_single() = _ expr() _ EOS();

    /// Entry point for parsing list of expressions in function calls and parametrized types instantiations.
    pub rule parse_list() = _ expr() _ ("," _ expr() _)* EOS();

    /// Whitespace rule
    rule _() = quiet!{([' '|'\n']+ / "\\\n" / comment())*};

    rule comment() = "#" (!EOL() [_])* EOL();

    /// End-Of-Line
    rule EOL() = ['\n'] / EOS();
    /// End-Of-Stream
    rule EOS() = ![_];

    rule string()
      = "'" [x if x != '\'']* "'"
      / "\"" (ch() / escaped())* "\""
      ;

    /// Single non-escaped character in string
    rule ch() = [x if x != '\\' && x != '"'];
    /// One escaped character
    rule escaped() = "\\" (quotedChar() / quotedOct() / quotedHex());
    /// Characters that can be escaped by backslash
    rule quotedChar() = ['a'|'b'|'t'|'n'|'v'|'f'|'r'|'e'|'\''|'"'|'\\'];
    rule quotedOct()  = oct()+;
    rule quotedHex()  = ['u'] hex()*<4>;

    rule integer()
      = ['1'..='9'] ['0'..='9' | '_']*
      / "0" ['b' | 'B'] bin()+
      / "0" ['o' | 'O'] oct()+
      / "0" ['x' | 'X'] hex()+
      / "0"
      ;
    rule oct() = ['0'..='7' | '_'];
    rule bin() = ['0'..='1' | '_'];
    rule hex() = ['0'..='9' | 'a'..='f' | 'A'..='F' | '_'];

    rule digit() = ['0'..='9'];

    rule float()//TODO: allow '_' in floats
      = digit()+ exponent()   // Ex.: 4E2, 4E+2, 4e-2
      / fixed() exponent()?   // Ex.: 4.E2, .4e+2, 4.2e-0
    ;
    rule fixed()
      = digit()* "." digit()+     // Ex.: 4.2, .42
      / digit()+ "." !namePart()  // Ex.: 42.
      ;
    rule exponent() = ['e' | 'E'] ['+' | '-']? digit()+;

    //-------------------------------------------------------------------------------------------------

    rule name() = nameStart() namePart()*;
    rule nameStart() = ['a'..='z' | 'A'..='Z' | '_'];
    rule namePart()  = ['a'..='z' | 'A'..='Z' | '_' | '0'..='9'];

    rule typeName() = "::"? _ name()                 (_ "::" _ name())* (_ "[" _ "]")?;// Ex.: xyz, ::abc::def, array[]
    rule enumName() = "::"? _ name() _ "::" _ name() (_ "::" _ name())*;               // Ex.: enum::value, ::root::type::enum::value

    //-------------------------------------------------------------------------------------------------
    // Operators
    //-------------------------------------------------------------------------------------------------

    rule OR()  = "or"  !namePart();
    rule AND() = "and" !namePart();
    rule NOT() = "not" !namePart();

    rule expr()     = or_test() (_ "?" _ expr() _ ":" _ expr())?;
    rule or_test()  = and_test() (_ OR()  _ and_test())*;
    rule and_test() = not_test() (_ AND() _ not_test())*;

    rule not_test()
      = NOT() _ not_test()
      / or_expr() (_ comp_op() _ or_expr())?
      ;

    rule comp_op()
      = "=="
      / "!="
      / "<="
      / ">="
      / "<"
      / ">"
      ;

    rule or_expr()    = xor_expr()   (_ "|"           _ xor_expr()  )*;
    rule xor_expr()   = and_expr()   (_ "^"           _ and_expr()  )*;
    rule and_expr()   = shift_expr() (_ "&"           _ shift_expr())*;
    rule shift_expr() = arith_expr() (_ ("<<" / ">>") _ arith_expr())*;
    rule arith_expr() = term()       (_ ['+'|'-']     _ term()      )*;
    rule term()       = factor()     (_ ['*'|'/'|'%'] _ factor()    )*;

    rule factor()
      = "+" _ factor()
      / "-" _ factor()
      / "~" _ factor()
      / atom() (_ postfix())*
      ;

    rule atom()
      = "(" _ expr() _ ")"
      / "[" _ list()? _ "]"
      / "sizeof" _ "<" _ typeName() _ ">"
      / "bitsizeof" _ "<" _ typeName() _ ">"
      / (string() _)+
      / enumName()
      / name()
      / float()
      / integer()
      ;

    rule postfix()
      = "(" _ args() _ ")"                  // call
      / "[" _ expr() _ "]"                  // indexing
      / "." _ "as" _ "<" _ typeName() _ ">" // type cast
      / "." _ name()                        // attribute access
      ;

    rule list() = expr() (_ "," _ expr())* _ ","?;
    rule args() = expr() ** (_ ",");
  }
}

#[cfg(test)]
mod parse {
  /// Wrapper, for use with https://github.com/fasterthanlime/pegviz
  fn parse_single(input: &str) -> Result<(), peg::error::ParseError<peg::str::LineCol>> {
    println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
    let result = super::parser::parse_single(input);
    println!("[PEG_TRACE_STOP]");
    result
  }

  mod comments {
    use super::*;

    #[test]
    fn empty() {
      assert_eq!(parse_single("#\n123"), Ok(()));
    }
    #[test]
    fn following() {
      assert_eq!(parse_single("123# comment"), Ok(()));
      assert_eq!(parse_single("123\n# comment"), Ok(()));
    }
    #[test]
    fn leading() {
      assert_eq!(parse_single("# comment\n123"), Ok(()));
    }
    #[test]
    fn multi_line() {
      assert_eq!(parse_single(r#"
      1
      # multi-line
      # comment
      +
      # and yet
      # another
      2
      "#), Ok(()));
    }
  }

  mod dec {
    use super::*;

    #[test]
    fn positive() {
      assert_eq!(parse_single("123"), Ok(()));
    }

    #[test]
    fn negative() {
      assert_eq!(parse_single("-456"), Ok(()));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("100_500"), Ok(()));
      assert_eq!(parse_single("100500_"), Ok(()));
    }
  }

  mod hex {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0x1234"), Ok(()));
      assert_eq!(parse_single("0X1234"), Ok(()));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0x_1234"), Ok(()));
      assert_eq!(parse_single("0x12_34"), Ok(()));
      assert_eq!(parse_single("0x1234_"), Ok(()));

      assert_eq!(parse_single("0X_1234"), Ok(()));
      assert_eq!(parse_single("0X12_34"), Ok(()));
      assert_eq!(parse_single("0X1234_"), Ok(()));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0x_").is_err());
      assert!(parse_single("0X_").is_err());
    }
  }

  mod oct {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0o644"), Ok(()));
      assert_eq!(parse_single("0O644"), Ok(()));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0o_0644"), Ok(()));
      assert_eq!(parse_single("0o06_44"), Ok(()));
      assert_eq!(parse_single("0o0644_"), Ok(()));

      assert_eq!(parse_single("0O_0644"), Ok(()));
      assert_eq!(parse_single("0O06_44"), Ok(()));
      assert_eq!(parse_single("0O0644_"), Ok(()));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0o_").is_err());
      assert!(parse_single("0O_").is_err());
    }
  }

  mod bin {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0b10101010"), Ok(()));
      assert_eq!(parse_single("0B10101010"), Ok(()));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0b_1010_1010"), Ok(()));
      assert_eq!(parse_single("0b1010_1_010"), Ok(()));
      assert_eq!(parse_single("0b1010_1010_"), Ok(()));

      assert_eq!(parse_single("0B_1010_1010"), Ok(()));
      assert_eq!(parse_single("0B1010_1_010"), Ok(()));
      assert_eq!(parse_single("0B1010_1010_"), Ok(()));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0b_").is_err());
      assert!(parse_single("0B_").is_err());
    }
  }

  mod float {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("1.2345"), Ok(()));
    }

    #[test]
    fn with_signless_exponent() {
      assert_eq!(parse_single("123e4"), Ok(()));
      assert_eq!(parse_single("123E4"), Ok(()));
    }

    #[test]
    fn with_positive_exponent() {
      assert_eq!(parse_single("123e+4"), Ok(()));
      assert_eq!(parse_single("123E+4"), Ok(()));
    }

    #[test]
    fn with_negative_exponent() {
      assert_eq!(parse_single("123e-7"), Ok(()));
      assert_eq!(parse_single("123E-7"), Ok(()));
    }

    #[test]
    fn non_integral_part_with_signless_exponent() {
      assert_eq!(parse_single("1.2345e7"), Ok(()));
      assert_eq!(parse_single("1.2345E7"), Ok(()));
    }

    #[test]
    fn non_integral_part_with_positive_exponent() {
      assert_eq!(parse_single("123.45e+7"), Ok(()));
      assert_eq!(parse_single("123.45E+7"), Ok(()));
    }

    #[test]
    fn non_integral_part_with_negative_exponent() {
      assert_eq!(parse_single("123.45e-7"), Ok(()));
      assert_eq!(parse_single("123.45E-7"), Ok(()));
    }
  }

  mod string {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("\"abc\""), Ok(()));
    }

    #[test]
    fn interpolated_with_newline() {
      assert_eq!(parse_single("\"abc\\ndef\""), Ok(()));
    }

    #[test]
    fn non_interpolated_with_newline() {
      assert_eq!(parse_single("'abc\\ndef'"), Ok(()));
    }

    #[test]
    fn interpolated_with_zero_char() {
      assert_eq!(parse_single("\"abc\\0def\""), Ok(()));
    }

    #[test]
    fn non_interpolated_with_zero_char() {
      assert_eq!(parse_single("'abc\\0def'"), Ok(()));
    }

    #[test]
    fn interpolated_with_octal_char() {
      assert_eq!(parse_single("\"abc\\75def\""), Ok(()));
    }

    #[test]
    fn interpolated_with_hex_unicode_char() {
      assert_eq!(parse_single("\"abc\\u21bbdef\""), Ok(()));
    }

    mod concat {
      use super::*;

      #[test]
      fn interpolated_strings() {
        assert_eq!(parse_single(r#""abc""def""#), Ok(()));
      }

      #[test]
      fn non_interpolated_strings() {
        assert_eq!(parse_single(r#"'abc''def'"#), Ok(()));
      }

      #[test]
      fn mixed_strings() {
        assert_eq!(parse_single(r#""abc"'def'"#), Ok(()));
        assert_eq!(parse_single(r#"'abc'"def""#), Ok(()));
      }
    }
  }

  mod expr {
    use super::*;

    #[test]
    fn unary() {
      assert_eq!(parse_single("++1"), Ok(()));
      assert_eq!(parse_single("--1"), Ok(()));
      assert_eq!(parse_single("~~1"), Ok(()));
      assert_eq!(parse_single("not not 1"), Ok(()));
    }

    #[test]
    fn binary() {
      assert_eq!(parse_single("1 + 2 + 3"), Ok(()));
      assert_eq!(parse_single("1 - 2 - 3"), Ok(()));
      assert_eq!(parse_single("1 * 2 * 3"), Ok(()));
      assert_eq!(parse_single("1 / 2 / 3"), Ok(()));
      assert_eq!(parse_single("1 % 2 % 3"), Ok(()));
      assert_eq!(parse_single("1 | 2 | 3"), Ok(()));
      assert_eq!(parse_single("1 & 2 & 3"), Ok(()));
      assert_eq!(parse_single("1 ^ 2 ^ 3"), Ok(()));
      assert_eq!(parse_single("1 << 2 << 3"), Ok(()));
      assert_eq!(parse_single("1 >> 2 >> 3"), Ok(()));
    }

    #[test]
    fn ternary() {
      assert_eq!(parse_single("x ? \"foo\" : \"bar\""), Ok(()));
    }

    #[test]
    fn arith() {
      assert_eq!(parse_single("(1 + 2) / (7 * 8)"), Ok(()));
    }

    #[test]
    fn comparison() {
      assert_eq!(parse_single("1 == 2"), Ok(()));
      assert_eq!(parse_single("1 != 2"), Ok(()));
      assert_eq!(parse_single("1 <= 2"), Ok(()));
      assert_eq!(parse_single("1 >= 2"), Ok(()));
      assert_eq!(parse_single("1 < 2"), Ok(()));
      assert_eq!(parse_single("1 > 2"), Ok(()));
    }

    #[test]
    fn indexing() {
      assert_eq!(parse_single("a[42]"), Ok(()));
      assert_eq!(parse_single("a[42 - 2]"), Ok(()));
    }
  }

  mod enums {
    use super::*;

    #[test]
    fn value() {
      assert_eq!(parse_single("port::http"), Ok(()));
    }

    #[test]
    fn with_type() {
      assert_eq!(parse_single("some_type::port::http"), Ok(()));
      assert_eq!(parse_single("parent_type::some_type::port::http"), Ok(()));
    }

    #[test]
    fn with_abs_path() {
      assert_eq!(parse_single("::port::http"), Ok(()));
      assert_eq!(parse_single("::parent_type::child_type::port::http"), Ok(()));
    }
  }

  #[test]
  fn complex() {
    assert_eq!(parse_single("port::http.to_i + 8000 == 8080"), Ok(()));
  }

  #[test]
  fn list() {
    assert_eq!(parse_single("[1, 2, 0x1234]"), Ok(()));
  }

  mod literals {
    use super::*;

    #[test]
    fn boolean() {
      assert_eq!(parse_single("true"), Ok(()));
      assert_eq!(parse_single("false"), Ok(()));
    }

    #[test]
    fn identifiers() {
      assert_eq!(parse_single("truex"), Ok(()));
      assert_eq!(parse_single("true1"), Ok(()));

      assert_eq!(parse_single("falsex"), Ok(()));
      assert_eq!(parse_single("false1"), Ok(()));

      assert_eq!(parse_single("notx"), Ok(()));
      assert_eq!(parse_single("not1"), Ok(()));

      assert_eq!(parse_single("andx"), Ok(()));
      assert_eq!(parse_single("and1"), Ok(()));

      assert_eq!(parse_single("orx"), Ok(()));
      assert_eq!(parse_single("or1"), Ok(()));
    }
  }

  mod casts {
    use super::*;

    #[test]
    fn int_as_type() {
      assert_eq!(parse_single("123.as<u4>"), Ok(()));
    }
    #[test]
    fn expr_as_type() {
      assert_eq!(parse_single("(123).as<u4>"), Ok(()));
    }
    #[test]
    fn str_as_type() {
      assert_eq!(parse_single("\"str\".as<x>"), Ok(()));
    }
    #[test]
    fn var_as_type() {
      assert_eq!(parse_single("foo.as<x>"), Ok(()));
    }
    #[test]
    fn as_type_with_spaces() {
      assert_eq!(parse_single("foo.as < x  >  "), Ok(()));
    }

    #[test]
    fn as_enum() {
      assert_eq!(parse_single("foo.as<bar::baz>"), Ok(()));
      assert_eq!(parse_single("foo.as<::bar::baz>"), Ok(()));
    }

    #[test]
    fn as_array() {
      assert_eq!(parse_single("foo.as<bar[]>"), Ok(()));
      assert_eq!(parse_single("foo.as<::bar::baz[]>"), Ok(()));
    }

    #[test]
    fn attribute() {
      assert_eq!(parse_single("foo.as"), Ok(()));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("foo.as<x"), Ok(()));
    }
  }

  mod sizeof_ {
    use super::*;

    #[test]
    fn of_type() {
      assert_eq!(parse_single("sizeof<foo>"), Ok(()));
    }

    #[test]
    fn of_enum() {
      assert_eq!(parse_single("sizeof<foo::bar>"), Ok(()));
      assert_eq!(parse_single("sizeof<::foo::bar>"), Ok(()));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("sizeof<foo"), Ok(()));
    }
  }

  mod bitsizeof_ {
    use super::*;

    #[test]
    fn of_type() {
      assert_eq!(parse_single("bitsizeof<foo>"), Ok(()));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("bitsizeof<foo"), Ok(()));
    }
  }

  mod attrs {
    use super::*;

    #[test]
    fn access() {
      assert_eq!(parse_single("123.to_s"), Ok(()));
      assert_eq!(parse_single("foo.bar"), Ok(()));
    }

    #[test]
    fn int_not_float() {
      assert_eq!(parse_single("123.e"), Ok(()));
      assert_eq!(parse_single("123.E"), Ok(()));
      assert_eq!(parse_single("123._"), Ok(()));
    }

    #[test]
    fn float_and_access() {
      assert_eq!(parse_single("123.4.to_s"), Ok(()));
    }
  }
}
