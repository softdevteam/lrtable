use std::fmt;

extern crate regex;
use self::regex::Regex;

type YaccResult<T> = Result<T, YaccError>;

use grammar::{AssocKind, Precedence};
use grammar_ast::{GrammarAST, Symbol};

pub struct YaccParser {
    src: String,
    newlines: Vec<usize>,
    grammar: GrammarAST
}

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum YaccErrorKind {
    IllegalName,
    IllegalString,
    IncompleteRule,
    MissingColon,
    PrematureEnd,
    ProgramsNotSupported,
    UnknownDeclaration,
    DuplicatePrecedence
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct YaccError {
    pub kind: YaccErrorKind,
    line: usize,
    col: usize
}

impl fmt::Display for YaccError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s;
        match self.kind {
            YaccErrorKind::IllegalName          => s = "Illegal name",
            YaccErrorKind::IllegalString        => s = "Illegal string",
            YaccErrorKind::IncompleteRule       => s = "Incomplete rule",
            YaccErrorKind::MissingColon         => s = "Missing colon",
            YaccErrorKind::PrematureEnd         => s = "File ends prematurely",
            YaccErrorKind::ProgramsNotSupported => s = "Programs not currently supported",
            YaccErrorKind::UnknownDeclaration   => s = "Unknown declaration",
            YaccErrorKind::DuplicatePrecedence  => s = "Token already has a precedence"
        }
        write!(f, "{} at line {} column {}", s, self.line, self.col)
    }
}

lazy_static! {
    static ref RE_NAME: Regex = {
        Regex::new(r"^[a-zA-Z_.][a-zA-Z0-9_.]*").unwrap()
    };
    static ref RE_TERMINAL: Regex = {
        Regex::new("^(?:(\".+?\")|('.+?')|([a-zA-Z_][a-zA-Z_0-9]*))").unwrap()
    };
}

/// The actual parser is intended to be entirely opaque from outside users.
impl YaccParser {
    fn new(src: String) -> YaccParser {
        YaccParser {
            src     : src,
            newlines: vec![0],
            grammar : GrammarAST::new()
        }
    }

    fn mk_error(&self, k: YaccErrorKind, off: usize) -> YaccError {
        let (line, col) = self.off_to_line_col(off);
        YaccError{kind: k, line: line, col: col}
    }

    fn off_to_line_col(&self, off: usize) -> (usize, usize) {
        if off == self.src.len() {
            let line_off = *self.newlines.iter().last().unwrap();
            return (self.newlines.len(), self.src[line_off..].chars().count() + 1);
        }
        let (line_m1, &line_off) = self.newlines.iter()
                                                .enumerate()
                                                .rev()
                                                .find(|&(_, &line_off)| line_off <= off)
                                                .unwrap();
        let c_off = self.src[line_off..]
                        .char_indices()
                        .position(|(c_off, _)| c_off == off - line_off)
                        .unwrap();
        return (line_m1 + 1, c_off + 1);
    }

    fn parse(&mut self) -> YaccResult<usize> {
        // We pass around an index into the *bytes* of self.src. We guarantee that at all times
        // this points to the beginning of a UTF-8 character (since multibyte characters exist, not
        // every byte within the string is also a valid character).
        let mut i = try!(self.parse_declarations(0));
        i = try!(self.parse_rules(i));
        // We don't currently support the programs part of a specification. One day we might...
        match self.lookahead_is("%%", i) {
            Some(j) => {
                if try!(self.parse_ws(j)) == self.src.len() { Ok(i) }
                else {
                    Err(self.mk_error(YaccErrorKind::ProgramsNotSupported, i))
                }
            }
            None    => Ok(i)
        }
    }

    fn parse_declarations(&mut self, mut i: usize) -> YaccResult<usize> {
        i = try!(self.parse_ws(i));
        let mut prec_level  = 0;
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() { return Ok(i); }
            if let Some(j) = self.lookahead_is("%token", i) {
                i = try!(self.parse_ws(j));
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() { break; }
                    let (j, n) = try!(self.parse_terminal(i));
                    self.grammar.tokens.insert(n);
                    i = try!(self.parse_ws(j));
                }
            }
            else if let Some(j) = self.lookahead_is("%start", i) {
                i = try!(self.parse_ws(j));
                let (j, n) = try!(self.parse_name(i));
                self.grammar.start = Some(n);
                i = try!(self.parse_ws(j));
            }
            else {
                let k;
                let kind;
                if let Some(j) = self.lookahead_is("%left", i) {
                    kind = AssocKind::Left;
                    k = j;
                } else if let Some(j) = self.lookahead_is("%right", i) {
                    kind = AssocKind::Right;
                    k = j;
                } else if let Some(j) = self.lookahead_is("%nonassoc", i) {
                    kind = AssocKind::Nonassoc;
                    k = j;
                } else {
                    return Err(self.mk_error(YaccErrorKind::UnknownDeclaration, i));
                }

                i = try!(self.parse_ws(k));
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() { break; }
                    let (j, n) = try!(self.parse_terminal(i));
                    if self.grammar.precs.contains_key(&n) {
                        return Err(self.mk_error(YaccErrorKind::DuplicatePrecedence, i));
                    }
                    let prec = Precedence{level: prec_level, kind: kind};
                    self.grammar.precs.insert(n, prec);
                    i = try!(self.parse_ws(j));
                }
                prec_level += 1;
            }
        }
        Err(self.mk_error(YaccErrorKind::PrematureEnd, i - 1))
    }

    fn parse_rules(&mut self, mut i: usize) -> YaccResult<usize> {
        // self.parse_declarations should have left the input at '%%'
        match self.lookahead_is("%%", i) {
            Some(j) => i = j,
            None    => panic!("Internal error.")
        }
        i = try!(self.parse_ws(i));
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() { break; }
            i = try!(self.parse_rule(i));
            i = try!(self.parse_ws(i));
        }
        Ok(i)
    }

    fn parse_rule(&mut self, mut i: usize) -> YaccResult<usize> {
        let (j, rn) = try!(self.parse_name(i));
        i = try!(self.parse_ws(j));
        match self.lookahead_is(":", i) {
            Some(j) => i = j,
            None    => {
                return Err(self.mk_error(YaccErrorKind::MissingColon, i));
            }
        }
        let mut syms = Vec::new();
        i = try!(self.parse_ws(i));
        while i < self.src.len() {
            if let Some(j) = self.lookahead_is("|", i) {
                self.grammar.add_rule(rn.clone(), syms);
                syms = Vec::new();
                i = try!(self.parse_ws(j));
                continue;
            }
            else if let Some(j) = self.lookahead_is(";", i) {
                self.grammar.add_rule(rn.clone(), syms);
                return Ok(j);
            }

            if self.lookahead_is("\"", i).is_some()
              || self.lookahead_is("'", i).is_some() {
                let (j, sym) = try!(self.parse_terminal(i));
                i = try!(self.parse_ws(j));
                self.grammar.tokens.insert(sym.clone());
                syms.push(Symbol::Terminal(sym));
            }
            else {
                let (j, sym) = try!(self.parse_terminal(i));
                if self.grammar.tokens.contains(&sym) {
                    syms.push(Symbol::Terminal(sym));
                } else {
                    syms.push(Symbol::Nonterminal(sym));
                }
                i = j;
            }
            i = try!(self.parse_ws(i));
        }
        Err(self.mk_error(YaccErrorKind::IncompleteRule, i))
    }

    fn parse_name(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_NAME.find(&self.src[i..]) {
            Some((s, e)) => {
                assert!(s == 0);
                Ok((i + e, self.src[i..i + e].to_string()))
            },
            None         => {
                Err(self.mk_error(YaccErrorKind::IllegalName, i))
            }
        }
    }

    fn parse_terminal(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_TERMINAL.find(&self.src[i..]) {
            Some((s, e)) => {
                assert!(s == 0 && e > 0);
                match self.src[i..].chars().next().unwrap() {
                    '"' | '\'' => {
                        assert!('"'.len_utf8() == 1 && '\''.len_utf8() == 1);
                        Ok((i + e, self.src[i + 1..i + e - 1].to_string()))
                    },
                    _ =>  Ok((i + e, self.src[i..i + e].to_string()))
                }
            },
            None => {
                Err(self.mk_error(YaccErrorKind::IllegalString, i))
            }
        }
    }

    fn parse_ws(&mut self, i: usize) -> YaccResult<usize> {
        let mut j = i;
        for c in self.src[i..].chars() {
            match c {
                ' '  | '\t' => (),
                '\n' | '\r' => self.newlines.push(j + 1),
                _           => break
            }
            j += c.len_utf8();
        }
        Ok(j)
    }

    fn lookahead_is(&self, s: &'static str, i: usize) -> Option<usize> {
        if self.src[i..].starts_with(s) {
            Some(i + s.len())
        }
        else {
            None
        }
    }
}

pub fn parse_yacc(s:&str) -> Result<GrammarAST, YaccError> {
    let mut yp = YaccParser::new(s.to_string());
    match yp.parse() {
        Ok(_) => Ok(yp.grammar),
        Err(e) => Err(e)
    }
}

#[cfg(test)]
mod test {
    use super::{parse_yacc, YaccError, YaccErrorKind};
    use grammar::{AssocKind, Precedence};
    use grammar_ast::{Rule, Symbol};

    fn nonterminal(n: &str) -> Symbol {
        Symbol::Nonterminal(n.to_string())
    }

    fn terminal(n: &str) -> Symbol {
        Symbol::Terminal(n.to_string())
    }

    #[test]
    fn test_macro() {
        assert_eq!(Symbol::Terminal("A".to_string()), terminal("A"));
    }

    #[test]
    fn test_symbol_eq() {
        assert_eq!(nonterminal("A"), nonterminal("A"));
        assert!(nonterminal("A") != nonterminal("B"));
        assert!(nonterminal("A") != terminal("A"));
    }

    #[test]
    fn test_rule_eq() {
        assert_eq!(Rule::new("A".to_string()), Rule::new("A".to_string()));
        assert!(Rule::new("A".to_string()) != Rule::new("B".to_string()));

        let mut rule1 = Rule::new("A".to_string());
        rule1.add_symbols(vec![terminal("a")]);
        let mut rule2 = Rule::new("A".to_string());
        rule2.add_symbols(vec![terminal("a")]);
        assert_eq!(rule1, rule2);
    }

    #[test]
    fn test_rule() {
        let src = "
            %%
            A : 'a';
        ".to_string();
        let grm = parse_yacc(&src).unwrap();
        let mut rule1 = Rule::new("A".to_string());
        rule1.add_symbols(vec![terminal("a")]);
        assert_eq!(*grm.get_rule("A").unwrap(), rule1);
        let mut rule2 = Rule::new("B".to_string());
        rule2.add_symbols(vec![terminal("a")]);
        assert!(*grm.get_rule("A").unwrap() != rule2);
    }

    #[test]
    fn test_rule_production_simple() {
        let src = "
            %%
            A : 'a';
            A : 'b';
        ".to_string();
        let grm = parse_yacc(&src).unwrap();
        let mut rule1 = Rule::new("A".to_string());
        rule1.add_symbols(vec![terminal("a")]);
        rule1.add_symbols(vec![terminal("b")]);
        assert_eq!(*grm.get_rule("A").unwrap(), rule1);
        let mut rule2 = Rule::new("B".to_string());
        rule2.add_symbols(vec![terminal("a")]);
        assert!(*grm.get_rule("A").unwrap() != rule2);
    }

    #[test]
    fn test_rule_empty() {
        let src = "
            %%
            A : ;
            B : 'b' | ;
            C : | 'c';
        ".to_string();
        let grm = parse_yacc(&src).unwrap();

        let mut rule1 = Rule::new("A".to_string());
        rule1.add_symbols(vec![]);
        assert_eq!(*grm.get_rule("A").unwrap(), rule1);

        let mut rule2 = Rule::new("B".to_string());
        rule2.add_symbols(vec![terminal("b")]);
        rule2.add_symbols(vec![]);
        assert_eq!(*grm.get_rule("B").unwrap(), rule2);

        let mut rule3 = Rule::new("C".to_string());
        rule3.add_symbols(vec![]);
        rule3.add_symbols(vec![terminal("c")]);
        assert_eq!(*grm.get_rule("C").unwrap(), rule3);
    }

    #[test]
    fn test_rule_alternative() {
        let src = "
            %%
            A : 'a' | 'b';
        ".to_string();
        let grm = parse_yacc(&src).unwrap();
        let mut rule1 = Rule::new("A".to_string());
        rule1.add_symbols(vec![terminal("a")]);
        rule1.add_symbols(vec![terminal("b")]);
        assert_eq!(*grm.get_rule("A").unwrap(), rule1);
        let mut rule2 = Rule::new("B".to_string());
        rule2.add_symbols(vec![terminal("a")]);
        assert!(*grm.get_rule("A").unwrap() != rule2);
    }

    #[test]
    fn test_empty_program() {
        let src = "%%\nA : 'a';\n%%".to_string();
        parse_yacc(&src).unwrap();
    }

    #[test]
    fn test_multiple_symbols() {
        let src = "%%\nA : 'a' B;".to_string();
        let grm = parse_yacc(&src).unwrap();
        let mut rule = Rule::new("A".to_string());
        rule.add_symbols(vec![terminal("a"), nonterminal("B")]);
        assert_eq!(*grm.get_rule("A").unwrap(), rule)
    }

    #[test]
    fn test_token_types() {
        let src = "%%\nA : 'a' \"b\";".to_string();
        let grm = parse_yacc(&src).unwrap();
        let mut rule = Rule::new("A".to_string());
        rule.add_symbols(vec![terminal("a"), terminal("b")]);
        assert_eq!(*grm.get_rule("A").unwrap(), rule)
    }

    #[test]
    fn test_declaration_start() {
        let src = "%start   A\n%%\nA : a;".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert_eq!(grm.start.unwrap(), "A");
    }

    #[test]
    fn test_declaration_token() {
        let src = "%token   a\n%%\nA : a;".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_declaration_token_literal() {
        let src = "%token   'a'\n%%\nA : 'a';".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_declaration_tokens() {
        let src = "%token   a b c 'd'\n%%\nA : a;".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert!(grm.has_token("a"));
        assert!(grm.has_token("b"));
        assert!(grm.has_token("c"));
    }

    #[test]
    fn test_auto_add_tokens() {
        let src = "%%\nA : 'a';".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_token_non_literal() {
        let src = "%token T %%\nA : T;".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert!(grm.has_token("T"));
        match grm.rules.get("A").unwrap().productions[0][0] {
            Symbol::Nonterminal(_) => panic!("Should be terminal"),
            Symbol::Terminal(_)    => ()
        }
    }

    #[test]
    fn test_token_unicode() {
        let src = "%token '❤' %%\nA : '❤';".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert!(grm.has_token("❤"));
    }

    #[test]
    fn test_unicode_err1() {
        let src = "%token '❤' ❤;".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incorrect token parsed"),
            Err(YaccError{kind: YaccErrorKind::IllegalString, line: 1, col: 12}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_unicode_err2() {
        let src = "%token '❤'\n%%\nA : '❤' | ❤;".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incorrect token parsed"),
            Err(YaccError{kind: YaccErrorKind::IllegalString, line: 3, col: 11}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    #[should_panic]
    fn test_simple_decl_fail() {
        let src = "%fail x\n%%\nA : a".to_string();
        parse_yacc(&src).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_empty() {
        let src = "".to_string();
        parse_yacc(&src).unwrap();
    }

    #[test]
    fn test_incomplete_rule1() {
        let src = "%%A:".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccError{kind: YaccErrorKind::IncompleteRule, line: 1, col: 5}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report1() {
        let src = "%%
A:".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccError{kind: YaccErrorKind::IncompleteRule, line: 2, col: 3}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report2() {
        let src = "%%
A:
".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccError{kind: YaccErrorKind::IncompleteRule, line: 3, col: 1}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report3() {
        let src = "

        %woo".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccError{kind: YaccErrorKind::UnknownDeclaration, line: 3, col: 9}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_missing_colon() {
        let src = "%%A x;".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Missing colon parsed"),
            Err(YaccError{kind: YaccErrorKind::MissingColon, line: 1, col: 5}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_premature_end() {
        let src = "%token x".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccError{kind: YaccErrorKind::PrematureEnd, line: 1, col: 8}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_programs_not_supported() {
        let src = "%% %%
x".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Programs parsed"),
            Err(YaccError{kind: YaccErrorKind::ProgramsNotSupported, line: 1, col: 4}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_unknown_declaration() {
        let src = "%woo".to_string();
        match parse_yacc(&src) {
            Ok(_)  => panic!("Unknown declaration parsed"),
            Err(YaccError{kind: YaccErrorKind::UnknownDeclaration, line: 1, col: 1}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_precs() {
        let src = "
          %left '+' '-'
          %left '*'
          %right '/'
          %right '^'
          %nonassoc '~'
          %%
          ".to_string();
        let grm = parse_yacc(&src).unwrap();
        assert_eq!(grm.precs.len(), 6);
        assert_eq!(*grm.precs.get("+").unwrap(), Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(*grm.precs.get("-").unwrap(), Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(*grm.precs.get("*").unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(*grm.precs.get("/").unwrap(), Precedence{level: 2, kind: AssocKind::Right});
        assert_eq!(*grm.precs.get("^").unwrap(), Precedence{level: 3, kind: AssocKind::Right});
        assert_eq!(*grm.precs.get("~").unwrap(), Precedence{level: 4, kind: AssocKind::Nonassoc});
    }

    #[test]
    fn test_dup_precs() {
        let srcs = vec![
          "
          %left 'x'
          %left 'x'
          %%
          ",
          "
          %left 'x'
          %right 'x'
          %%
          ",
          "
          %right 'x'
          %right 'x'
          %%
          ",
          "
          %nonassoc 'x'
          %nonassoc 'x'
          %%
          ",
          "
          %left 'x'
          %nonassoc 'x'
          %%
          ",
          "
          %right 'x'
          %nonassoc 'x'
          %%
          "
          ];
        for src in srcs.iter() {
            match parse_yacc(&src.to_string()) {
                Ok(_) => panic!("Duplicate precedence parsed"),
                Err(YaccError{kind: YaccErrorKind::DuplicatePrecedence, line: 3, ..}) => (),
                Err(e) => panic!("Incorrect error returned {}", e)
            }
        }
    }
}