mod parser {
    include!(concat!(env!("OUT_DIR"), "/list.yapg.rs"));
}

mod ast {
    #![allow(unused)]

    #[derive(Debug, Clone, PartialEq)]
    pub enum Item {
        Num(i32),
        List(List),
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct List(pub Vec<Item>);

    #[derive(Debug, Clone)]
    pub enum Token {
        Num(i32),
        Comma,
        LBracket,
        RBracket,
    }

    impl From<&str> for Token {
        fn from(s: &str) -> Self {
            match s {
                "[" => Token::LBracket,
                "]" => Token::RBracket,
                "," => Token::Comma,
                num => Token::Num(num.parse().expect("expected number")),
            }
        }
    }

    pub struct SemanticAction;

    impl SemanticAction {
        pub fn make_empty_list(&mut self, _: (Token, Token)) -> List {
            List(vec![])
        }

        pub fn make_list(&mut self, (_, items, _): (Token, Vec<Item>, Token)) -> List {
            List(items)
        }

        pub fn make_single_item(&mut self, item: (Item)) -> Vec<Item> {
            vec![item]
        }

        pub fn append_item(
            &mut self,
            (_, item, mut items, _): (Token, Item, Vec<(Token, Item)>, Token),
        ) -> List {
            let mut res = vec![item];
            res.extend(items.into_iter().map(|(_, it)| it));
            List(res)
        }

        pub fn make_num_item(&mut self, token: Token) -> Item {
            match token {
                Token::Num(n) => Item::Num(n),
                _ => panic!("expected Num token"),
            }
        }

        pub fn make_list_item(&mut self, list: List) -> Item {
            Item::List(list)
        }
    }
}

#[test]
fn test_empty_list() {
    let actioner = ast::SemanticAction;
    let parser = parser::ListParser::new(actioner);
    let input = "[ ]";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(ast::Token::from).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    assert_eq!(res.unwrap(), ast::List(vec![]));
}

#[test]
fn test_single_item() {
    let actioner = ast::SemanticAction;
    let parser = parser::ListParser::new(actioner);
    let input = "[ 42 ]";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(ast::Token::from).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    assert_eq!(res.unwrap(), ast::List(vec![ast::Item::Num(42)]));
}

#[test]
fn test_multiple_items() {
    let actioner = ast::SemanticAction;
    let parser = parser::ListParser::new(actioner);
    let input = "[ 1 , 2 , 3 ]";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(ast::Token::from).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    assert_eq!(
        res.unwrap(),
        ast::List(vec![ast::Item::Num(1), ast::Item::Num(2), ast::Item::Num(3)])
    );
}

#[test]
fn test_nested_list() {
    let actioner = ast::SemanticAction;
    let parser = parser::ListParser::new(actioner);
    let input = "[ 1 , [ 2 , 3 ] , 4 ]";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(ast::Token::from).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    let expected = ast::List(vec![
        ast::Item::Num(1),
        ast::Item::List(ast::List(vec![ast::Item::Num(2), ast::Item::Num(3)])),
        ast::Item::Num(4),
    ]);
    assert_eq!(res.unwrap(), expected);
}
