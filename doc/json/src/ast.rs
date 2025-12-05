#![allow(warnings)]

#[derive(Debug, Clone)]
pub enum JsonValue {
    String(String),
    Number(String),
    Bool(bool),
    Array(Array),
    Object(JsonObject),
    Null,
}

#[derive(Debug, Clone)]
pub struct Array {
    pub elements: Vec<JsonValue>,
}

impl From<Vec<JsonValue>> for Array {
    fn from(elements: Vec<JsonValue>) -> Self {
        Array { elements }
    }
}

#[derive(Debug, Clone)]
pub struct JsonObject {
    pub members: Vec<(String, JsonValue)>,
}

impl JsonObject{
    pub fn new() -> Self {
        JsonObject { members: vec![] }
    }

    pub fn insert(&mut self, key: String, value: JsonValue) {
        self.members.push((key, value));
    }
}

