//! JMESPath utility functions

extern crate rustc_serialize;

use self::rustc_serialize::json::Json;
use ast::Comparator;

/// Convert a JSON object to an array IFF the value provided is an object.
pub fn object_to_array(data: &Json) -> Json {
    match data.as_object() {
        Some(obj) => Json::Array(obj.values().cloned().collect()),
        None => Json::Null
    }
}

/// Returns the index position N of the length of a Vec minus i
pub fn negative_offset<'a, T: 'a>(data: &'a Vec<T>, i: &i32) -> Option<&'a T> {
    data.len().checked_sub(i.abs() as usize)
        .and_then(|actual_index| data.get(actual_index))
}

/// Returns true if the value is true according to JMESPath rules.
pub fn is_truthy(data: &Json) -> bool {
    match data {
        &Json::Boolean(ref b) if *b == true => true,
        &Json::String(ref s) if s.len() > 0 => true,
        &Json::Array(ref a) if a.len() > 0 => true,
        &Json::Object(ref o) if o.len() > 0 => true,
        &Json::I64(_) | &Json::U64(_) | &Json::F64(_) => true,
        _ => false
    }
}

/// Returns the JMESPath type name of a JSON value.
pub fn jp_type(data: &Json) -> &str {
    match data {
        &Json::Boolean(_) => "boolean",
        &Json::String(_) => "string",
        &Json::I64(_) | &Json::U64(_) | &Json::F64(_) => "number",
        &Json::Array(_) => "array",
        &Json::Object(_) => "object",
        &Json::Null => "null"
    }
}

/// Compares two JSON values using a comparator.
pub fn comparison(cmp: &Comparator, lhs: &Json, rhs: &Json) -> Json {
    match cmp {
        &Comparator::Eq => Json::Boolean(lhs == rhs),
        &Comparator::Ne => Json::Boolean(lhs != rhs),
        &Comparator::Lt if lhs.is_number() && rhs.is_number() => Json::Boolean(lhs < rhs),
        &Comparator::Lte if lhs.is_number() && rhs.is_number() => Json::Boolean(lhs <= rhs),
        &Comparator::Gt if lhs.is_number() && rhs.is_number() => Json::Boolean(lhs > rhs),
        &Comparator::Gte if lhs.is_number() && rhs.is_number() => Json::Boolean(lhs >= rhs),
        _ => Json::Null
    }
}


#[cfg(test)]
mod tests {
    extern crate rustc_serialize;
    use self::rustc_serialize::json::Json;
    use super::*;
    use ast::Comparator;

    #[test] fn test_determines_types() {
        assert_eq!("object".to_string(), jp_type(&Json::from_str(&"{\"foo\": \"bar\"}").unwrap()));
        assert_eq!("array".to_string(), jp_type(&Json::from_str(&"[\"foo\"]").unwrap()));
        assert_eq!("null".to_string(), jp_type(&Json::Null));
        assert_eq!("boolean".to_string(), jp_type(&Json::Boolean(true)));
        assert_eq!("string".to_string(), jp_type(&Json::String("foo".to_string())));
        assert_eq!("number".to_string(), jp_type(&Json::U64(10)));
    }

    #[test] fn test_is_truthy() {
        assert_eq!(true, is_truthy(&Json::from_str(&"{\"foo\": \"bar\"}").unwrap()));
        assert_eq!(false, is_truthy(&Json::from_str(&"{}").unwrap()));
        assert_eq!(true, is_truthy(&Json::from_str(&"[\"foo\"]").unwrap()));
        assert_eq!(false, is_truthy(&Json::from_str(&"[]").unwrap()));
        assert_eq!(false, is_truthy(&Json::Null));
        assert_eq!(true, is_truthy(&Json::Boolean(true)));
        assert_eq!(false, is_truthy(&Json::Boolean(false)));
        assert_eq!(true, is_truthy(&Json::String("foo".to_string())));
        assert_eq!(false, is_truthy(&Json::String("".to_string())));
        assert_eq!(true, is_truthy(&Json::U64(10)));
        assert_eq!(true, is_truthy(&Json::U64(0)));
    }

    #[test] fn test_negative_offset() {
        assert_eq!(Some(&3), negative_offset(&vec!(1, 2, 3), &-1));
        assert_eq!(Some(&3), negative_offset(&vec!(1, 2, 3), &1));
        assert_eq!(Some(&2), negative_offset(&vec!(1, 2, 3), &-2));
        assert_eq!(Some(&1), negative_offset(&vec!(1, 2, 3), &-3));
        assert_eq!(Some(&1), negative_offset(&vec!(1, 2, 3), &3));
        assert_eq!(None, negative_offset(&vec!(1, 2, 3), &-4));
        assert_eq!(None, negative_offset(&vec!(1, 2, 3), &4));
    }

    #[test] fn test_object_to_array() {
        let good = Json::from_str(&"{\"foo\": \"bar\"}").unwrap();
        assert_eq!(object_to_array(&good), Json::from_str(&"[\"bar\"]").unwrap());
        let bad = Json::from_str(&"[\"foo\", \"bar\", \"baz\", \"bam\"]").unwrap();
        assert_eq!(Json::Null, object_to_array(&bad));
    }

    #[test] fn test_eq_ne_comparison() {
        let l = Json::String("foo".to_string());
        let r = Json::String("foo".to_string());
        assert_eq!(Json::Boolean(true), comparison(&Comparator::Eq, &l, &r));
        assert_eq!(Json::Boolean(false), comparison(&Comparator::Ne, &l, &r));
    }

    #[test] fn test_comparison() {
        let invalid = Json::String("foo".to_string());
        let l = Json::U64(10);
        let r = Json::U64(20);
        assert_eq!(Json::Null, comparison(&Comparator::Gt, &invalid, &r));
        assert_eq!(Json::Boolean(false), comparison(&Comparator::Gt, &l, &r));
        assert_eq!(Json::Boolean(false), comparison(&Comparator::Gte, &l, &r));
        assert_eq!(Json::Boolean(true), comparison(&Comparator::Gt, &r, &l));
        assert_eq!(Json::Boolean(true), comparison(&Comparator::Gte, &r, &l));
        assert_eq!(Json::Boolean(true), comparison(&Comparator::Lt, &l, &r));
        assert_eq!(Json::Boolean(true), comparison(&Comparator::Lte, &l, &r));
        assert_eq!(Json::Boolean(false), comparison(&Comparator::Lt, &r, &l));
        assert_eq!(Json::Boolean(false), comparison(&Comparator::Lte, &r, &l));
    }
}
