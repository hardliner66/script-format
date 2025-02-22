use std::any::TypeId;
use std::time::Instant;

use rhai::{Array, CustomType, Dynamic, ImmutableString, Map, TypeBuilder, FLOAT, INT};

use crate::engine::ScriptResult;

#[allow(clippy::needless_pass_by_value)]
pub fn script_is_some<T>(opt: Option<T>) -> bool {
    opt.is_some()
}

pub fn script_unwrap<T>(opt: Option<T>) -> T {
    opt.unwrap()
}

pub fn script_unwrap_or<T>(opt: Option<T>, default: T) -> T {
    opt.unwrap_or(default)
}

pub fn script_join(v: &[String], sep: &str) -> String {
    v.join(sep)
}

pub fn script_split(s: &str, pattern: &str) -> Vec<Dynamic> {
    s.split(pattern)
        .map(|s| Dynamic::from(s.to_string()))
        .collect()
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
pub fn script_splitn(s: &str, n: INT, pattern: &str) -> Vec<Dynamic> {
    s.splitn(n as usize, pattern)
        .map(|s| Dynamic::from(s.to_string()))
        .collect()
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
pub fn script_rsplitn(s: &str, n: INT, pattern: &str) -> Vec<Dynamic> {
    s.rsplitn(n as usize, pattern)
        .map(|s| Dynamic::from(s.to_string()))
        .collect()
}

pub fn script_string_is_empty(s: &str) -> bool {
    s.is_empty()
}

pub fn script_array_is_empty(s: &Array) -> bool {
    s.is_empty()
}

pub fn script_starts_with(s: &str, pat: &str) -> bool {
    s.starts_with(pat)
}

pub fn script_ends_with(s: &str, pat: &str) -> bool {
    s.ends_with(pat)
}

pub fn script_trim(s: &str) -> &str {
    s.trim()
}

pub fn script_is_no_string(_: Dynamic) -> bool {
    false
}

pub fn script_is_string(_: &str) -> bool {
    true
}

fn is_true(b: bool) -> bool {
    b
}

pub fn script_any_void(arr: &Vec<Dynamic>) -> bool {
    arr.iter()
        .filter(|a| a.is_bool())
        .filter(|a| a.as_bool().unwrap())
        .count()
        > 0
}

pub fn script_any_type<T: PartialEq>(arr: &Vec<T>, v: T) -> bool {
    arr.iter().map(|a| a == &v).any(is_true)
}

pub fn script_any(arr: &Vec<Dynamic>, v: rhai::Dynamic) -> ScriptResult<bool> {
    let values: ScriptResult<Vec<bool>> = arr
        .iter()
        .map(|a| script_value_equals(a.clone(), v.clone()))
        .collect();
    Ok(values?.into_iter().any(is_true))
}

pub fn script_all_void(arr: &Vec<Dynamic>) -> bool {
    let expected = arr.len();
    arr.iter()
        .filter(|a| a.is_bool())
        .filter(|a| a.as_bool().unwrap())
        .count()
        == expected
}

pub fn script_all_type<T: PartialEq>(arr: &Vec<T>, v: T) -> bool {
    arr.iter().map(|a| a == &v).all(is_true)
}

pub fn script_all(arr: &Vec<Dynamic>, v: rhai::Dynamic) -> ScriptResult<bool> {
    let values: ScriptResult<Vec<bool>> = arr
        .iter()
        .map(|a| script_value_equals(a.clone(), v.clone()))
        .collect();
    Ok(values?.into_iter().all(is_true))
}

pub fn script_none_void(arr: &Vec<Dynamic>) -> bool {
    arr.iter()
        .filter(|a| a.is_bool())
        .filter(|a| a.as_bool().unwrap())
        .count()
        == 0
}

pub fn script_none_type<T: PartialEq>(arr: &Vec<T>, v: T) -> bool {
    !arr.iter().map(|a| a == &v).all(is_true)
}

pub fn script_none(arr: &Vec<Dynamic>, v: rhai::Dynamic) -> ScriptResult<bool> {
    let values: ScriptResult<Vec<bool>> = arr
        .iter()
        .map(|a| script_value_equals(a.clone(), v.clone()))
        .collect();
    Ok(!values?.into_iter().all(is_true))
}

#[derive(Clone, CustomType)]
pub struct ToBe {
    count: INT,
    value: Dynamic,
}

pub fn script_to_be(count: INT, value: Dynamic) -> ToBe {
    ToBe { count, value }
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
pub fn script_require(arr: Array, tb: ToBe) -> ScriptResult<bool> {
    let values: ScriptResult<Vec<_>> = arr
        .iter()
        .map(|a| script_value_equals(a.clone(), tb.value.clone()))
        .collect();
    let count = values?.into_iter().filter(|b: &bool| is_true(*b)).count();
    if count == tb.count as usize {
        Ok(true)
    } else {
        Err(format!(
            "Value \"{}\" expected {} times but got only {count}!",
            tb.value, tb.count
        )
        .into())
    }
}

pub fn script_map_equals(m1: &Map, m2: &Map) -> ScriptResult<bool> {
    if m1.len() != m2.len() {
        return Ok(false);
    }
    for (key, value) in m1 {
        if let Some(value2) = m2.get(key) {
            if !script_value_equals(value.clone(), value2.clone())? {
                return Ok(false);
            }
        } else {
            return Ok(false);
        }
    }
    Ok(true)
}

pub fn script_string_contains(s: &str, v: &str) -> bool {
    s.contains(v)
}

pub fn script_map_contains(m: &Map, name: &str) -> bool {
    m.get(name).is_some()
}

pub fn script_value_equals(v1: Dynamic, v2: Dynamic) -> ScriptResult<bool> {
    let t1 = v1.type_id();
    let t2 = v2.type_id();
    if t1 != t2 {
        Ok(false)
    } else if t1 == TypeId::of::<()>() {
        Ok(true)
    } else if t1 == TypeId::of::<bool>() {
        Ok(v1.as_bool() == v2.as_bool())
    } else if t1 == TypeId::of::<ImmutableString>() {
        Ok(v1.into_immutable_string() == v2.into_immutable_string())
    } else if t1 == TypeId::of::<char>() {
        Ok(v1.as_char() == v2.as_char())
    } else if t1 == TypeId::of::<INT>() {
        Ok(v1.as_int() == v2.as_int())
    } else if t1 == TypeId::of::<FLOAT>() {
        Ok(v1.as_float() == v2.as_float())
    } else if t1 == TypeId::of::<Array>() {
        Ok(script_array_equals(
            &v1.cast::<Array>(),
            &v2.cast::<Array>(),
        ))
    } else if t1 == TypeId::of::<Map>() {
        script_map_equals(&v1.cast::<Map>(), &v2.cast::<Map>())
    } else if t1 == TypeId::of::<Instant>() {
        Ok(v1.cast::<Instant>() == v2.cast::<Instant>())
    } else {
        println!("1");
        Err("unsupported type".into())
    }
}

pub fn script_array_equals(arr: &Array, arr2: &Array) -> bool {
    if arr.len() != arr2.len() {
        return false;
    }
    let result = arr
        .iter()
        .zip(arr2.iter())
        .all(|(e1, e2)| script_value_equals(e1.clone(), e2.clone()).unwrap_or_default());
    result
}

pub fn script_array_contains(arr: Array, v: &Dynamic) -> bool {
    arr.into_iter()
        .any(|ele| script_value_equals(ele, v.clone()).unwrap_or_default())
}
