use std::any::TypeId;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::Instant;

use rhai::packages::{CorePackage, Package};
use rhai::{Array, Dynamic, Engine, EvalAltResult, ImmutableString, Map, FLOAT, INT};

type ScriptResult<T> = Result<T, Box<EvalAltResult>>;

#[allow(clippy::needless_pass_by_value)]
fn script_is_some<T>(opt: Option<T>) -> bool {
    opt.is_some()
}

fn script_unwrap<T>(opt: Option<T>) -> T {
    opt.unwrap()
}

fn script_unwrap_or<T>(opt: Option<T>, default: T) -> T {
    opt.unwrap_or(default)
}

fn script_join(v: &[String], sep: &str) -> String {
    v.join(sep)
}

fn script_split(s: &str, pattern: &str) -> Vec<Dynamic> {
    s.split(pattern)
        .map(|s| Dynamic::from(s.to_string()))
        .collect()
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn script_splitn(s: &str, n: INT, pattern: &str) -> Vec<Dynamic> {
    s.splitn(n as usize, pattern)
        .map(|s| Dynamic::from(s.to_string()))
        .collect()
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn script_rsplitn(s: &str, n: INT, pattern: &str) -> Vec<Dynamic> {
    s.rsplitn(n as usize, pattern)
        .map(|s| Dynamic::from(s.to_string()))
        .collect()
}

fn script_string_is_empty(s: &str) -> bool {
    s.is_empty()
}

fn script_array_is_empty(s: &Array) -> bool {
    s.is_empty()
}

fn script_starts_with(s: &str, pat: &str) -> bool {
    s.starts_with(pat)
}

fn script_ends_with(s: &str, pat: &str) -> bool {
    s.ends_with(pat)
}

fn script_trim(s: &str) -> &str {
    s.trim()
}

fn script_is_no_string(_: Dynamic) -> bool {
    false
}

fn script_is_string(_: &str) -> bool {
    true
}

fn script_any(arr: &Array) -> ScriptResult<bool> {
    if arr.iter().all(rhai::Dynamic::is::<bool>) {
        Ok(arr.iter().any(|b| b.as_bool().unwrap()))
    } else {
        Err("any only takes bool values".into())
    }
}

fn script_all(arr: &Array) -> ScriptResult<bool> {
    if arr.iter().all(rhai::Dynamic::is::<bool>) {
        Ok(arr.iter().all(|b| b.as_bool().unwrap()))
    } else {
        Err("all only takes bool values".into())
    }
}

fn script_none(arr: &Array) -> ScriptResult<bool> {
    if arr.iter().all(rhai::Dynamic::is::<bool>) {
        Ok(!arr.iter().any(|b| b.as_bool().unwrap()))
    } else {
        Err("none only takes bool values".into())
    }
}

#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn script_require(arr: &Array, n: INT) -> ScriptResult<bool> {
    if arr.iter().all(rhai::Dynamic::is::<bool>) {
        Ok(arr.iter().filter(|b| b.as_bool().unwrap()).count() == n as usize)
    } else {
        Err("none only takes bool values".into())
    }
}

fn script_map_equals(m1: &Map, m2: &Map) -> ScriptResult<bool> {
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

fn script_string_contains(s: &str, v: &str) -> bool {
    s.contains(v)
}

fn script_map_contains(m: &Map, name: &str) -> bool {
    m.get(name).is_some()
}

fn script_value_equals(v1: Dynamic, v2: Dynamic) -> ScriptResult<bool> {
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
        Err("unsupported type".into())
    }
}

fn script_array_equals(arr: &Array, arr2: &Array) -> bool {
    if arr.len() != arr2.len() {
        return false;
    }
    let result = arr
        .iter()
        .zip(arr2.iter())
        .all(|(e1, e2)| script_value_equals(e1.clone(), e2.clone()).unwrap_or_default());
    result
}

fn script_array_contains(arr: Array, v: &Dynamic) -> bool {
    arr.into_iter()
        .any(|ele| script_value_equals(ele, v.clone()).unwrap_or_default())
}

#[macro_export]
macro_rules! register_vec {
    ($T: ty) => {
        engine
            .register_type::<Vec<$T>>()
            .register_fn("len", |v: Vec<$T>| v.len())
            .register_iterator::<Vec<$T>>()
            .register_iterator::<&Vec<&$T>>()
            .register_iterator::<Vec<$T>>()
            .register_iterator::<&Vec<&$T>>()
            .register_indexer_get(|v: &mut Vec<$T>, i: i64| v[usize::try_from(i).unwrap()].clone());
    };
}

#[macro_export]
macro_rules! register_options {
    ($engine: ident, ($($T: ty),*)) => {
        $(
        $engine
            .register_fn("is_some", script_is_some::<$T>)
            .register_fn("unwrap", script_unwrap::<$T>)
            .register_fn("unwrap_or", script_unwrap_or::<$T>);
        )*
    };
}

#[allow(clippy::too_many_lines)]
pub fn build_engine(messages: Rc<RefCell<Vec<String>>>, debug: bool) -> Engine {
    let mut engine = Engine::new();
    engine.set_max_expr_depths(128, 64);

    let package = CorePackage::new();

    engine.register_global_module(package.as_shared_module());

    let indent = Rc::new(RefCell::new(" ".to_owned()));

    let v = indent.clone();

    // This isn't deprecated, the api is just volatile and may change
    #[allow(deprecated)]
    engine.on_var(move |name, _, _| match name {
        "IND" => Ok(Some(v.borrow().clone().into())),
        _ => Ok(None),
    });

    let v = indent.clone();
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    engine.register_fn("IND", move |count: i64| v.borrow().repeat(count as usize));

    let v = indent.clone();
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    engine.register_fn("SET_INDENT", move |value: &str| {
        value.clone_into(&mut v.borrow_mut());
    });

    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    engine.register_fn("NL", |count: i64| "\n".repeat(count as usize));

    register_options!(
        engine,
        (String, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128)
    );

    engine
        .register_fn("join", script_join)
        .register_fn("split", script_split)
        .register_fn("splitn", script_splitn)
        .register_fn("rsplitn", script_rsplitn)
        .register_fn("is_empty", script_string_is_empty)
        .register_fn("is_empty", script_array_is_empty)
        .register_fn("starts_with", script_starts_with)
        .register_fn("ends_with", script_ends_with)
        .register_fn("trim", script_trim)
        .register_fn("is_string", script_is_no_string)
        .register_fn("is_string", script_is_string);

    // DSL
    engine
        .register_custom_operator("and", 60)
        .unwrap()
        .register_fn("and", |a: bool, b: bool| a && b)
        .register_custom_operator("or", 30)
        .unwrap()
        .register_fn("or", |a: bool, b: bool| a || b)
        .register_custom_operator("xor", 30)
        .unwrap()
        .register_fn("xor", |a: bool, b: bool| a ^ b)
        .register_custom_operator("contains", 15)
        .unwrap()
        .register_custom_operator("equals", 15)
        .unwrap()
        .register_custom_operator("require", 15)
        .unwrap()
        .register_fn("contains", script_map_contains)
        .register_fn("contains", script_string_contains)
        .register_fn("equals", script_map_equals)
        .register_fn("equals", script_value_equals)
        .register_fn("equals", script_array_equals)
        .register_fn("contains", script_array_contains)
        .register_fn("require", script_require)
        .register_fn("any", script_any)
        .register_fn("all", script_all)
        .register_fn("none", script_none);

    macro_rules! register_msg_single {
        ($($T: ty),*) => {
            $(
            {
                let messages = messages.clone();
                engine.register_fn("-", move |msg: $T| {
                    messages.borrow_mut().push(format!("{msg}"));
                });
            }
            )*
        };
    }

    register_msg_single!(&str, usize, bool);

    macro_rules! register_msg_multi {
        ($(($A: ty, $B: ty)),*) => {
            $(
            {
                let messages = messages.clone();
                engine.register_fn("++", move |a: $A, b: $B| {
                    messages.borrow_mut().push(format!("{a}"));
                    messages.borrow_mut().push(format!("{b}"));
                });
            }
            )*
        };
    }

    register_msg_multi!(
        (&str, &str),
        (&str, usize),
        (usize, &str),
        (usize, usize),
        (&str, bool),
        (bool, &str),
        (bool, usize),
        (bool, bool)
    );

    // macro_rules! register_comparison {
    //     ($(($A: ty, $B: ty, $C: ty)),*) => {
    //         $(
    //         engine.register_fn(">",  |left: $A, right: $B| left as $C >  right as $C);
    //         engine.register_fn(">=", |left: $A, right: $B| left as $C >= right as $C);
    //         engine.register_fn("<",  |left: $A, right: $B| left as $C <  right as $C);
    //         engine.register_fn("<=", |left: $A, right: $B| left as $C <= right as $C);
    //         engine.register_fn("!=", |left: $A, right: $B| left as $C != right as $C);
    //         engine.register_fn("==", |left: $A, right: $B| left as $C == right as $C);

    //         engine.register_fn(">",  |left: $B, right: $A| left as $C >  right as $C);
    //         engine.register_fn(">=", |left: $B, right: $A| left as $C >= right as $C);
    //         engine.register_fn("<",  |left: $B, right: $A| left as $C <  right as $C);
    //         engine.register_fn("<=", |left: $B, right: $A| left as $C <= right as $C);
    //         engine.register_fn("!=", |left: $B, right: $A| left as $C != right as $C);
    //         engine.register_fn("==", |left: $B, right: $A| left as $C == right as $C);
    //         )*
    //     };
    // }

    // register_comparison!(
    //     (i64, usize, i128),
    //     (i32, usize, i128),
    //     (i16, usize, i128),
    //     (i8, usize, i128),
    //     (u64, usize, usize),
    //     (u32, usize, usize),
    //     (u16, usize, usize),
    //     (u8, usize, usize)
    // );

    macro_rules! register_string_concat_void {
        ($($T: ty),*) => {$({
            let messages = messages.clone();
            engine.register_fn("++", move |a: $T, _b: ()| {
                messages.borrow_mut().push(a.to_string());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |_a: (), b: $T| {
                messages.borrow_mut().push(b.to_string());
            });
        }
        )*};
    }

    macro_rules! register_string_concat {
        ($($T: ty),*) => {$({
            let messages = messages.clone();
            engine.register_fn("++", move |a: $T, b: &str| {
                messages.borrow_mut().push(a.to_string());
                messages.borrow_mut().push(b.to_owned());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: &str, b: $T| {
                messages.borrow_mut().push(a.to_owned());
                messages.borrow_mut().push(b.to_string());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: $T, b: $T| {
                messages.borrow_mut().push(a.to_string());
                messages.borrow_mut().push(b.to_string());
            });
        })*};
    }

    macro_rules! register_string_concat_vec {
        ($($T: ty),*) => {$({
            let messages = messages.clone();
            engine.register_fn("++", move |a: &Vec<$T>, b: &str| {
                messages.borrow_mut().push(format!("{:?}", a));
                messages.borrow_mut().push(b.to_owned());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: &str, b: &Vec<$T>| {
                messages.borrow_mut().push(a.to_owned());
                messages.borrow_mut().push(format!("{:?}", b));
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: &Vec<$T>, b: &Vec<$T>| {
                messages.borrow_mut().push(format!("{:?}", a));
                messages.borrow_mut().push(format!("{:?}", b));
            });
        })*};
    }

    macro_rules! register_concat {
        ($($T: ty),*) => {{
            register_string_concat!($($T),*);
            register_string_concat_vec!($($T),*);
            register_string_concat_void!($($T),*);
        }};
    }

    register_concat!(i32, u32, i64, u64, f32, f64, bool);

    {
        let messages = messages.clone();
        engine.register_fn("++", move |(): (), b: &str| {
            messages.borrow_mut().push(b.to_owned());
        });
    }
    {
        let messages = messages.clone();
        engine.register_fn("++", move |(): (), b: usize| {
            messages.borrow_mut().push(b.to_string());
        });
    }
    engine.register_custom_operator("++", 15).unwrap();
    {
        let messages = messages.clone();
        engine.register_fn("emit", move |msg: &str| {
            messages.borrow_mut().push(msg.to_owned());
        });
    }
    engine.register_custom_operator("then_emit", 15).unwrap();
    {
        let messages = messages.clone();
        engine.register_fn("then_emit", move |a: bool, msg: &str| {
            if a {
                messages.borrow_mut().push(msg.to_owned());
            }
            a
        });
    }
    {
        let messages = messages.clone();
        engine.register_fn("then_emit", move |a: bool, m: Map| {
            if a {
                let msg = m
                    .get("msg")
                    .map(|e| e.clone().into_string().unwrap())
                    .unwrap();
                messages.borrow_mut().push(msg);
            }
            a
        });
    }
    engine.register_custom_operator("or_emit", 15).unwrap();
    {
        let messages = messages.clone();
        engine.register_fn("or_emit", move |a: bool, msg: &str| {
            if !a {
                messages.borrow_mut().push(msg.to_owned());
            }
            a
        });
    }
    {
        engine.register_fn("or_emit", move |a: bool, m: Map| {
            if !a {
                let msg = m
                    .get("msg")
                    .map(|e| e.clone().into_string().unwrap())
                    .unwrap();
                messages.borrow_mut().push(msg);
            }
            a
        });
    }
    // END DSL

    if debug {
        engine.on_print(move |x| eprintln!("INFO => {x}"));
        engine.on_debug(move |x, _, pos| eprintln!("DEBUG({pos:?}) => {x}"));
    } else {
        engine.on_print(|_| ());
        engine.on_debug(|_, _, _| ());
    }

    engine.disable_symbol("eval");

    engine
}
