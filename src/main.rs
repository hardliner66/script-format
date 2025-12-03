use std::{io::Read, path::PathBuf};

use clap::{Parser, ValueEnum};
use script_format::FormattingEngine;

#[derive(Debug, Parser)]
struct Args {
    /// The format of the data to be formatted
    /// If no format is provided, we try to parse the data as all supported formats
    #[arg(short, long)]
    format: Option<DataFormat>,

    /// Enable debug mode for formatting
    #[arg(long, short)]
    debug: bool,

    /// The data to be formatted
    /// If neither this nor input are provided, the data will be read from stdin
    #[arg(conflicts_with = "input")]
    data: Option<String>,

    /// The input file to be rewritten
    /// If neither this nor data are provided, the data will be read from stdin
    #[arg(long, short, conflicts_with = "data")]
    input: Option<PathBuf>,

    /// The script to format the data
    #[arg(long, short)]
    script: PathBuf,

    /// The output file to write the formatted data to
    /// If not provided, the data will be written to stdout
    #[arg(long, short)]
    output: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub enum DataFormat {
    Json,
    Yaml,
    Toml,
    Rsn,
}

pub fn parse_data(content: &str) -> anyhow::Result<serde_value::Value> {
    let result = serde_json::from_str(content)
        .or_else(|_| toml::from_str(content))
        .or_else(|_| serde_yaml::from_str(content))
        .or_else(|_| rsn::from_str(content));
    Ok(result?)
}

fn main() -> anyhow::Result<()> {
    let Args {
        format,
        data,
        input,
        output,
        debug,
        script,
    } = Args::parse();
    let input = data.unwrap_or_else(|| {
        input
            .map(|p| std::fs::read_to_string(p).unwrap())
            .unwrap_or_else(|| {
                let mut buf = Vec::new();
                std::io::stdin().read_to_end(&mut buf).unwrap();
                String::from_utf8(buf).unwrap()
            })
    });
    let data = match format {
        Some(DataFormat::Json) => serde_json::from_str(&input)?,
        Some(DataFormat::Rsn) => rsn::from_str(&input)?,
        Some(DataFormat::Yaml) => serde_yaml::from_str(&input)?,
        Some(DataFormat::Toml) => toml::from_str(&input)?,
        None => parse_data(&input)?,
    };

    let mut engine = FormattingEngine::new(debug);
    engine.register_type::<serde_value::Value>();

    fn index_value_bool(this: &mut serde_value::Value, index: bool) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::Bool(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_u8(this: &mut serde_value::Value, index: u8) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::U8(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_u16(this: &mut serde_value::Value, index: u16) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::U16(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_u32(this: &mut serde_value::Value, index: u32) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::U32(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_u64(this: &mut serde_value::Value, index: u64) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::U64(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_i8(this: &mut serde_value::Value, index: i8) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::I8(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_i16(this: &mut serde_value::Value, index: i16) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::I16(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_i32(this: &mut serde_value::Value, index: i32) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::I32(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_i64(this: &mut serde_value::Value, index: i64) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::I64(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_f32(this: &mut serde_value::Value, index: f32) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::F32(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_f64(this: &mut serde_value::Value, index: f64) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::F64(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_string(this: &mut serde_value::Value, index: String) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::String(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_char(this: &mut serde_value::Value, index: char) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::Char(index)].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    fn index_value_unit(this: &mut serde_value::Value, _index: ()) -> serde_value::Value {
        match this {
            serde_value::Value::Map(map) => map[&serde_value::Value::Unit].clone(),
            _ => panic!("Cannot index into non-object"),
        }
    }

    engine.register_fn("contains", |s: serde_value::Value, v: bool| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::Bool(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::Bool(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: i8| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::I8(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::I8(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: u8| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::U8(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::U8(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: u16| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::U16(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::U16(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: i16| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::I16(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::I16(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: u32| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::U32(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::U32(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: i32| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::I32(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::I32(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: u64| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::U64(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::U64(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: i64| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::I64(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::I64(v.into())),
        _ => false,
    });
    engine.register_fn("contains", |s: serde_value::Value, v: char| match s {
        serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::Char(v.into())),
        serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::Char(v.into())),
        _ => false,
    });

    engine
        .register_type::<serde_value::Value>()
        .register_fn("contains", |s: serde_value::Value, v: &str| match s {
            serde_value::Value::Map(map) => map.contains_key(&serde_value::Value::String(v.into())),
            serde_value::Value::Seq(seq) => seq.contains(&serde_value::Value::String(v.into())),
            serde_value::Value::String(str) => str.contains(v),
            _ => false,
        })
        .register_fn(
            "contains",
            |s: serde_value::Value, v: serde_value::Value| match (s, v) {
                (serde_value::Value::Map(map), v) => map.contains_key(&v),
                (serde_value::Value::Seq(seq), v) => seq.contains(&v),
                (serde_value::Value::String(str), serde_value::Value::String(sub)) => {
                    str.contains(&sub)
                }
                _ => false,
            },
        )
        .register_indexer_get(index_value_bool)
        .register_indexer_get(index_value_u8)
        .register_indexer_get(index_value_u16)
        .register_indexer_get(index_value_u32)
        .register_indexer_get(index_value_u64)
        .register_indexer_get(index_value_i8)
        .register_indexer_get(index_value_i16)
        .register_indexer_get(index_value_i32)
        .register_indexer_get(index_value_i64)
        .register_indexer_get(index_value_f32)
        .register_indexer_get(index_value_f64)
        .register_indexer_get(index_value_string)
        .register_indexer_get(index_value_char)
        .register_indexer_get(index_value_unit)
        .register_indexer_get(index_value_string);

    match engine.format_from_file("data", data, script) {
        Ok(formatted) => match output {
            Some(ref output) => {
                std::fs::write(output, formatted).unwrap();
            }
            None => {
                println!("{formatted}");
            }
        },
        Err(err) => {
            eprintln!("Error formatting data: {}", err);
        }
    }

    Ok(())
}
