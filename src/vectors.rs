use crate::{
    exception::Exception, gc::Gc, lists::slice_to_list, num::Number, registry::bridge, value::Value,
};
use rug::Integer;
use std::{clone::Clone, ops::Range};

fn try_make_range(start: usize, end: usize) -> Result<Range<usize>, Exception> {
    if end < start {
        Err(Exception::error(format!(
            "Range end {} cannot be less than start {}",
            end, start
        )))
    } else {
        Ok(start..end)
    }
}
fn try_to_u64(n: &Gc<Value>) -> Result<u64, Exception> {
    n.read().as_ref().try_into().map(|n: &Number| n.to_u64())
}

trait Indexer {
    type Collection;

    fn get_len(&self, _: &Self::Collection) -> usize;
    fn get_range(&self, _: &Self::Collection, _: Range<usize>) -> Self::Collection;
    fn try_get<'a>(&self, _: &'a Value) -> Result<&'a Self::Collection, Exception>;

    fn index(&self, from: &Gc<Value>, range: &[Gc<Value>]) -> Result<Self::Collection, Exception> {
        let from = from.read();
        let collection = self.try_get(&from)?;
        let len = self.get_len(collection);

        let start: usize = range
            .first()
            .map(try_to_u64)
            .transpose()?
            .unwrap_or(0)
            .try_into()?;
        let end: usize = range
            .get(1)
            .map(try_to_u64)
            .transpose()?
            .map(<u64 as TryInto<usize>>::try_into)
            .transpose()?
            .unwrap_or(len);

        let range = try_make_range(start, end)?;
        if range.end > len {
            return Err(Exception::invalid_range(range, len));
        }

        Ok(self.get_range(collection, range))
    }
}

struct StringIndexer;
impl Indexer for StringIndexer {
    type Collection = String;

    fn get_len(&self, string: &String) -> usize {
        string.chars().count()
    }
    fn get_range(&self, string: &String, range: Range<usize>) -> String {
        string
            .chars()
            .skip(range.start)
            .take(range.end - range.start)
            .collect()
    }
    fn try_get<'a>(&self, val: &'a Value) -> Result<&'a String, Exception> {
        val.try_into()
    }
}
struct VectorIndexer;
impl Indexer for VectorIndexer {
    type Collection = Vec<Value>;

    fn get_len(&self, vec: &Vec<Value>) -> usize {
        vec.len()
    }
    fn get_range(&self, vec: &Vec<Value>, range: Range<usize>) -> Self::Collection {
        vec.iter()
            .skip(range.start)
            .take(range.end - range.start)
            .cloned()
            .collect()
    }
    fn try_get<'a>(&self, val: &'a Value) -> Result<&'a Vec<Value>, Exception> {
        val.try_into()
    }
}

#[bridge(name = "make-vector", lib = "(base)")]
pub async fn make_vector(n: &Gc<Value>, with: &[Gc<Value>]) -> Result<Vec<Gc<Value>>, Exception> {
    let n = n.read();
    let n: &Number = n.as_ref().try_into()?;
    let n = n.to_u64();

    Ok((0..n)
        .map(|_| {
            with.first()
                .cloned()
                .unwrap_or_else(|| Gc::new(Value::Null))
        })
        .collect())
}

#[bridge(name = "vector", lib = "(base)")]
pub async fn vector(args: &[Gc<Value>]) -> Result<Vec<Gc<Value>>, Exception> {
    Ok(vec![Gc::new(Value::Vector(
        args.iter()
            .map(Gc::read)
            .map(|guard| guard.as_ref().clone())
            .collect(),
    ))])
}

#[bridge(name = "vector-ref", lib = "(base)")]
pub async fn vector_ref(vec: &Gc<Value>, index: &Gc<Value>) -> Result<Vec<Gc<Value>>, Exception> {
    let vec = vec.read();
    let vec: &Vec<Value> = vec.as_ref().try_into()?;

    let index = index.read();
    let index: &Number = index.as_ref().try_into()?;
    let index: usize = index.to_u64().try_into()?;

    Ok(vec![Gc::new(
        vec.get(index)
            .ok_or_else(|| Exception::invalid_index(index, vec.len()))?
            .clone(),
    )])
}

#[bridge(name = "vector-length", lib = "(base)")]
pub async fn vector_len(vec: &Gc<Value>) -> Result<Vec<Gc<Value>>, Exception> {
    let vec = vec.read();
    let vec: &Vec<Value> = vec.as_ref().try_into()?;

    Ok(vec![Gc::new(Value::Number(
        match i64::try_from(vec.len()) {
            Ok(len) => Number::FixedInteger(len),
            Err(_) => Number::BigInteger(Integer::from(vec.len())),
        },
    ))])
}

#[bridge(name = "vector-set!", lib = "(base)")]
pub async fn vector_set(
    vec: &Gc<Value>,
    index: &Gc<Value>,
    with: &Gc<Value>,
) -> Result<Vec<Gc<Value>>, Exception> {
    let mut vec = vec.write();
    let vec: &mut Vec<Value> = vec.as_mut().try_into()?;
    let vec_len = vec.len();

    let index = index.read();
    let index: &Number = index.as_ref().try_into()?;
    let index: usize = index.to_u64().try_into()?;

    let index = vec
        .get_mut(index)
        .ok_or_else(|| Exception::invalid_index(index, vec_len))?;
    *index = with.read().clone();

    Ok(vec![])
}

#[bridge(name = "vector->list", lib = "(base)")]
pub async fn vector_to_list(
    from: &Gc<Value>,
    range: &[Gc<Value>],
) -> Result<Vec<Gc<Value>>, Exception> {
    let vec: Vec<Gc<Value>> = VectorIndexer
        .index(from, range)?
        .into_iter()
        .map(Gc::new)
        .collect();
    Ok(vec![Gc::new(slice_to_list(vec.as_slice()))])
}

#[bridge(name = "vector->string", lib = "(base)")]
pub async fn vector_to_string(
    from: &Gc<Value>,
    range: &[Gc<Value>],
) -> Result<Vec<Gc<Value>>, Exception> {
    Ok(vec![Gc::new(Value::String(
        VectorIndexer
            .index(from, range)?
            .into_iter()
            .map(<Value as TryInto<char>>::try_into)
            .collect::<Result<String, _>>()?,
    ))])
}

#[bridge(name = "string->vector", lib = "(base)")]
pub async fn string_to_vector(
    from: &Gc<Value>,
    range: &[Gc<Value>],
) -> Result<Vec<Gc<Value>>, Exception> {
    Ok(vec![Gc::new(Value::Vector(
        StringIndexer
            .index(from, range)?
            .chars()
            .map(Value::Character)
            .collect(),
    ))])
}

#[bridge(name = "vector-copy", lib = "(base)")]
pub async fn vector_copy(
    from: &Gc<Value>,
    range: &[Gc<Value>],
) -> Result<Vec<Gc<Value>>, Exception> {
    Ok(vec![Gc::new(Value::Vector(
        VectorIndexer.index(from, range)?,
    ))])
}

#[bridge(name = "vector-copy!", lib = "(base)")]
pub async fn vector_copy_to(
    to: &Gc<Value>,
    at: &Gc<Value>,
    from: &Gc<Value>,
    range: &[Gc<Value>],
) -> Result<Vec<Gc<Value>>, Exception> {
    let mut to = to.write();
    let to: &mut Vec<Value> = to.as_mut().try_into()?;

    let at: usize = try_to_u64(at)?.try_into()?;

    if at >= to.len() {
        return Err(Exception::invalid_index(at, to.len()));
    }

    let copies = VectorIndexer.index(from, range)?;
    if copies.len() + at >= to.len() {
        return Err(Exception::invalid_range(at..at + copies.len(), to.len()));
    }

    copies
        .into_iter()
        .enumerate()
        .map(|(i, copy)| (i + at, copy))
        .for_each(|(i, copy)| {
            if let Some(i) = to.get_mut(i) {
                *i = copy;
            }
        });

    Ok(vec![])
}

#[bridge(name = "vector-append", lib = "(base)")]
pub async fn vector_append(args: &[Gc<Value>]) -> Result<Vec<Gc<Value>>, Exception> {
    if args.is_empty() {
        return Err(Exception::wrong_num_of_variadic_args(1..usize::MAX, 0));
    }

    Ok(vec![Gc::new(Value::Vector(
        args.iter()
            .flat_map(|arg| {
                <&Value as TryInto<&Vec<Value>>>::try_into(arg.read().as_ref())
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect::<Vec<_>>(),
    ))])
}

#[bridge(name = "vector-fill!", lib = "(base)")]
pub async fn vector_fill(
    vector: &Gc<Value>,
    with: &Gc<Value>,
    start: &Gc<Value>,
    end: &[Gc<Value>],
) -> Result<Vec<Gc<Value>>, Exception> {
    let mut vector = vector.write();
    let vector: &mut Vec<Value> = vector.as_mut().try_into()?;

    let start: usize = try_to_u64(start)?.try_into()?;
    let end: usize = end
        .first()
        .map(try_to_u64)
        .transpose()?
        .map(|n| n.try_into())
        .transpose()?
        .unwrap_or(vector.len());

    let range = try_make_range(start, end)?;
    if range.end > vector.len() {
        return Err(Exception::invalid_range(range, vector.len()));
    }

    range.for_each(|i| {
        if let Some(slot) = vector.get_mut(i) {
            *slot = with.read().as_ref().clone();
        }
    });

    Ok(vec![])
}
