//! A bounded over-approximation of an untouched effect payload packet.
//! Facts belong to this dispatch, not to a lexical prefix of handler clauses.
use super::{DefKey, VmFunction, VmPattern, VmType, nominal_layout_descriptor};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Value {
    Unknown,
    Unit,
    Bool(bool),
    Tuple(Vec<Value>),
    Nominal {
        definition: DefKey,
        variant: Option<u32>,
        fields: Vec<Value>,
    },
}
pub(super) type Domain = Vec<Vec<Value>>;

fn weight(value: &Value) -> usize {
    1 + match value {
        Value::Tuple(fields) | Value::Nominal { fields, .. } => fields.iter().map(weight).sum(),
        _ => 0,
    }
}

fn product(columns: Vec<Vec<Value>>) -> Option<Domain> {
    if columns.len() > 4096 {
        return None;
    }
    let mut result = vec![vec![]];
    for column in columns {
        if result.len().checked_mul(column.len())? > 4096 {
            return None;
        }
        let prefix_weight: usize = result.iter().flatten().map(weight).sum();
        let column_weight: usize = column.iter().map(weight).sum();
        if prefix_weight
            .checked_mul(column.len())?
            .checked_add(column_weight.checked_mul(result.len())?)?
            > 65_536
        {
            return None;
        }
        let mut next = vec![];
        for prefix in result {
            for value in &column {
                let mut row = prefix.clone();
                row.push(value.clone());
                next.push(row);
            }
        }
        result = next;
    }
    Some(result)
}

fn values(
    function: &VmFunction,
    ty: &VmType,
    fuel: &mut usize,
    depth: usize,
) -> Option<Vec<Value>> {
    if *fuel == 0 || depth > 32 {
        return None;
    }
    *fuel -= 1;
    let result = match ty {
        VmType::Unit => vec![Value::Unit],
        VmType::Bool => vec![Value::Bool(true), Value::Bool(false)],
        VmType::Tuple(fields) => product(
            fields
                .iter()
                .map(|ty| values(function, ty, fuel, depth + 1))
                .collect::<Option<Vec<_>>>()?,
        )?
        .into_iter()
        .map(Value::Tuple)
        .collect(),
        VmType::Nominal { definition, .. } => {
            let Ok(layout) = nominal_layout_descriptor(function, ty) else {
                return Some(vec![Value::Unknown]);
            };
            let mut result = vec![];
            let mut nodes = 0usize;
            for (variant, fields) in layout.variants.iter().enumerate() {
                let rows = product(
                    fields
                        .iter()
                        .map(|ty| values(function, ty, fuel, depth + 1))
                        .collect::<Option<Vec<_>>>()?,
                )?;
                if result.len().checked_add(rows.len())? > 4096 {
                    return None;
                }
                nodes = nodes
                    .checked_add(rows.len())?
                    .checked_add(rows.iter().flatten().map(weight).sum())?;
                if nodes > 65_536 {
                    return None;
                }
                result.extend(rows.into_iter().map(|fields| Value::Nominal {
                    definition: *definition,
                    variant: layout.is_enum.then_some(variant as u32),
                    fields,
                }));
            }
            result
        }
        _ => vec![Value::Unknown],
    };
    *fuel = fuel.checked_sub(result.iter().map(weight).sum())?;
    Some(result)
}

pub(super) fn packet(function: &VmFunction, registers: &[u32]) -> Option<Domain> {
    // Charge intermediate domains too, before collecting sibling columns.
    let mut fuel = 131_072;
    product(
        registers
            .iter()
            .map(|register| {
                values(
                    function,
                    function.registers.get(*register as usize)?,
                    &mut fuel,
                    0,
                )
            })
            .collect::<Option<Vec<_>>>()?,
    )
}

fn all(results: impl Iterator<Item = Option<bool>>) -> Option<bool> {
    let mut unknown = false;
    for result in results {
        match result {
            Some(false) => return Some(false),
            None => unknown = true,
            Some(true) => {}
        }
    }
    if unknown { None } else { Some(true) }
}

fn matches(pattern: &VmPattern, value: &Value) -> Option<bool> {
    match (pattern, value) {
        (VmPattern::Any, _) => Some(true),
        (_, Value::Unknown) => None,
        (VmPattern::Literal(literal), Value::Bool(value)) => {
            Some(literal == if *value { "true" } else { "false" })
        }
        (VmPattern::Literal(literal), Value::Unit) => Some(literal == "()"),
        (VmPattern::Tuple(patterns), Value::Unit) => Some(patterns.is_empty()),
        (VmPattern::Tuple(patterns), Value::Tuple(fields)) if patterns.len() == fields.len() => {
            all(patterns
                .iter()
                .zip(fields)
                .map(|(pattern, value)| matches(pattern, value)))
        }
        (
            VmPattern::Enum {
                definition,
                variant,
                fields,
                ..
            },
            Value::Nominal {
                definition: actual,
                variant: selected,
                fields: values,
            },
        ) => {
            if definition != actual || Some(*variant) != *selected {
                return Some(false);
            }
            all(fields.iter().map(|field| {
                values
                    .get(field.index as usize)
                    .and_then(|value| matches(&field.pattern, value))
            }))
        }
        (
            VmPattern::Record {
                definition, fields, ..
            },
            Value::Nominal {
                definition: actual,
                variant: None,
                fields: values,
            },
        ) => {
            if definition != actual {
                return Some(false);
            }
            all(fields.iter().map(|field| {
                values
                    .get(field.index as usize)
                    .and_then(|value| matches(&field.pattern, value))
            }))
        }
        _ => None,
    }
}

pub(super) fn refine(domain: &mut Domain, column: usize, pattern: &VmPattern, outcome: bool) {
    domain.retain(|row| {
        row.get(column)
            .and_then(|value| matches(pattern, value))
            .is_none_or(|matched| matched == outcome)
    });
}

pub(super) fn merge(left: &mut Option<Domain>, right: &Option<Domain>) -> bool {
    match (left.as_mut(), right) {
        (Some(left), Some(right)) => {
            let mut changed = false;
            for row in right {
                if !left.contains(row) {
                    left.push(row.clone());
                    changed = true;
                }
            }
            changed
        }
        (Some(_), None) => {
            *left = None;
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_payloads_keep_both_pattern_outcomes() {
        for outcome in [true, false] {
            let mut domain = vec![vec![Value::Unknown]];
            refine(&mut domain, 0, &VmPattern::Literal("42".into()), outcome);
            assert_eq!(domain, vec![vec![Value::Unknown]]);
        }
    }

    #[test]
    fn joins_union_payload_possibilities_and_unknown_predecessors_widen() {
        let mut left = Some(vec![vec![Value::Bool(true)]]);
        assert!(merge(&mut left, &Some(vec![vec![Value::Bool(false)]])));
        assert_eq!(left.as_ref().unwrap().len(), 2);
        assert!(merge(&mut left, &None));
        assert!(left.is_none());
        assert!(!merge(&mut left, &Some(vec![vec![Value::Bool(true)]])));
    }

    #[test]
    fn large_pattern_domains_fall_back_to_unknown() {
        assert!(product(vec![vec![Value::Bool(true), Value::Bool(false)]; 13]).is_none());
        let wide = Value::Tuple(vec![Value::Unknown; 1024]);
        assert!(product(vec![vec![wide]; 65]).is_none());
    }
}
