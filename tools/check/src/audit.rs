//! Parser for the output of Lean `#print axioms` and the audit policy applied to it.

use std::collections::BTreeSet;
use std::fmt;

pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

#[derive(Debug, PartialEq, Eq)]
pub enum AuditError {
    Malformed(String),
    Duplicate(String),
    Unexpected(Vec<String>),
    Missing(Vec<String>),
    Unlisted(Vec<String>),
}

impl fmt::Display for AuditError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(rest) => {
                write!(f, "Could not parse the Lean axiom audit near: {rest:?}")
            }
            Self::Duplicate(name) => write!(f, "Duplicate theorem in the Lean axiom audit: {name}"),
            Self::Unexpected(names) => write!(f, "Unexpected theorem axioms: {}", names.join(", ")),
            Self::Missing(names) => {
                write!(
                    f,
                    "Roots listed in Audit.lean but not audited: {}",
                    names.join(", ")
                )
            }
            Self::Unlisted(names) => {
                write!(
                    f,
                    "Roots audited but not listed in Audit.lean: {}",
                    names.join(", ")
                )
            }
        }
    }
}

const DEPENDS: &str = "' depends on axioms: [";
const NONE: &str = "' does not depend on any axioms";

/// Identifiers named by `#print axioms <ident>` lines, in file order.
pub fn expected_roots(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| line.strip_prefix("#print axioms "))
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Parse the whole Lean output into `(root, axioms)` entries.
/// Names are located from the fixed suffixes, so they may contain any character, including `'`.
pub fn parse(output: &str) -> Result<Vec<(String, Vec<String>)>, AuditError> {
    let mut entries = Vec::new();
    let mut rest = output.trim_start();
    while !rest.is_empty() {
        let malformed = || AuditError::Malformed(rest.chars().take(80).collect());
        let body = rest.strip_prefix('\'').ok_or_else(malformed)?;
        let depends = body.find(DEPENDS);
        let none = body.find(NONE);
        let (end, has_list) = match (depends, none) {
            (Some(d), Some(n)) if n < d => (n, false),
            (Some(d), _) => (d, true),
            (None, Some(n)) => (n, false),
            (None, None) => return Err(malformed()),
        };
        let name = body[..end].to_owned();
        if !has_list {
            entries.push((name, Vec::new()));
            rest = body[end + NONE.len()..].trim_start();
            continue;
        }
        let list = &body[end + DEPENDS.len()..];
        let close = list_end(list).ok_or_else(malformed)?;
        let axioms = list[..close]
            .split(',')
            .map(|axiom| axiom.trim().to_owned())
            .filter(|axiom| !axiom.is_empty())
            .collect();
        entries.push((name, axioms));
        rest = list[close + 1..].trim_start();
    }
    Ok(entries)
}

/// The list ends at the first `]` followed only by whitespace and then the next entry or the end.
fn list_end(list: &str) -> Option<usize> {
    list.match_indices(']').map(|(i, _)| i).find(|&i| {
        let after = list[i + 1..].trim_start();
        after.is_empty() || after.starts_with('\'')
    })
}

/// Reject duplicates, axioms outside the allowlist, and any difference from the expected roots.
pub fn check(output: &str, expected: &[String]) -> Result<usize, AuditError> {
    let mut audited = BTreeSet::new();
    for (root, axioms) in parse(output)? {
        if !audited.insert(root.clone()) {
            return Err(AuditError::Duplicate(root));
        }
        let mut unexpected: Vec<String> = axioms
            .into_iter()
            .filter(|axiom| !ALLOWED_AXIOMS.contains(&axiom.as_str()))
            .collect();
        unexpected.sort();
        if !unexpected.is_empty() {
            return Err(AuditError::Unexpected(unexpected));
        }
    }
    let wanted: BTreeSet<String> = expected.iter().cloned().collect();
    let missing: Vec<String> = wanted.difference(&audited).cloned().collect();
    if !missing.is_empty() {
        return Err(AuditError::Missing(missing));
    }
    let unlisted: Vec<String> = audited.difference(&wanted).cloned().collect();
    if !unlisted.is_empty() {
        return Err(AuditError::Unlisted(unlisted));
    }
    Ok(audited.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roots(names: &[&str]) -> Vec<String> {
        names.iter().map(|n| n.to_string()).collect()
    }

    const OUTPUT: &str =
        "'Labyrinth.a' depends on axioms: [propext, Classical.choice, Quot.sound]\n\
        'Labyrinth.b' does not depend on any axioms\n";

    #[test]
    fn accepts_both_forms() {
        assert_eq!(
            check(OUTPUT, &roots(&["Labyrinth.a", "Labyrinth.b"])),
            Ok(2)
        );
    }

    #[test]
    fn names_with_apostrophe_question_mark_and_dots() {
        let out = "'Foo.bar'' depends on axioms: [propext]\n\
            'Foo.is_ok?' does not depend on any axioms\n\
            'A.B.c'_d' depends on axioms: [Quot.sound]\n";
        let expected = roots(&["Foo.bar'", "Foo.is_ok?", "A.B.c'_d"]);
        assert_eq!(check(out, &expected), Ok(3));
    }

    #[test]
    fn name_containing_the_fixed_suffix_start_is_still_split_at_the_first_suffix() {
        let out = "'x' y' does not depend on any axioms\n";
        assert_eq!(parse(out).unwrap(), vec![("x' y".to_owned(), vec![])]);
    }

    #[test]
    fn multi_line_axiom_list() {
        let out = "'T.t' depends on axioms: [propext,\n   Classical.choice,\n   Quot.sound]\n\
            'T.u' does not depend on any axioms";
        assert_eq!(check(out, &roots(&["T.t", "T.u"])), Ok(2));
    }

    #[test]
    fn unexpected_axiom_is_rejected() {
        let out = "'set_parent_spec' depends on axioms: [propext, unapproved_axiom]\n";
        assert_eq!(
            check(out, &roots(&["set_parent_spec"])),
            Err(AuditError::Unexpected(roots(&["unapproved_axiom"])))
        );
    }

    #[test]
    fn duplicate_root_is_rejected() {
        let out = format!("{OUTPUT}'Labyrinth.a' does not depend on any axioms\n");
        assert_eq!(
            check(&out, &roots(&["Labyrinth.a", "Labyrinth.b"])),
            Err(AuditError::Duplicate("Labyrinth.a".into()))
        );
    }

    #[test]
    fn missing_and_unlisted_roots_are_rejected() {
        assert_eq!(
            check(
                OUTPUT,
                &roots(&["Labyrinth.a", "Labyrinth.b", "Labyrinth.c"])
            ),
            Err(AuditError::Missing(roots(&["Labyrinth.c"])))
        );
        assert_eq!(
            check(OUTPUT, &roots(&["Labyrinth.a"])),
            Err(AuditError::Unlisted(roots(&["Labyrinth.b"])))
        );
    }

    #[test]
    fn stray_text_is_rejected() {
        for out in [
            "warning: x\n'a' does not depend on any axioms\n",
            "'a' does not depend on any axioms\ntrailing\n",
            "'a' depends on axioms: [propext\n",
            "'a' is something else\n",
        ] {
            assert!(matches!(parse(out), Err(AuditError::Malformed(_))), "{out}");
        }
    }

    #[test]
    fn empty_output_lists_every_root_as_missing() {
        assert_eq!(
            check("", &roots(&["a"])),
            Err(AuditError::Missing(roots(&["a"])))
        );
    }

    #[test]
    fn expected_roots_accept_any_identifier() {
        let src = "import X\n#print axioms A.b'\n#print axioms c?\n  #print axioms indented\n-- #print axioms no\n#print axioms «odd name»\n";
        assert_eq!(expected_roots(src), roots(&["A.b'", "c?", "«odd name»"]));
    }
}
