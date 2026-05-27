//! Tiny predicate grammar for v0.2 spec preconditions.
//!
//! ## Grammar
//!
//! ```text
//! predicate := ws? ident ws? cmp_op ws? int_literal ws?
//!            | ws? int_literal ws? cmp_op ws? ident ws?
//! ident        := [a-zA-Z_] [a-zA-Z0-9_]*
//! cmp_op       := "<" | "<=" | ">" | ">=" | "==" | "!="
//! int_literal  := "-"? [0-9]+   (parsed as i128; range-checked at
//!                                  translation time against the target
//!                                  type)
//! ws           := whitespace
//! ```
//!
//! Both `x < 100` and `100 > x` parse to the same `Predicate`
//! (`{ var: "x", op: Lt, lit: 100 }`); the reversed form is
//! normalized via `CmpOp::flip` so downstream code only sees the
//! ident-first form.
//!
//! ## Why not full Rust expression syntax
//!
//! v0.2 covers ~80% of useful precondition shapes with this tiny
//! grammar. The shapes that require richer parsing — multiple
//! conjuncts, arithmetic on the right side, function calls — land
//! when we have a real expression IR. The conservative MVP keeps
//! the spec-translation TCB legible (`<50 LOC` for the parser
//! plus the SMT translator).
//!
//! ## Backward compat with O.1
//!
//! A precondition string that fails to parse as a predicate is
//! NOT a hard error — it falls back to the O.1 posture of
//! splicing as raw SMT-LIB. This lets users keep hand-written
//! SMT around for cases the grammar doesn't yet cover.
use serde::{Deserialize, Serialize};
/// A parsed precondition of the form `<ident> <cmp> <int>`. The
/// `var` always refers to a function parameter by source name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Predicate {
    /// Source name of the parameter the predicate constrains.
    pub var: String,
    /// Comparison operator (always normalized so `var` is on the
    /// left after `flip`-normalization at parse time).
    pub op: CmpOp,
    /// Integer literal the operator compares `var` against.
    /// Range-checked against the target type when translated to
    /// SMT-LIB; out-of-range literals produce a translation error,
    /// not silent truncation.
    pub lit: i128,
}
/// Comparison operators in our predicate grammar.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CmpOp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
    /// `==`
    Eq,
    /// `!=`
    Ne,
}
impl CmpOp {
    /// Flip the operator (i.e. `A op B` ⇔ `B (flip op) A`).
    /// Used to normalize reversed-form predicates to ident-first
    /// after parsing.
    #[must_use]
    pub fn flip(self) -> Self {
        match self {
            CmpOp::Lt => CmpOp::Gt,
            CmpOp::Le => CmpOp::Ge,
            CmpOp::Gt => CmpOp::Lt,
            CmpOp::Ge => CmpOp::Le,
            // Equality and inequality are symmetric.
            CmpOp::Eq => CmpOp::Eq,
            CmpOp::Ne => CmpOp::Ne,
        }
    }
}
/// Failure mode for `parse_predicate`. The caller surfaces this as
/// an audit note when the precondition originated from
/// `pitbull.toml` — silent rejection is exactly the anti-pattern
/// the v0.1 audit (C1/C2) said to avoid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// The original input string, copied so callers can report
    /// the offender without holding the borrow.
    pub input: String,
    /// Why the parse failed.
    pub reason: String,
}
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "predicate parse error: {} (input: {:?})", self.reason, self.input)
    }
}
impl std::error::Error for ParseError {}
/// Parse a predicate string. Returns `Err` if neither the
/// ident-first nor the literal-first form matches.
///
/// The grammar accepts arbitrary whitespace between tokens; the
/// operator must appear as a contiguous substring (e.g. `<=`
/// without a space between `<` and `=`).
pub fn parse_predicate(s: &str) -> Result<Predicate, ParseError> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(ParseError {
            input: s.to_string(),
            reason: "empty input".into(),
        });
    }
    // Order matters: two-char operators MUST be tried before their
    // one-char prefixes so `<=` isn't tokenized as `<` + `= ...`.
    const OPS: &[(&str, CmpOp)] = &[
        ("<=", CmpOp::Le),
        (">=", CmpOp::Ge),
        ("==", CmpOp::Eq),
        ("!=", CmpOp::Ne),
        ("<", CmpOp::Lt),
        (">", CmpOp::Gt),
    ];
    for (op_str, op) in OPS {
        if let Some(idx) = trimmed.find(op_str) {
            let left = trimmed[..idx].trim();
            let right = trimmed[idx + op_str.len()..].trim();
            // Try ident-first form: <left ident> <op> <right int>.
            if let (Some(var), Some(lit)) = (parse_ident(left), parse_int(right)) {
                return Ok(Predicate { var, op: *op, lit });
            }
            // Try reversed form: <left int> <op> <right ident>.
            // Normalize by flipping the operator.
            if let (Some(lit), Some(var)) = (parse_int(left), parse_ident(right)) {
                return Ok(Predicate { var, op: op.flip(), lit });
            }
            // The operator matched but neither orientation produced
            // a valid `ident OP int` parse. Don't fall through to a
            // different op — that risks tokenizing `<=` as `<` and
            // then misinterpreting the trailing `=`. Report the
            // specific failure for this operator and stop.
            return Err(ParseError {
                input: s.to_string(),
                reason: format!(
                    "matched operator `{op_str}` but operands don't \
                     form `<ident> {op_str} <int>` or `<int> {op_str} <ident>` \
                     (left: {:?}, right: {:?})",
                    left, right,
                ),
            });
        }
    }
    Err(ParseError {
        input: s.to_string(),
        reason: "no comparison operator found".into(),
    })
}
/// Validate an identifier per Rust's lexer (ASCII subset: starts
/// with letter or underscore, continues with alphanumerics or
/// underscores). Rejects empty strings.
fn parse_ident(s: &str) -> Option<String> {
    let first = s.chars().next()?;
    if !(first.is_ascii_alphabetic() || first == '_') {
        return None;
    }
    if !s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }
    Some(s.to_string())
}
/// Parse a decimal integer literal into `i128`. Accepts an
/// optional leading `-`. Rejects suffixes (`100u32`) and
/// non-decimal bases (`0x...`, `0b...`).
fn parse_int(s: &str) -> Option<i128> {
    s.parse::<i128>().ok()
}
/// Failure mode for `validate_assertion_form` — the lex validator
/// the visitor runs on raw-SMT-LIB precondition strings (the
/// O.1 escape hatch). v0.2 red-team finding F2: a maliciously
/// crafted assumption could carry multiple top-level directives
/// (`"(check-sat) (assert false)"`) that subvert the wrapper's
/// solver-verdict interpretation. The validator forces every
/// raw assumption to be exactly one `(assert ...)` form with
/// balanced parens and nothing else — strings or comments are
/// rejected to avoid lexer ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssertionFormError {
    /// Input was empty or whitespace.
    Empty,
    /// First non-whitespace token wasn't `(assert`.
    NotAssertForm,
    /// Parens don't balance (too many opens or too many closes).
    UnbalancedParens,
    /// Multiple top-level directives — content appears after the
    /// first balanced close. Defeats the multi-directive injection
    /// path documented in the v0.2 red-team.
    MultipleDirectives,
    /// Contains a `"` character — string-literal handling would
    /// require a proper tokenizer (parens inside strings don't
    /// nest). Rejected for now.
    StringLiteralNotSupported,
    /// Contains a `;` character — SMT-LIB comments could mask
    /// paren imbalance. Rejected for now.
    CommentNotSupported,
    /// Contains a `|` character — SMT-LIB quoted-symbol syntax
    /// `|...|` ignores parens inside, but our byte-level paren
    /// counter doesn't. A crafted precondition can therefore
    /// validate as a single balanced `(assert ...)` form here
    /// while Z3 sees multiple directives (audit finding H-RT1,
    /// 2026-05-26). Rejected wholesale — Pitbull's own emitted
    /// assumptions never need `|` (predicate-translated forms
    /// use `bvult/bvslt/=/distinct` with hex literals; constant
    /// pins use `=` with hex literals).
    QuotedSymbolNotSupported,
}
impl std::fmt::Display for AssertionFormError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "empty or whitespace-only"),
            Self::NotAssertForm => write!(f, "must start with `(assert`"),
            Self::UnbalancedParens => write!(f, "parens not balanced"),
            Self::MultipleDirectives => write!(f, "must be exactly one top-level directive"),
            Self::StringLiteralNotSupported => write!(f, "string literals not supported"),
            Self::CommentNotSupported => write!(f, "comments not supported"),
            Self::QuotedSymbolNotSupported => {
                write!(f, "quoted-symbol syntax `|...|` not supported (audit finding H-RT1)")
            }
        }
    }
}
impl std::error::Error for AssertionFormError {}
/// Lex-validate a raw assumption string as a single SMT-LIB 2
/// `(assert ...)` directive.
///
/// This is a deliberate restriction, narrower than the SMT-LIB
/// grammar: the validator rejects string literals (`"..."`) and
/// comments (`;...`) outright. Real Pitbull assumptions never
/// need either — predicate-translated forms are
/// `(assert (bvXXX lhs|rhs #x...))` and human-written
/// assumptions for our use case are similar bit-vector
/// constraints. The narrow grammar makes paren-balancing
/// unambiguous and forecloses the multi-directive injection
/// vector (red-team finding F2).
///
/// Returns `Ok(())` for valid input, otherwise a specific error
/// that the caller surfaces to the auditor.
pub fn validate_assertion_form(s: &str) -> Result<(), AssertionFormError> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(AssertionFormError::Empty);
    }
    // Reject string literals and comments wholesale — they require
    // tokenizer state we don't have, and they aren't needed for
    // Pitbull's bit-vector assumption shapes.
    if trimmed.contains('"') {
        return Err(AssertionFormError::StringLiteralNotSupported);
    }
    if trimmed.contains(';') {
        return Err(AssertionFormError::CommentNotSupported);
    }
    // Audit finding H-RT1 (2026-05-26): SMT-LIB quoted-symbol
    // syntax `|...|` lets ANY character (except `|` and `\`)
    // appear inside, including unmatched parens. Our byte-level
    // paren scanner counts every `(` and `)` literally, so a
    // crafted precondition like
    //   `(assert (= 1 |))(check-sat)(assert false|))`
    // can byte-balance correctly while Z3 sees three directives:
    // `(assert (= 1 |...|))`, `(check-sat)`, `(assert false|...|))`.
    // The validator's "single (assert ...) form" promise is broken.
    // Pitbull's own assumption synthesis (predicate translation,
    // operand pin) never emits `|`, so rejecting it wholesale
    // closes the injection path with zero legitimate-use cost.
    if trimmed.contains('|') {
        return Err(AssertionFormError::QuotedSymbolNotSupported);
    }
    if !trimmed.starts_with("(assert") {
        return Err(AssertionFormError::NotAssertForm);
    }
    // After `(assert` the next char must be whitespace or `(` so
    // we don't accidentally accept `(assertion ...)` or similar.
    let after_keyword = &trimmed["(assert".len()..];
    match after_keyword.chars().next() {
        Some(c) if c.is_whitespace() || c == '(' => {}
        _ => return Err(AssertionFormError::NotAssertForm),
    }
    // Paren-balance scan. The first balanced close ends the
    // single top-level directive; anything after must be
    // whitespace only.
    let mut depth: i32 = 0;
    let mut closed_at: Option<usize> = None;
    for (idx, ch) in trimmed.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return Err(AssertionFormError::UnbalancedParens);
                }
                if depth == 0 && closed_at.is_none() {
                    closed_at = Some(idx + ch.len_utf8());
                }
            }
            _ => {}
        }
    }
    if depth != 0 {
        return Err(AssertionFormError::UnbalancedParens);
    }
    let end = closed_at.ok_or(AssertionFormError::UnbalancedParens)?;
    if !trimmed[end..].trim().is_empty() {
        return Err(AssertionFormError::MultipleDirectives);
    }
    Ok(())
}
/// Translation failure for `predicate_to_smt_assertion`. The
/// caller surfaces this as an audit note (silent rejection is
/// the anti-pattern the v0.1 audit forbids).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranslationError {
    /// Operand type name (e.g. `"f32"`) isn't a primitive integer
    /// the SMT bit-vector encoding can express.
    UnsupportedType {
        /// The offending type name passed by the caller.
        ty_name: String,
    },
    /// Literal doesn't fit the target type's range. Catches the
    /// pathological case where a user writes `x < 999999999999`
    /// for a `u8` parameter — the SMT bit-vector would silently
    /// truncate the literal, weakening the precondition without
    /// telling anyone.
    LiteralOutOfRange {
        /// The out-of-range literal from the predicate.
        lit: i128,
        /// The target type the literal couldn't fit.
        ty_name: String,
    },
}
impl std::fmt::Display for TranslationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TranslationError::UnsupportedType { ty_name } => {
                write!(f, "predicate translation: unsupported type `{ty_name}`")
            }
            TranslationError::LiteralOutOfRange { lit, ty_name } => {
                write!(
                    f,
                    "predicate translation: literal {lit} out of range for `{ty_name}`",
                )
            }
        }
    }
}
impl std::error::Error for TranslationError {}
/// Translate a parsed predicate into an SMT-LIB 2 `(assert ...)`
/// directive that constrains `operand_smt_name` (typically `"lhs"`
/// or `"rhs"` — the variables declared in the overflow problem).
///
/// `target_ty_name` is the Rust primitive integer name (`"u32"`,
/// `"i64"`, etc.). It determines:
/// - Whether to use unsigned or signed BV predicates
///   (`bvult` vs `bvslt`, etc.).
/// - The bit-vector width.
/// - The legal literal range — values outside the type's range
///   produce `LiteralOutOfRange` rather than silent two's-complement
///   wraparound.
///
/// Equality (`==`) and inequality (`!=`) use SMT-LIB's `=` and
/// `distinct` directly — they don't have signed/unsigned variants.
pub fn predicate_to_smt_assertion(
    pred: &Predicate,
    operand_smt_name: &str,
    target_ty_name: &str,
) -> Result<String, TranslationError> {
    let (signed, bits) = int_type_info(target_ty_name)
        .ok_or_else(|| TranslationError::UnsupportedType {
            ty_name: target_ty_name.to_string(),
        })?;
    // Range check. The legal range for `u<bits>` is [0, 2^bits - 1];
    // for `i<bits>` it's [-2^(bits-1), 2^(bits-1) - 1]. We compute
    // via i128 to handle every supported width up through i128
    // / u64 without overflow. (u128 max doesn't fit in i128 — see
    // the `u128` arm below.)
    let (min, max) = legal_range_i128(signed, bits)
        .ok_or_else(|| TranslationError::UnsupportedType {
            ty_name: target_ty_name.to_string(),
        })?;
    if pred.lit < min || pred.lit > max {
        return Err(TranslationError::LiteralOutOfRange {
            lit: pred.lit,
            ty_name: target_ty_name.to_string(),
        });
    }
    let smt_op = match (pred.op, signed) {
        (CmpOp::Lt, false) => "bvult",
        (CmpOp::Lt, true) => "bvslt",
        (CmpOp::Le, false) => "bvule",
        (CmpOp::Le, true) => "bvsle",
        (CmpOp::Gt, false) => "bvugt",
        (CmpOp::Gt, true) => "bvsgt",
        (CmpOp::Ge, false) => "bvuge",
        (CmpOp::Ge, true) => "bvsge",
        // Bit-vector equality doesn't have signed/unsigned forms.
        (CmpOp::Eq, _) => "=",
        (CmpOp::Ne, _) => "distinct",
    };
    let lit_smt = format_bv_literal(pred.lit, bits);
    Ok(format!("(assert ({smt_op} {operand_smt_name} {lit_smt}))"))
}
/// Emit an SMT-LIB `(assert (= <operand> <bv-literal>))` directive
/// that pins a constant operand's value in a bit-vector problem.
///
/// O.2.5: the visitor uses this to constrain known-value
/// constant operands like the `1` in `x + 1`. Before O.2.5, such
/// constants were free `BitVec N` variables from the solver's
/// perspective — overflow obligations with preconditions on `x`
/// still returned `sat` because `rhs` could be anything. Pinning
/// `rhs = 1` makes the check decidable.
///
/// The literal is two's-complement-encoded against the target
/// width, so unsigned values that wrapped to negative `i128`
/// during extraction (only possible for `u128` > `i128::MAX`)
/// round-trip to the correct bit pattern.
///
/// Returns `None` for unsupported types — matches the rest of
/// the module's behavior. Range-checking is intentionally skipped
/// because the value came from a real MIR constant whose type
/// is already that of the operand; out-of-range here would mean
/// a bug in the adapter or the type-resolution chain, not a
/// user error.
#[must_use]
pub fn operand_pin_assertion(
    operand_smt_name: &str,
    value: i128,
    target_ty_name: &str,
) -> Option<String> {
    let (_signed, bits) = int_type_info(target_ty_name)?;
    let lit = format_bv_literal(value, bits);
    Some(format!("(assert (= {operand_smt_name} {lit}))"))
}
/// Decode a Rust primitive integer type name into (signed, bits).
/// Returns `None` for non-int types, suffixes, or unsupported widths.
fn int_type_info(name: &str) -> Option<(bool, u32)> {
    let (signed, rest) = if let Some(r) = name.strip_prefix('u') {
        (false, r)
    } else if let Some(r) = name.strip_prefix('i') {
        (true, r)
    } else {
        return None;
    };
    let bits = match rest {
        "8" => 8,
        "16" => 16,
        "32" => 32,
        "64" => 64,
        "128" => 128,
        // usize/isize: see comment in `pitbull_vc::smt`. v0.2 scaffold
        // defers them pending the target-pointer-width threading.
        _ => return None,
    };
    Some((signed, bits))
}
/// Legal value range for `i<bits>` or `u<bits>` as `i128`.
/// Returns `None` for `u128` (its max doesn't fit `i128::MAX`)
/// and for any width the `i128` arithmetic can't represent.
///
/// Audit-cleanup #4 / red-team F3: an earlier version computed
/// `1i128.checked_shl(127)` for signed-128, which returned
/// `Some(i128::MIN)` — then `-i128::MIN` panicked in debug and
/// wrapped in release, producing a wrong range. The fix
/// special-cases `i128` to the full i128 range (which is exactly
/// what the predicate IR can express — `lit: i128`).
fn legal_range_i128(signed: bool, bits: u32) -> Option<(i128, i128)> {
    match (signed, bits) {
        // i128: the full i128 range matches the predicate IR
        // literal type one-to-one. No shifts needed.
        (true, 128) => Some((i128::MIN, i128::MAX)),
        // Other signed widths: standard two's-complement range.
        (true, _) => {
            let half = 1i128.checked_shl(bits - 1)?;
            Some((-half, half - 1))
        }
        // u128::MAX = 2^128 - 1 > i128::MAX. The predicate IR
        // uses i128 literals so cannot express u128 bounds today.
        // Caller reports as UnsupportedType rather than truncating.
        (false, 128) => None,
        (false, _) => {
            let max = (1i128 << bits) - 1;
            Some((0, max))
        }
    }
}
/// Format an `i128` value as an SMT-LIB bit-vector literal of the
/// given width. Negative values get two's-complement-encoded.
fn format_bv_literal(lit: i128, bits: u32) -> String {
    // Two's-complement mask. The integer cast does the encoding
    // because Rust's `as u128` on a negative i128 produces the
    // wrapping representation, which is exactly what we want.
    #[allow(clippy::cast_sign_loss)]
    let raw_u128 = lit as u128;
    let mask: u128 = if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    let masked = raw_u128 & mask;
    // Prefer the hex form when `bits` is a multiple of 4 (the
    // common case for u8/u16/u32/u64/u128 and their signed
    // counterparts) — it reads identical to the standard "0xCAFE"
    // notation in source. Fall back to `(_ bv<value> <bits>)` for
    // non-multiple-of-4 widths.
    if bits.is_multiple_of(4) {
        let hex_chars = (bits / 4) as usize;
        format!("#x{masked:0hex_chars$X}")
    } else {
        format!("(_ bv{masked} {bits})")
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    /// Pin every operator's parse. A change to operator semantics
    /// is a breaking spec-language change — must surface in review.
    #[test]
    fn parses_every_operator() {
        let cases = [
            ("x < 100", CmpOp::Lt, "x", 100),
            ("x <= 100", CmpOp::Le, "x", 100),
            ("x > 100", CmpOp::Gt, "x", 100),
            ("x >= 100", CmpOp::Ge, "x", 100),
            ("x == 100", CmpOp::Eq, "x", 100),
            ("x != 100", CmpOp::Ne, "x", 100),
        ];
        for (input, expected_op, expected_var, expected_lit) in cases {
            let p = parse_predicate(input).expect(input);
            assert_eq!(p.op, expected_op, "op mismatch on {input:?}");
            assert_eq!(p.var, expected_var, "var mismatch on {input:?}");
            assert_eq!(p.lit, expected_lit, "lit mismatch on {input:?}");
        }
    }
    /// Reversed form (`100 > x`) normalizes to ident-first via
    /// `flip`. Pins the normalization: downstream code never has
    /// to handle the literal-first orientation.
    #[test]
    fn parses_reversed_form_normalized_to_ident_first() {
        let p = parse_predicate("100 > x").expect("reversed parses");
        assert_eq!(p.var, "x");
        assert_eq!(p.op, CmpOp::Lt, "100 > x means x < 100");
        assert_eq!(p.lit, 100);
    }
    /// Negative literals (relevant for signed types). `i32` can
    /// legitimately have preconditions like `x > -10`.
    #[test]
    fn parses_negative_literals() {
        let p = parse_predicate("x >= -10").expect("negative literal parses");
        assert_eq!(p.var, "x");
        assert_eq!(p.op, CmpOp::Ge);
        assert_eq!(p.lit, -10);
    }
    /// Whitespace flexibility: leading, trailing, and around
    /// operators must all be tolerated.
    #[test]
    fn whitespace_flexibility() {
        let canonical = parse_predicate("x < 100").expect("canonical parses");
        for input in ["x<100", "  x  <  100  ", "x  <100", "x<  100"] {
            let p = parse_predicate(input).expect(input);
            assert_eq!(p, canonical, "whitespace variant should normalize: {input:?}");
        }
    }
    /// Two-character operators take precedence over their one-char
    /// prefixes. Pins the tokenization order in `OPS`.
    #[test]
    fn two_char_ops_take_precedence() {
        let p = parse_predicate("x <= 5").expect("<= parses");
        assert_eq!(p.op, CmpOp::Le);
        let p = parse_predicate("x >= 5").expect(">= parses");
        assert_eq!(p.op, CmpOp::Ge);
        let p = parse_predicate("x == 5").expect("== parses");
        assert_eq!(p.op, CmpOp::Eq);
        let p = parse_predicate("x != 5").expect("!= parses");
        assert_eq!(p.op, CmpOp::Ne);
    }
    /// Underscore-prefixed identifiers and identifiers with
    /// digits are valid (matching Rust's lexer subset).
    #[test]
    fn ident_allows_underscores_and_digits_after_first() {
        let p = parse_predicate("_x < 5").expect("underscore prefix");
        assert_eq!(p.var, "_x");
        let p = parse_predicate("arg_2 < 5").expect("ident with digit");
        assert_eq!(p.var, "arg_2");
    }
    /// Malformed inputs surface a `ParseError` with the original
    /// input embedded — caller can report context to the auditor.
    #[test]
    fn malformed_inputs_return_errors() {
        for input in [
            "",                  // empty
            "   ",               // whitespace only
            "x",                 // no operator
            "x <",               // missing right operand
            "< 5",               // missing left operand
            "x < y",             // var on both sides (we want ident < int or int < ident)
            "5 < 10",            // int on both sides
            "1x < 5",            // ident starts with digit
            "x.y < 5",           // ident with `.`
            "x < 100u32",        // suffixed literal
            "x < 0x64",          // hex literal
        ] {
            assert!(
                parse_predicate(input).is_err(),
                "expected parse failure on {input:?}",
            );
        }
    }
    /// Operator-found-but-operands-broken produces a specific
    /// error rather than silently falling through to another
    /// operator (which would misinterpret `<=` as `<`).
    #[test]
    fn matched_op_with_bad_operands_does_not_fall_through() {
        let err = parse_predicate("<= 5").expect_err("missing left operand");
        assert!(
            err.reason.contains("matched operator `<=`"),
            "should pin the specific operator that matched; got {:?}",
            err.reason,
        );
    }
    // ----- translator tests -------------------------------------------
    /// `x < 100` against `u32` lhs produces an unsigned BV
    /// less-than predicate with the 32-bit hex literal.
    #[test]
    fn translates_u32_lt() {
        let p = Predicate { var: "x".into(), op: CmpOp::Lt, lit: 100 };
        let smt = predicate_to_smt_assertion(&p, "lhs", "u32")
            .expect("u32 supported");
        assert_eq!(smt, "(assert (bvult lhs #x00000064))");
    }
    /// Signed types use bvslt/bvsle/bvsgt/bvsge.
    #[test]
    fn translates_i32_gt_uses_signed_predicate() {
        let p = Predicate { var: "x".into(), op: CmpOp::Gt, lit: -10 };
        let smt = predicate_to_smt_assertion(&p, "rhs", "i32")
            .expect("i32 supported");
        assert!(
            smt.contains("bvsgt"),
            "signed types must use bvsgt for `>`; got {smt}",
        );
    }
    /// Negative literals on signed types two's-complement-encode.
    /// -1 in i8 is 0xFF; in i32 is 0xFFFFFFFF.
    #[test]
    fn negative_literals_use_twos_complement_encoding() {
        let p = Predicate { var: "x".into(), op: CmpOp::Eq, lit: -1 };
        let smt_i8 = predicate_to_smt_assertion(&p, "lhs", "i8")
            .expect("i8 supported");
        assert!(
            smt_i8.contains("#xFF"),
            "i8 -1 should encode as #xFF; got {smt_i8}",
        );
        let smt_i32 = predicate_to_smt_assertion(&p, "lhs", "i32")
            .expect("i32 supported");
        assert!(
            smt_i32.contains("#xFFFFFFFF"),
            "i32 -1 should encode as #xFFFFFFFF; got {smt_i32}",
        );
    }
    /// `==` and `!=` use SMT-LIB `=` and `distinct` — no
    /// signed/unsigned distinction for equality.
    #[test]
    fn equality_uses_bv_equality_not_bvueq() {
        let pe = Predicate { var: "x".into(), op: CmpOp::Eq, lit: 42 };
        let smt = predicate_to_smt_assertion(&pe, "lhs", "u32")
            .expect("u32 supported");
        assert!(
            smt.contains("(assert (= lhs"),
            "equality should be `=`; got {smt}",
        );
        let pn = Predicate { var: "x".into(), op: CmpOp::Ne, lit: 42 };
        let smt = predicate_to_smt_assertion(&pn, "lhs", "u32")
            .expect("u32 supported");
        assert!(
            smt.contains("(assert (distinct lhs"),
            "inequality should be `distinct`; got {smt}",
        );
    }
    /// Out-of-range literals must produce a translation error,
    /// not a silently-truncated SMT assertion. Catches the case
    /// where a user writes `x < 999_999` for a `u8` parameter.
    #[test]
    fn out_of_range_literal_rejected() {
        let p = Predicate { var: "x".into(), op: CmpOp::Lt, lit: 1_000_000 };
        let err = predicate_to_smt_assertion(&p, "lhs", "u8")
            .expect_err("u8 cannot hold 1M");
        match err {
            TranslationError::LiteralOutOfRange { lit, ty_name } => {
                assert_eq!(lit, 1_000_000);
                assert_eq!(ty_name, "u8");
            }
            other => panic!("expected LiteralOutOfRange, got {other:?}"),
        }
    }
    /// Negative literals against unsigned types are out-of-range
    /// (`u32::MIN == 0`). Reject with `LiteralOutOfRange`.
    #[test]
    fn negative_literal_against_unsigned_type_rejected() {
        let p = Predicate { var: "x".into(), op: CmpOp::Gt, lit: -1 };
        let err = predicate_to_smt_assertion(&p, "lhs", "u32")
            .expect_err("u32 has no negative range");
        assert!(matches!(err, TranslationError::LiteralOutOfRange { .. }));
    }
    /// Unsupported types (`f32`, `bool`, usize until v0.3) return
    /// `UnsupportedType`.
    #[test]
    fn unsupported_type_rejected() {
        let p = Predicate { var: "x".into(), op: CmpOp::Lt, lit: 0 };
        for ty in ["f32", "bool", "usize", "isize", "u3", "i256"] {
            let err = predicate_to_smt_assertion(&p, "lhs", ty)
                .expect_err(ty);
            assert!(matches!(err, TranslationError::UnsupportedType { .. }));
        }
    }
    /// O.2.5: `operand_pin_assertion` emits a properly-encoded
    /// `(assert (= <pos> <bv-lit>))` directive for known-value
    /// constant operands. Pins both the format and the
    /// two's-complement encoding for negative values.
    #[test]
    fn operand_pin_assertion_basic() {
        let s = operand_pin_assertion("rhs", 1, "u32")
            .expect("u32 supported");
        assert_eq!(s, "(assert (= rhs #x00000001))");
        let s = operand_pin_assertion("lhs", 42, "i64")
            .expect("i64 supported");
        assert_eq!(s, "(assert (= lhs #x000000000000002A))");
        // Negative literal on signed type → two's complement.
        let s = operand_pin_assertion("rhs", -1, "i32")
            .expect("i32 supported");
        assert_eq!(s, "(assert (= rhs #xFFFFFFFF))");
        // Negative literal on unsigned type would round-trip as
        // the same bit pattern — the encoder doesn't range-check
        // (that's by design; the visitor only feeds values
        // extracted from real MIR constants of that type).
        let s = operand_pin_assertion("lhs", -1, "u32")
            .expect("u32 supported");
        assert_eq!(s, "(assert (= lhs #xFFFFFFFF))");
    }
    /// Unsupported types return None without error.
    #[test]
    fn operand_pin_assertion_rejects_unsupported_types() {
        for ty in ["f32", "bool", "usize", "isize", "Bogus"] {
            assert!(
                operand_pin_assertion("lhs", 0, ty).is_none(),
                "unsupported type `{ty}` should return None",
            );
        }
    }
    /// Audit-cleanup F3: i128 predicates translate cleanly without
    /// the off-by-one overflow that broke `legal_range_i128`
    /// before the fix. A non-trivial test: a negative literal
    /// (which exercises two's-complement encoding) and a
    /// boundary literal (i128::MIN, the value that overflowed).
    #[test]
    fn i128_predicates_translate_cleanly() {
        let p_neg = Predicate { var: "x".into(), op: CmpOp::Gt, lit: -1_000_000 };
        let smt = predicate_to_smt_assertion(&p_neg, "lhs", "i128")
            .expect("i128 with negative literal supported");
        assert!(smt.contains("bvsgt"), "signed-128 must use bvsgt; got {smt}");
        // i128::MIN must NOT be out-of-range (the bug we fixed).
        let p_min = Predicate { var: "x".into(), op: CmpOp::Eq, lit: i128::MIN };
        let _smt = predicate_to_smt_assertion(&p_min, "lhs", "i128")
            .expect("i128 must accept i128::MIN");
        // i128::MAX likewise.
        let p_max = Predicate { var: "x".into(), op: CmpOp::Eq, lit: i128::MAX };
        let _smt = predicate_to_smt_assertion(&p_max, "lhs", "i128")
            .expect("i128 must accept i128::MAX");
    }
    /// rhs binding works the same as lhs — the operand name is
    /// just a label in the produced SMT.
    #[test]
    fn rhs_binding_changes_emitted_label() {
        let p = Predicate { var: "x".into(), op: CmpOp::Lt, lit: 100 };
        let smt = predicate_to_smt_assertion(&p, "rhs", "u32")
            .expect("rhs label");
        assert_eq!(smt, "(assert (bvult rhs #x00000064))");
    }
    // ----- assertion-form validator (red-team F2) ---------------------
    /// Predicate-translated forms always validate. Pin a few.
    #[test]
    fn validate_accepts_predicate_translated_forms() {
        for ok in [
            "(assert (bvult lhs #x00000064))",
            "(assert (bvsgt rhs #xFFFFFFFF))",
            "(assert (= lhs #x00000042))",
            "(assert (distinct rhs #x00000007))",
            "(assert (bvule lhs (_ bv1 32)))",
            "  (assert (bvult lhs #x64))  ",   // surrounding whitespace
        ] {
            assert!(
                validate_assertion_form(ok).is_ok(),
                "valid assumption rejected: {ok:?}",
            );
        }
    }
    /// The red-team attack vector: multi-directive injection. Each
    /// of these would have leaked through O.1's verbatim splice.
    #[test]
    fn validate_rejects_multi_directive_injection() {
        for bad in [
            "(check-sat) (assert false)",
            "(assert false) (check-sat)",
            "(assert (bvult lhs #x64)) (assert false)",
            "(push) (assert false) (pop)",
            "(define-fun evil () Bool false) (assert evil)",
        ] {
            let err = validate_assertion_form(bad).expect_err(bad);
            assert!(
                matches!(
                    err,
                    AssertionFormError::MultipleDirectives
                        | AssertionFormError::NotAssertForm,
                ),
                "multi-directive `{bad:?}` should be rejected; got {err:?}",
            );
        }
    }
    /// Unbalanced parens — defeats one form of paren-spoofing.
    #[test]
    fn validate_rejects_unbalanced_parens() {
        for bad in [
            "(assert (bvult lhs #x64)",   // one too few closes
            "(assert (bvult lhs #x64)))", // one too many closes
            "(assert ",                   // truncated
            "assert (foo))",              // missing leading paren
        ] {
            assert!(
                validate_assertion_form(bad).is_err(),
                "unbalanced/malformed accepted: {bad:?}",
            );
        }
    }
    /// Strings and comments rejected — both create lex ambiguity
    /// the simple validator can't handle. Real assumptions don't
    /// need either.
    #[test]
    fn validate_rejects_strings_and_comments() {
        assert!(matches!(
            validate_assertion_form("(assert (= name \"foo\"))"),
            Err(AssertionFormError::StringLiteralNotSupported),
        ));
        assert!(matches!(
            validate_assertion_form("(assert true) ; trailing comment"),
            Err(AssertionFormError::CommentNotSupported),
        ));
    }
    /// Audit finding H-RT1 (2026-05-26): SMT-LIB quoted-symbol
    /// syntax `|...|` defeats the byte-level paren scanner. A
    /// crafted precondition can pass the validator's "single
    /// (assert ...) form" check while Z3 sees multi-directive
    /// injection. Reject all `|` characters wholesale.
    #[test]
    fn validate_rejects_quoted_symbol_syntax() {
        // The textbook attack from H-RT1: byte-scan sees balanced
        // `(assert ...)`; Z3 sees three top-level directives.
        let attack = r"(assert (= 1 |))(check-sat)(assert false|))";
        assert!(
            matches!(
                validate_assertion_form(attack),
                Err(AssertionFormError::QuotedSymbolNotSupported),
            ),
            "H-RT1 attack payload must be rejected; got: {:?}",
            validate_assertion_form(attack),
        );
        // Even benign-looking quoted-symbol uses are rejected —
        // the wholesale ban is the simplest sound defense.
        for benign in [
            r"(assert (bvult |i| #x64))",        // quoted ident
            r"(assert (= |my var| #x01))",       // quoted with space
            r"(assert |raw|)",                    // bare quoted
        ] {
            assert!(
                matches!(
                    validate_assertion_form(benign),
                    Err(AssertionFormError::QuotedSymbolNotSupported),
                ),
                "quoted-symbol form must be rejected uniformly; \
                 input: {benign:?} got: {:?}",
                validate_assertion_form(benign),
            );
        }
    }
    /// `(assertion ...)` (typo-like) rejected because the keyword
    /// must end before the next char.
    #[test]
    fn validate_rejects_assert_lookalike_keywords() {
        for bad in ["(assertion 5)", "(assertfoo)", "(check-sat)"] {
            let err = validate_assertion_form(bad).expect_err(bad);
            assert!(matches!(err, AssertionFormError::NotAssertForm));
        }
    }
    /// Empty input rejected.
    #[test]
    fn validate_rejects_empty() {
        for bad in ["", "   ", "\t\n"] {
            assert!(matches!(
                validate_assertion_form(bad),
                Err(AssertionFormError::Empty),
            ));
        }
    }
}
