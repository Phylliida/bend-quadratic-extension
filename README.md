# bend-quadratic-extension

Formally verified quadratic extension library in [Bend](https://github.com/bendlang/bend) (Bend 2).

Spike status: exact integer arithmetic (`Int`, sign + magnitude over unary
`Nat`, canonical zero) with proved `add_comm`, `mul_comm`, `mul_assoc`,
`mul_swap`; a `Nat` lemma inventory (`add_comm`, `add_assoc`, `mul_distrib`,
`mul_assoc`, comparison-evidence bridges); and `QExt` (elements `re +
im*sqrt(d)`, radicand as an operation parameter) with proved `add_comm` and
`mul_comm`. All files check with `bend src/qext.bend` (or
`node bend2/main.ts src/qext.bend` from a bend checkout).

Known gaps, in dependency order: `Int.add_assoc` (needs a truncated-sub /
ordering lemma library), `Rat` (normalization needs gcd, which needs a
division proof), binary nats for performance (unary `Nat` is O(value)),
then the field axioms and ordering for `QExt`.
