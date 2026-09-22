# bend-quadratic-extension

Formally verified quadratic extension library in [Bend](https://github.com/bendlang/bend) (Bend 2).

Spike status: exact integer arithmetic (`Int`, sign + magnitude over unary
`Nat`, canonical zero) with proved `add_comm`, `mul_comm`, `mul_assoc`,
`mul_swap`; a `Nat` lemma inventory (`add_comm`, `add_assoc`, `mul_distrib`,
`mul_assoc`, comparison-evidence bridges); and `QExt` (elements `re +
im*sqrt(d)`, radicand as an operation parameter) with proved `add_comm` and
`mul_comm`.

## Layout

Laws and proofs live in separate files; each `*_proofs.bend` fills every
law of its sibling via `def <alias>.<name>(...)`:

- `src/nat.bend` — the 78 Nat/Cmp laws, plus `Cmp.flip` (used in law
  statements). No proofs.
- `src/nat_proofs.bend` — fills every nat.bend law; also hosts the
  proof-only machinery (`CmpIsEQ`, `CmpIsGT`, `NatIsPos`, `Nat.pred`).
- `src/int.bend` — `Int` type, the ops (`Int.mk`, `Int.add.same`,
  `Int.add.opp`, `Int.add.go`, `Int.add`, `Int.mul`), and the Int laws.
- `src/int_proofs.bend` — fills every int.bend law (Nat evidence via
  nat.bend, filled by the nat_proofs.bend import).
- `src/qext.bend` — `QExt` type, `QExt.nat`/`add`/`mul`, and the two laws.
- `src/qext_proofs.bend` — fills both qext.bend laws.
- `scratch.bend` — smoke test with a `main`.

Check with `node bend2/main.ts <file>` from a bend checkout. The three
`*_proofs.bend` files and `scratch.bend` are the gates and print
`All terms check.`; the laws-only files intentionally fail with
`Error: N TODOs found.` (an open law is an unfilled TODO).

Known gaps, in dependency order: `Int.add_assoc` (needs a truncated-sub /
ordering lemma library), `Rat` (normalization needs gcd, which needs a
division proof), binary nats for performance (unary `Nat` is O(value)),
then the field axioms and ordering for `QExt`.
