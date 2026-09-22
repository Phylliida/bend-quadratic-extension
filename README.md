# bend-quadratic-extension

Formally verified quadratic extension library in [Bend](https://github.com/bendlang/bend) (Bend 2).

Spike status: exact integer arithmetic (`Int`, a `(pos, neg)` difference pair)
with the full ring law set proved — `add_comm`, `add_assoc`, `add_exchange`,
`add_zero`, `zero_add`, `neg_invol`, `neg_add`, `neg_mul`, `sub_eq_add_neg`,
`mul_comm`, `mul_assoc`, `mul_swap`, `mul_distrib`, `mul_add_left`,
`mul_zero`, `mul_one`, `one_mul`; a `Nat` lemma inventory (`add_comm`,
`add_assoc`, `add_exchange`, `mul_distrib`, `mul_assoc`, `mul_one`,
comparison-evidence bridges, the truncated-sub/ordering `ci*` family, and
division: the `Nat.divmod.go` loop invariant plus `div_add_mod`/`mod_lt`, and
`Nat.gcd` with both of its step-2 obligations — scaling *and* "divides both
arguments"); and `QExt` (elements `re + im*sqrt(d)`, radicand as an operation
parameter) with proved `add_comm` and `mul_comm`.

## Int is a presentation, not a canonical form

An `Int` is `Int{pos, neg}`, standing for `pos - neg`. Every operation is a
constructor built out of `Nat.add`/`Nat.mul`, so operations always compose and
every ring law above is a `Nat` semiring identity — no case analysis on sign
anywhere. The price is that `Int{1, 0}` and `Int{2, 1}` are both 1 and are
*not* `==`: `==` on `Int` does not decide equality. Deciding it is
`Int.canon`'s job, and it is needed only where a canonical representative
matters. The identities that name a specific representative of a value —
`x + (-x) = 0` above all — are therefore not `==` statements about `Int`, and
land with `Int.canon`.

The earlier sign-magnitude design (sign bit + magnitude, every op
canonicalizing through `Int.mk`) did have decidable `==`, but paid for it in
case analysis, and that case analysis is what the switch removed. See
`PROVING.md` for the measurement.

## Layout

Laws and proofs live in separate files; each `*_proofs.bend` fills every
law of its sibling via `def <alias>.<name>(...)`:

- `src/nat.bend` — the 101 Nat/Cmp laws (including the `Nat.divmod` and
  `Nat.gcd` blocks), plus `Cmp.flip`, the gcd defs and the `Nat.Div` witness
  type. No proofs.
- `src/nat_proofs.bend` — fills every nat.bend law; also hosts the
  proof-only machinery (`CmpIsEQ`, `CmpIsGT`, `NatIsPos`, `Nat.pred`).
- `src/int.bend` — `Int` type, the ops (`Int.zero`, `Int.one`, `Int.add`,
  `Int.neg`, `Int.sub`, `Int.mul`), `Int.canon` (the canonical
  representative, which is what makes `==` decide integer equality), and
  the Int laws.
- `src/int_proofs.bend` — fills every int.bend law (Nat evidence via
  nat.bend, filled by the nat_proofs.bend import).
- `src/qext.bend` — `QExt` type, `QExt.nat`/`add`/`mul`, and the two laws.
- `src/qext_proofs.bend` — fills both qext.bend laws.
- `scratch.bend` — smoke test with a `main`.

Check with `node bend2/main.ts <file>` from a bend checkout. The three
`*_proofs.bend` files and `scratch.bend` are the gates and print
`All terms check.`; the laws-only files intentionally fail with
`Error: N TODOs found.` (an open law is an unfilled TODO). The count is
transitive over imports: nat.bend 101, int.bend 22 (it imports only `Base`),
qext.bend 24 = 22 Int + 2 QExt.

Nat division is proved (`div_add_mod`, `mod_lt`), including the
`Nat.divmod.go` loop invariant it rests on.

`Nat.gcd` (subtractive Euclid, fuel-driven) is proved *natural under scaling*
(`gcd.go.scale`, `gcd.go.fuel`, `gcd_scale`) and proved to *divide both
arguments* (`gcd.go.divides`, with the two per-step assembly laws
`gcd.divides_lt`/`gcd.divides_gt`) — both step-2 obligations are closed. The
loop itself is defined in `src/nat.bend` (`Nat.gcd.go` / `Nat.gcd`); two errors
in the PROVING.md sketch were found and fixed there (see that file).

Known gaps, in dependency order:

1. `Int.canon.eqv` — the quotient lemma (`canon x == canon y` iff
   `xp + yn == yp + xn`) — and `Int.canon.scale`
   (`canon(x*k) == canon(x)*k`, `k >= 1`), which is what Rat normalization
   uses.
2. `Rat{num: Int, den: Nat}` with `Rat.mk` normalizing via `Int.canon` +
   gcd, then the field axioms. Canonicality is proved by the scaling route
   (`norm(n*k, d*k) == norm(n,d)`), which needs only the *forward*
   direction — "equal values have equal normal forms" — and therefore does
   not need coprime-ness or Euclid's lemma.
3. `QExt` over `Rat`: field axioms plus the multiplicative inverse
   (`1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)`).
4. Binary nats for performance (unary `Nat` is O(value)).
