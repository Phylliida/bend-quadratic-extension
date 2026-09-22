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

- `src/nat.bend` — the 124 Nat/Cmp laws (including the `Nat.divmod` and
  `Nat.gcd` blocks, the exact-division block, the difference-pair helpers, the
  scaling/divisibility bridges, `div_cross` -- the exact-division cross
  product the Rat value lemma is built from -- and the cross-sum lemmas the Int
  quotient lemma rests on),
  plus `Cmp.flip`, the gcd defs and the `Nat.Div` witness type. No proofs.
- `src/nat_proofs.bend` — fills every nat.bend law; also hosts the
  proof-only machinery (`CmpIsEQ`, `CmpIsGT`, `NatIsPos`, `Nat.pred`).
- `src/int.bend` — `Int` type, the ops (`Int.zero`, `Int.one`, `Int.add`,
  `Int.neg`, `Int.sub`, `Int.mul`), `Int.canon` (the canonical
  representative, which is what makes `==` decide integer equality), and
  the Int laws — including `Int.mul_scale`, the shape law that unfolds the raw
  scaling spelling `Int.mul(x, Int{d, 0n})` into the coordinate pair
  `(xp*d, xn*d)` the Rat value lemma is stated in.
- `src/int_proofs.bend` — fills every int.bend law (Nat evidence via
  nat.bend, filled by the nat_proofs.bend import).
- `src/qext.bend` — `QExt` type, `QExt.nat`/`add`/`mul`, and the two laws.
- `src/qext_proofs.bend` — fills both qext.bend laws.
- `src/rat.bend` — `Rat{num, den}` with the field projections `Rat.numof` /
  `Rat.denof`, `Rat.mk` (gcd normalization, match-free),
  `Rat.add`/`neg`/`sub`/`mul`/`zero`/`one`, and the laws.
- `src/rat_proofs.bend` — fills every rat.bend law.
- `scratch.bend` — smoke test with a `main`.

Check with `node bend2/main.ts <file>` from a bend checkout. The four
`*_proofs.bend` files and `scratch.bend` are the gates and print
`All terms check.`; the laws-only files intentionally fail with
`Error: N TODOs found.` (an open law is an unfilled TODO). The count is
transitive over imports: nat.bend 124, int.bend 32, qext.bend 34 = 32 Int + 2
QExt, rat.bend 182 = 124 Nat + 32 Int + 26 Rat.

Nat division is proved (`div_add_mod`, `mod_lt`), including the
`Nat.divmod.go` loop invariant it rests on.

`Nat.gcd` (subtractive Euclid, fuel-driven) is proved *natural under scaling*
(`gcd.go.scale`, `gcd.go.fuel`, `gcd_scale`) and proved to *divide both
arguments* (`gcd.go.divides`, with the two per-step assembly laws
`gcd.divides_lt`/`gcd.divides_gt`) — both step-2 obligations are closed. The
loop itself is defined in `src/nat.bend` (`Nat.gcd.go` / `Nat.gcd`); two errors
in the PROVING.md sketch were found and fixed there (see that file).

`Int.canon` is proved idempotent, natural under scaling
(`Int.canon.scale`), and a *decider* of Int equality: `Int.canon.eqv.fwd` and
`Int.canon.eqv.bwd` are the two halves of the quotient lemma (`canon x ==
canon y` exactly when `xp + yn == yp + xn`). The Nat halves both halves rest on
are `cross_gt_gt` and `cross_cmp` in `src/nat.bend`. Only the forward direction
is on the Rat route; the reverse one is here because it is what "canon
decides equality" means.

Known gaps, in dependency order:

1. `Rat`: the type, `Rat.mk`, the operations and the normalization lemmas are
   in, and `==` on canonical values decides rational equality:
   `Rat.mk.scale` (normalization is natural under scaling) and `Rat.mk.eqv`
   (equal cross products give equal normal forms) are both proved, on top of
   `Rat.mk.canon`, `Rat.mk.zero`, `Rat.mk.fixed` and `Rat.mk.den.pos` (the
   denominator of a normalized fraction is positive -- one of the three
   canonicality clauses; the numerator is a difference pair by construction,
   and coprimality of the output is the part this route avoids). The value
   keystone is in as well: `Rat.mk.value` --
   `num(mk(n,d))*d == n*den(mk(n,d))`, the cross product relating a normalized
   fraction to its input, resting on `Rat.mk.value.go`, the exact-division
   cross product `Nat.div_cross` and the shape law `Int.mul_scale`. It is the
   hypothesis `Rat.mk.eqv` consumes, so it is what the composing laws below
   were waiting for. The bridge for a law whose *argument* is another
   operation's output is in as well: `Rat.mk_idem` --
   `mk(numof(M), denof(M)) == M` for `M = mk(Rat.num(np, nn), d)` -- which
   turns a value whose numerator is div/gcd terms back into the difference-pair
   spelling the value laws are stated over. Its fill is `Rat.mk.eqv.raw` at
   `Rat.mk.value`'s own cross product plus the two `sub_diag` rewrites that
   relate the two numerator spellings. It takes the positivity of the output's
   denominator as a hypothesis (`pq`), which is call-site-free: a caller holding
   an operation's output produces it with `Rat.mk.den.pos` and `gcd_divides` at
   its own gcd spelling. Deriving it inside the fill is what blocks it --
   the gcd `Rat.mk` computes and `Rat.mag`'s are equal by one `sub_diag` per
   coordinate, and no congruence reaches a rewrite under `Nat.div` (see
   `PROVING.md`) -- so unconditional `mk_idem` is future work, and the law is
   documented as a private bridge, not a target. Proved field
   laws:
   `add_comm`, `mul_comm`, `sub_eq_add_neg`, and the identity laws
   (`add_zero`, `zero_add`, `mul_one`, `one_mul`, `mul_zero`) for canonical
   values. `Rat.mul_assoc` is now proved as well — the first law that
   composes two *normalized* results, and the template for the rest. Its
   statement is over `Rat{Rat.num(np,nn), 1n+dp}` (the difference-pair
   presentation `Rat.mk.fixed` and the value lemma use, comparison as a
   parameter, no coprimality hypothesis), and its fill is four calls:
   `Rat.mk.value` on each product, `Rat.num.mul` on each product (the shape
   bridge: the product of two difference pairs is a difference pair again, by
   sign case analysis), `Int.scale_cross` (the cross product of the composed
   fraction from the two value equations, scaled by the shared denominator and
   cancelled with `Int.scale.cancel`), and `Rat.mk.eqv.raw`. Still open:
   - `add_assoc`, `add_exchange`, `mul_distrib`, `mul_add_left`, `neg_add`,
     `neg_neg`, the same recipe with the additive value equations (which also
     need the two `Int.canon`-level facts an `Int.add` numerator forces).
2. `QExt` over `Rat`: field axioms plus the multiplicative inverse
   (`1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)`).
3. Binary nats for performance (unary `Nat` is O(value)).
