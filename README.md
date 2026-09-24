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
parameter) with proved `add_comm`, `mul_comm`, `sub_eq_add_neg` and the
conditional `neg_neg`.

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

- `src/nat.bend` — the 129 Nat/Cmp laws (including the `Nat.divmod` and
  `Nat.gcd` blocks, the exact-division block, the difference-pair helpers, the
  scaling/divisibility bridges, `div_cross` -- the exact-division cross
  product the Rat value lemma is built from -- the cross-sum lemmas the Int
  quotient lemma rests on, and the three additive-block helpers `sub_cross` (the
  cross sum of a truncation pair, `(a-b) + b = (b-a) + a`), `cross_add` (two
  equations with a common padding combine criss-cross) and `sub_diag_rev` (the
  flipped twin of `sub_diag`, so a rewrite under a division's dividend can take
  its evidence directly)),
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
- `src/qrat.bend` — `QExt` over `Rat`: the type, `QExt.nat`/`zero`/`one`/
  `add`/`neg`/`sub`/`mul`/`conj`/`norm`, `QExt.of` (the six-coordinate
  abbreviation the composing law is stated with) and `QExt.emb` (a rational as a
  QExt value, the shape `QExt.norm.mul` is stated in), the two operations
  `QExt.inv`/`QExt.div` (`x/y = x * inv(y, q)`, the divisor handed in as a
  spelled rational for the reason every Rat division law does it), and
  twenty-five laws: `add_comm`/`mul_comm`/`sub_eq_add_neg`/`neg_neg`/
  `add_assoc`/`mul_assoc`/`mul_distrib`/`mul_conj`, then the two value laws, the
  field axioms, the three pairs stated over the operations, and the negation and
  conjugation block `neg_add`/`mul_neg`/`neg_mul`/`conj_add`/`conj_conj` (round
  ten). First `QExt.inv.value.gt` and `QExt.inv.value.lt` — the division
  payoff `1/x = conj(x)/norm(d,x)`, stated once per sign of the norm, each with
  the norm spelled as a raw pair of that sign plus `hZ` saying the norm *is*
  that rational (PROVING.md, rounds five and six). Then the operation-level
  `QExt.mul_inv.gt`/`.lt` (the payoff's product read as a quotient) and
  `QExt.div_add.gt`/`.lt` (`(x+y)/z = x/z + y/z`, PROVING.md, round seven).
  Then `QExt.mul_one` (`x * 1 = x`, stated over canonical spellings — `==` is
  structural, so a non-canonical `x` does not survive the product) and
  `QExt.div_mul_cancel.gt`/`.lt`, the field axiom `(x/y) * y = x` at a canonical
  dividend, one law per sign of the norm (PROVING.md, round eight). The
  additive identity and inverse close the operation surface: `QExt.add_zero`/
  `zero_add` (`x + 0 = x`, the same canonical presentation and the same two
  bridges `QExt.mul_one` takes — measured false at an unreduced coordinate, and
  there is no `d` parameter because the radicand belongs to `QExt.mul`) and
  `QExt.add_neg` (`x + (-x) = 0`, at an *arbitrary* value with the coefficients'
  positivity, since `QExt.neg` is componentwise and produces no `mk`) — PROVING.md,
  round nine. Its
  coefficients are rat.bend's `Rat` (`import ./rat.bend as R`); there is no
  second copy of the Rat layer.
- `src/qrat_proofs.bend` — fills every qrat.bend law, and only those: the two
  coordinate witnesses, the two `QExt.mul` coordinate chains, the six algebra
  fills, the six behind the payoff (one product rearrangement per coordinate
  per sign, plus the composing chain), `QExt.mul_one`'s two coordinate chains,
  and the six operation-law fills — five of them one call each, while the
  `div_mul_cancel` pair is the one place in this file where a fill is a
  composition rather than a call (`mul_assoc`, then `mul_comm` under a cong,
  then `mul_inv`, then `QExt.mul_one`) — and the three additive fills, which are
  the shortest in the layer: `add_zero`/`zero_add` are one `Rat.add_zero` /
  `Rat.zero_add` call per coordinate with nothing in between (addition is
  componentwise, so the coordinate goal *is* the Rat law's statement), and
  `add_neg` is one `Rat.add_neg` per coordinate at an arbitrary value. It also hosts `qext.nat.mul_zero` (the
  radicand's coefficient against zero, which `Rat.mul_zero` cannot state) and `qext.mul_add_left`, the bare helper for
  right-distributivity (`QExt.mul_distrib` is stated on the left; the mirror is
  `QExt.mul_comm`, that law, and two `QExt.mul_comm`s under a cong, and both
  `div_add` branches share it).
  The Rat laws it calls (`R.Rat.add_comm`, `R.Rat.mul_comm`,
  `R.Rat.add_assoc`, `R.Rat.neg_neg`) are rat.bend's own, filled by the
  `rat_proofs.bend` import — the same three-file arrangement
  `int_proofs.bend` uses for nat.bend.
- `src/rat.bend` — `Rat{num, den}` with the field projections `Rat.numof` /
  `Rat.denof`, `Rat.mk` (gcd normalization, match-free), `Rat.of` (the raw
  positive-pair spelling a divisor is named in, the abbreviation that lets a
  fill name the divisor once instead of ten times),
  `Rat.add`/`neg`/`sub`/`mul`/`zero`/`one`, `Rat.inv` (the reciprocal, split
  three ways on the numerator comparison) and `Rat.div`, and the laws --
  including the two `Rat.mul_inv` branches, the ten division laws, whose
  statements put the divisor's sign in its *spelling* (PROVING.md, round four),
  and the two denominator/multiplication closure laws `Rat.neg.den.pos` and
  `Rat.neg_mul` the payoff's rearrangements need. `Rat.neg_add.arb` is the
  rung-2 form of the additive negation, `-(x+y) = (-x)+(-y)` at arbitrary
  values -- the law the `QExt` negation block reaches for, because there the
  summands are operation outputs and the canonical `Rat.neg_add` cannot apply to
  them.
- `src/rat_proofs.bend` — fills every rat.bend law.
- `probe.bend` — consumer check for the ten division laws.
- `probe.payoff.bend` — consumer check for the payoff and the operations: the
  two conversions the design rests on (positive and negative divisor spelling),
  each payoff law from the caller's side at a variable `x`,
  `1/(2 + sqrt 2) = (2 - sqrt 2)/2` and `1/(1 + 2*sqrt 3) = (1 - 2*sqrt 3)/(-11)`
  at literals, then the operation-level surface — that `QExt.inv` is its own
  body by conversion, `x/x = 1` from the caller's side on each side of zero (one
  call each, the reason no third law exists), `div_add` at variables on each
  side of zero, `(2 + sqrt 2)/(2 + sqrt 2) = 1` at literals, and then the field
  axiom: `QExt.mul_one` and both `div_mul_cancel` branches from the caller's side
  at a variable `y`, plus `1/(2 + sqrt 2) * (2 + sqrt 2) = 1` at literals. Last,
  the additive identity and inverse: `add_zero`/`zero_add`/`add_neg` from the
  caller's side, `x - x = 0` stated with `QExt.sub` (which the law reaches by
  conversion, so a caller writing a difference needs nothing), and
  `(2 + sqrt 2) + 0 = 2 + sqrt 2` at literals. Last, the negation and
  conjugation laws from the caller's side: the five, one call each, plus
  `neg_add` read *backwards* through `Equal.sym` (the orientation a caller with a
  sum of negations needs is not baked into the statement) and `conj(conj(x)) = x`
  at literals.
- `scratch.bend` — smoke test with a `main`.

Check with `node bend2/main.ts <file>` from a bend checkout. The five
`*_proofs.bend` files are the gates and print `All terms check.`, as do the
two `probe*.bend` consumer files; the
laws-only files intentionally fail with
`Error: N TODOs found.` (an open law is an unfilled TODO), and `scratch.bend`
is the smoke test -- it has a `main`, so it prints the `Rat.inv` triple it
computes instead of that line. The count is
transitive over imports: nat.bend 129, int.bend 32, qext.bend 34 = 32 Int + 2
QExt, rat.bend 229 = 129 Nat + 32 Int + 68 Rat, qrat.bend 256 = 129 Nat +
32 Int + 68 Rat + 36 QExt (it imports rat.bend itself, so its count is
rat.bend's plus its own thirty-six laws).

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
are `cross_gt_gt` and `cross_cmp` in `src/nat.bend`. Both directions are on the
Rat route now: the forward one is what makes two canonical fields read off an
equal pair, and the reverse one (`bwd`, from the cross sum to the equality of the
canonical forms) is what `Rat.mk.eqv.val` consumes.

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
   operation's output is in as well, and it is **unconditional**: `Rat.mk_idem`
   --
   `mk(numof(M), denof(M)) == M` for `M = mk(Rat.num(np, nn), 1n+dp)` -- which
   turns a value whose numerator is div/gcd terms back into the difference-pair
   spelling the value laws are stated over. Its fill is `Rat.mk.eqv.raw` at
   `Rat.mk.value`'s own cross product plus the two `sub_diag` rewrites that
   relate the two numerator spellings; the positivity of the output's
   denominator, which three earlier rounds could not produce, is one
   `div_pos_wit` at the gcd spelling *the goal carries* (with the witness
   `gcd_divides` gives for that same magnitude) -- `Rat.mk.den.pos` is at the
   other spelling of that gcd, which is why it looked like it should apply
   verbatim. `Rat.mk_idem.raw` is the same law with a general denominator and
   its two positivity hypotheses, for callers whose denominator is a product
   (`pq` is call-site-free: the caller's own `gcd_divides` pair plus
   `div_pos_wit` produces it, as `Rat.mul_assoc` does for its two). Proved field
   laws:
   `add_comm`, `mul_comm`, `sub_eq_add_neg`, and the identity laws
   (`add_zero`, `zero_add`, `mul_one`, `one_mul`, `mul_zero`) for canonical
   values, plus `zero_mul` — `0 * x = 0` for a positive denominator, which is
   not the mirror of `mul_zero` by reduction: with the zero on the left the
   numerator collapses on its own but the denominator does not, and the way
   through is `Rat.mk.diag` (a diagonal numerator over a *positive* denominator
   is zero — no successor spelling, no coprimality). On top of it sits
   `Rat.mul_eq_zero`, the zero-product law in the unit form a proof can use:
   `x*y = 0` together with a right inverse `y*q = 1` gives `x = 0`. There is no
   disjunction in an equation, so the branch is the caller's: whoever knows `y`
   is non-zero hands over the inverse `Rat.mul_inv` produced, and its branch
   evidence *is* the non-zero-ness — which is why that law carries no sign at
   all. `Rat.mul_assoc` is now proved as well — the first law that
   composes two *normalized* results, and the template for the rest. Its
   statement is over `Rat{Rat.num(np,nn), 1n+dp}` (the difference-pair
   presentation `Rat.mk.fixed` and the value lemma use, comparison as a
   parameter, no coprimality hypothesis), and its fill is four calls:
   `Rat.mk.value` on each product, `Rat.num.mul` on each product (the shape
   bridge: the product of two difference pairs is a difference pair again, by
   sign case analysis), `Int.scale_cross` (the cross product of the composed
   fraction from the two value equations, scaled by the shared denominator and
   cancelled with `Int.scale.cancel`), and `Rat.mk.eqv.raw`. `Rat.neg_neg` is
   proved too — the first law whose argument is another operation's *output*.
   Its statement carries coprimality (`Rat.mk.fixed`'s own hypothesis), and
   that is required for truth rather than a convenience: `==` on `Rat` is
   structural, and `np = 4, nn = 0, dp = 1` evaluates to
   `neg(neg(Rat{Rat.num(4,0),2})) = Rat{Int{2,0},1}` against
   `Rat{Rat.num(4,0),2} = Rat{Int{4,0},2}`. With it, negation on a canonical
   value is two `Rat.mk.fixed` calls around one congruence (the intermediate's
   coprimality is the stated one, since `Rat.mag` is symmetric by `add_comm`) —
   no value equation, because negation does not touch the denominator.
   `Rat.mk.rep` — the representative bridge
   `mk(Rat.num(U,V), d) == mk(Int{U,V}, d)` — is unconditional and takes no
   comparison parameter: mk is blind to which representative of the numerator's
   value it is handed, and the two `sub_diag`s that collapse the `mag` of a
   one-sided pair are instances at the explicit comparisons (every rewrite is an
   `Equal.cong` with a motive, never a `%`, since all of them reach under a
   `Nat.div`). `Rat.mk.canon.go` (the comparison-threaded spelling of "mk is
   blind to the representative", named `.go` because `Rat.mk.canon` is the
   fixed-point law) is the same statement one level up: it puts
   `mk(Int{xp,xn}, d)` and `mk(Int.canon.go(c, xp, xn), d)` together, and it is
   what makes "equal-value pairs have equal mks" reachable at all -- the cross
   product `mk.eqv.raw` consumes can never show it, since
   `mul(X, unit d) == mul(Y, unit d)` is false for two different representatives
   of the same value. `Rat.add.value` is the newest: **add of two normal forms is the
   normal form of their *unreduced* sum**, the additive twin of the product
   shape. A sum of two difference pairs is *not* one-sided, so no shape law can
   relate it and the cross product has to be assembled instead — the fill is
   `Rat.mk.value` on each summand scaled into the shared denominator (the
   Int-level permutation of `R.Rat.add.piece`/`R.Rat.add.cross`), then
   `Rat.mk.eqv.raw`. `Rat.neg_add` is the newest — the first *additive*
   composing law, and the template for the rest: the right-hand side is
   `Rat.add.value` at the two negated summands, the left-hand side is
   `Rat.mk.eqv.raw` at the value equation `Rat.mk.value` gives after
   `Int.neg_mul` has moved the negation inside it, and `Rat.mk.rep` plus four
   `Nat.add` commutations join the two raw spellings. No coprimality, no case
   split, and no scaling at all — negation never touches a denominator.
   `Rat.mk.trunc` is the representative bridge one level up from `Rat.mk.rep`:
   `mk(Int{U,V}, d) == mk(Rat.num(sub(U,V), sub(V,U)), d)` -- the raw pair against
   its own truncation pair, with no comparison parameter, because canon.go's
   branch value *is* that pair and the collapse is two `sub_diag` instances at the
   explicit comparisons. This is what a *composite* numerator needs (a sum of two
   difference pairs is not a truncation of anything, so `mk.rep` cannot collapse
   it), and it is one step from the presentation the mixed value law is stated
   over.
   `Rat.mk.eqv.val` is the general quotient lemma the additive block needs, and
   the payoff of `Rat.mk.canon.go`: `mk` is *determined by the value* when the
   two fractions' cross **sums** agree (`xp*d2 + yn*d1 == yp*d1 + xn*d2`), with
   no coprimality and only the two denominators' positivity. That hypothesis is
   the one thing `Rat.mk.eqv.raw` cannot accept, and the reason is measured:
   `==` on `Rat` is structural, so two representatives of the same integer give
   different cross *products* (`6/24` against `-14/24`: `(6,20)` scaled against
   `(0,14)`), and no cross product will ever equate them. Its fill runs two
   forward chains, one per side — pos_witness to a successor denominator,
   `Rat.mk.scale` backwards over the common denominator `d1*d2`, `Int.mul_scale`
   to the raw pair, `Rat.mk.canon.go` — and meets them with
   `Int.canon.eqv.bwd` plus one congruence.
   `Rat.add.value.mixed` is also new, and it is the shape the additive block
   actually needs: `Rat.add.value` requires *both* summands mk-spelled, while
   add_assoc's outer add has one mk summand and one constructor summand. The
   mixed law is that law's twin with the second summand a *raw* coordinate pair
   `Int{Zp,Zn}` over its own denominator `D` (the difference-pair/successor form
   is the reading `Zp := sub(np2,nn2)`, `Zn := sub(nn2,np2)`, `D := 1n+dp2` of
   it) and the mk summand's denominator the general `d` it was handed (a product
   at every call site), so its fill is the value equation of the mk summand
   scaled by the square of the other denominator and carried through the two sums
   by the ring laws — no truncation reasoning, no case split, and three positivity
   hypotheses (`d`, `D`, and the mk output's denominator) of the same kind
   `Rat.mk.value`/`Rat.mk_idem.raw` take. The raw form is what the rung-2
   composing law can call, since its summands are arbitrary Rats and
   `Rat.num(Zp,Zn)` is a different pair from `Int{Zp,Zn}` unless a coordinate is
   zero. Its mirror image (constructor first) is `Rat.add_comm` away, so it is not
   stated separately.
   `Rat.add_assoc` is the newest, and the first law that composes a sum with a
   *sum*: the outer add's mk-headed summand has a numerator that is a sum of two
   difference pairs — not one-sided, which is what `Rat.mk.trunc` bridges — and
   the two sides then meet at one `Rat.mk.eqv.val` whose hypothesis is the Nat
   cross sum of the two inner sums' truncation pairs, proved from two
   `Nat.sub_cross` instances combined criss-cross by `Nat.cross_add`. No new Nat
   law, no case analysis, no coprimality, and no comparison parameter: the law
   is stated over the canonical presentation exactly as `Rat.mul_assoc` is. The
   Nat half is nine proof-only helpers (`R.Rat.nat.cross4` and the shuffles it
   is built from) in `rat_proofs.bend`. `Rat.add_exchange` follows, and it is
   the one law of the block whose fill needs no value equation and no cross sum
   at all: it is the three-step derivation from the two laws above it
   (`add_comm`, `add_assoc` read backwards, one congruence), so no new
   machinery.
   `Rat.mul_distrib` is the newest, and it is the law whose closing step had to
   be *remeasured*: `Rat.mk.eqv.raw` cannot close it, because the two mk
   arguments are different representatives of one rational and that law's
   hypothesis is a cross *product* between the pairs (the earlier
   `mk.trunc`-on-the-sum-side route is refuted too -- both spellings fail at all
   ten canonical instances tested). The consumer is `Rat.mk.eqv.val`, reached in
   three comparisons: the left-hand side against a *value-cleared* `U_L`
   (`num(x)*Rat.num(U2,V2)` over `xd*d2`, from the two `Rat.value.scaled`
   readings of `Rat.mk.value` at the inner sum), `U_L` against the right-hand
   side's own unreduced sum `U_R` (the pure Nat identity `(T)` PROVING.md
   records, multiplied by the common denominator `d1*d3`), and `U_R` against
   the right-hand side, which is exactly `Rat.add.value` plus two `Rat.mk.rep`
   steps and `Int.mul_scale`. `(T)` itself is proved by the padded-hypotheses
   route -- the inner sum's cross sum scaled by `x`'s two numerator coordinates
   and the two products' cross sums scaled by `Zd`/`Yd` share a padding, so
   `Nat.cross_add` combines them criss-cross -- with **no case analysis and no
   new Nat law**: the whole Nat block is fourteen proof-only helpers in
   `rat_proofs.bend` (`R.Rat.nat.distrib` and the shuffles it is built from).
   `Rat.mul_add_left` follows for free, exactly as PROVING.md predicted: three
   steps (`mul_comm`, `mul_distrib`, two `mul_comm`s under a congruence) and no
   arithmetic at all.
   `Rat.add_assoc.arb` is the newest, and it is the *rung-2* form of the law
   above: arbitrary `Rat` variables with the positivity of the three input
   denominators as the only hypotheses. It is the statement a caller whose
   summands are pattern variables can instantiate (a law stated over `Rat.mk(...)`
   applications cannot be used at a stuck term, which is what an arbitrary `Rat`
   is), and the canonical law above is its reading at its own coordinates -- it
   stays stated beside the general one (its own positivity slot is empty, while
   the general form's inputs are not mk-shaped, so a caller with canonical values
   wants the hypothesis-free statement) and its fill is now one call of the
   general law, with the three hypotheses supplied by `{==}`. The
   fill is the canonical fill's chain at the *raw* coordinates the two levels of
   destructuring expose (three Rats, then their three `Int` numerators -- one
   helper per level, since a def's parameters may be matched at its body head and
   a nested match on a pattern variable may not), with the Nat cross-sum block
   reused verbatim: its gaps are the raw coordinates, so it never saw the
   presentation at all. The two new pieces are `Rat.add.value.mixed` in its raw
   form (the outer adds' mk summands are raw pairs) and the positivity of the mk
   output's denominator, `Rat.div.pos` -- `Nat.div_pos_wit` at the dividend's own
   spelling, by one `pos_witness` rewrite that the divisibility witness is
   transported along. No projection bridge and no `Rat.mk_idem`-shaped step is
   needed anywhere in it.
   Still open: the `QExt` block below -- both distributive laws are now in, the
   multiplicative inverse is in, and the laws of `Rat.div` are in as well, so
   what the Rat side still lacks is the field axioms stated over `div` at an
   arbitrary divisor (the ten division laws are stated at a spelled-out sign,
   which is what makes them provable; see PROVING.md, round four).
2. `QExt` over `Rat` — landed so far:
   `src/qrat.bend` + `src/qrat_proofs.bend` carry the type, the operations, the
   two coefficient projections (`QExt.re`/`QExt.im`, which the general
   add_assoc's hypotheses are stated over) and five laws: `QExt.add_comm`,
   `QExt.mul_comm` (both hold for *every* pair of coefficients, because addition
   is componentwise and the radicand coefficient is a parameter, not an
   operation's output), `QExt.sub_eq_add_neg` (definitional, as in Rat),
   `QExt.neg_neg` (`-(-x) = x`, the one law that needs the canonical
   presentation and coprimality) and `QExt.add_assoc` (arbitrary values, below).
   `QExt.neg_neg` is componentwise `Rat.neg_neg` and therefore carries that
   law's coprimality hypothesis on *both* coordinates -- the Rat law is false
   unconditionally for the same reason (== is structural, and a negated value
   comes back mk-headed), and the QExt statement inherits exactly that. It is
   now two `R.Rat.neg_neg` calls, one per coordinate, into rat.bend's own
   (rat_proofs.bend-filled) law. The earlier round could not call it and
   restated it instead -- a Nat helper (`nat.sub.min`, `(a-b) - min(a,b) =
   (a-b)`, three branches on Nat.cmp, not `sub_self` and not `sub_cross` +
   `add_cancel`) plus two Rat helpers (`rat.mk.fixed.neg`, `rat.neg.neg`) went
   with the copy. All five are deleted: the Rat-level work is
   `rat_proofs.bend`'s fill, called at the law's own telescope with a literal
   `Nat.cmp` and `{==}` evidence.
   `QExt.add_assoc` landed first in the canonical presentation its own comment
   and `QExt.neg_neg` use -- six coordinates, each `Rat{Rat.num(np,nn), 1n+dp}`,
   so the law read `QExt.add_assoc(np1, nn1, dp1, mq1, mn1, dq1, np2, ...)` -- and
   is now the form over **arbitrary** QExt values, at the same key: `for +x:
   QExt, +y: QExt, +z: QExt` with the positivity of the six coefficients as the
   six hypotheses. The fill is exactly what the componentwise shape promised: one
   `R.Rat.add_assoc.arb` per coordinate and nothing else, two calls, no case
   analysis, and no arithmetic of its own -- and the six hypotheses are spent as
   they are, three per coordinate.
   The canonical form is gone rather than duplicated because the general one
   *does* subsume it: a caller with canonical values supplies each hypothesis
   with `{==}`, by computation (`Rat.denof(Rat{Rat.num(np,nn), 1n+dp})` is
   `1n+dp`). The Rat-level pair does not collapse that way -- there the canonical
   `Rat.add_assoc` stays stated beside `Rat.add_assoc.arb`, since its positivity
   slot is empty while the general form's inputs are not mk-shaped -- which is
   why the two layers are written differently.
   The earlier round recorded both sides of the obstruction honestly and they are
   still the reason the law needs hypotheses rather than a bridge: the law is
   *true* without them (nine evaluated witnesses outside the canonical
   presentation agree, PROVING.md records them) and the machinery cannot discharge
   them (an arbitrary `Rat` may be `Rat{Int{1,0}, 0}`, where mk's behaviour is
   junk, and == on Rat is structural so nothing turns an arbitrary Rat into a
   canonical one). What changed is that the Rat layer now has the mk-headed law
   the general form needs, so the hypotheses can be *stated* and passed through
   instead of being an obstruction.
   The composing *multiplicative* laws needed that rung-2 work too, and for a
   different reason: `QExt.mul`'s coordinates are *sums of products*
   (`xa*ya + d*xb*yb`), so `QExt.mul_assoc` and `QExt.mul_distrib` are not
   componentwise `Rat.mul_assoc`/`Rat.mul_distrib` calls at all -- they need
   those Rat laws at mk-headed arguments (each product and each sum in them is
   an operation's output), which is exactly the rung-2 work their fills do, at
   `R.Rat.mul_assoc.arb` / `R.Rat.mul_distrib.arb`.
   The multiplicative inverse
   (`1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)`) was staged as the step
   after that, and it was the one that needed `Rat.sub` under both distributive
   laws.
   The rung-2 form (arbitrary `Rat` variables, positivity of the three inputs as
   hypotheses) is **in for the additive law now**: `Rat.add_assoc.arb` landed in
   `rat.bend`, filled in `rat_proofs.bend`, and `QExt.add_assoc` moved to it: its
   fill is two `R.Rat.add_assoc.arb` calls and nothing else. (This sentence used
   to say that move was *the next unit*, while the fill was still the canonical
   `R.Rat.add_assoc` per coordinate; the composing multiplicative laws moved the
   same way, so the whole block is at rung 2 now.) What that round had *not*
   measured -- and two earlier rounds had assumed -- is that the rung-2 fill
   needs no bridge of the `Rat.mk_idem` kind at
   all; the spelling the previous round was stuck on (`mk` of a projection pair
   against `mk(Rat.num(a,b), W)`, and the `Int.mul` that stays stuck in the goal
   while its `trans` argument unfolds) belongs to the *other* route, which bridged
   a mk-headed summand by naming its projection. Destructuring the three inputs
   twice instead — one helper level per layer — makes every term on both sides
   reduce, and the chain is then the canonical one at raw coordinates. PROVING.md
   records both the two measurements that stopped the previous round and this
   round's result.
   The **negation block** that the inverse needs is in as well, and it moved the
   layer's frontier: `Rat.mk.diag` (`mk(Int{T,T}, d) == Rat.zero()` for any
   positive `d`), `Rat.mul_neg` (`x*(-y) = -(x*y)`) and `Rat.add_neg`
   (`x + (-x) = 0`). All three carry the rung-2 positivity hypothesis rather
   than coprimality or a canonical spelling, and the two negation laws are
   *not* congruence fills even though their raw numerators do line up: `Rat.mul`
   destructures its second argument, whose numerator is the stuck
   `Int.neg(yn)`, so the goal never reaches the congruence shape. What makes
   them cheap is `Rat.neg_eq_mul_negone` — `-y = (-1)*y`, unconditional, two
   congruences — after which `mul_neg` is `Rat.mul_assoc.arb` twice around one
   `Rat.mul_comm`, and `add_neg` is `Rat.mul_comm` + `Rat.mk.rep` +
   `Rat.add.value.mixed` + `Rat.mk.diag` with `Nat.sub_cross` and
   `Nat.mul_add_left` closing the diagonal. `Rat.add_neg` was *restated* from
   the canonical-plus-coprime form the previous round wrote to the arbitrary
   value form: the inverse needs it at `Rat.mul(xa, xb)`, an mk-headed product
   no canonical statement can be instantiated at, and with the raw coordinates
   in hand no coprimality is needed at all. PROVING.md's last section records
   the measurements.
   The **multiplicative inverse is in**: `Rat.inv` splits on
   `Nat.cmp(np, nn)` and returns `d/(np-nn)` -- spelled as the raw constructor,
   which is one pair and needs no coprimality -- `Rat.div` is `mul` by it, and
   both branch laws `Rat.mul_inv.gt`/`Rat.mul_inv.lt` are proved in
   `rat_proofs.bend`. Both were *false as first stated*: the numerator was
   spelled out of `np`/`nn` and dropped `d`, so the reciprocal's value was 1 for
   every non-zero input and no proof could have existed; the fix is the `d` in
   the numerator slot. What makes the branches cheap is that the product's
   coordinates come out as `div(T,T)`, `div(0,T)`, `div(T,T)` with `T = d'*|np-nn|`
   -- so the closing is `div_self` twice and `div_zero` once, and the *only*
   gcd work is showing the divisor is `T`, which is `Nat.gcd_scale` (plus the
   new `Nat.gcd_self`). Those two were the last unfilled laws in the tree, and
   there are none left: every `*_proofs.bend` file checks. PROVING.md's
   round-two and round-three sections record the measurements (including the two
   Nat laws this rests on).
   The laws of `Rat.div` are **in**: ten of them, stated at a divisor whose sign
   is in the *spelling* (`Rat{Rat.num(1n+ap, 0n), 1n+dp}` for positive,
   `Rat{Rat.num(0n, 1n+bp), 1n+dp}` for negative, `Rat{Rat.num(0n, 0n), 1n+dp}`
   for the zero case, where the comparison computes and `Rat.div` reduces to a
   product by the reciprocal). Three value forms
   (`Rat.div.value.gt`/`.lt`/`.eq`, the last being the division-by-zero case),
   the two `Rat.div_self` branches and `Rat.div_one`, the field axiom
   `Rat.div_mul_cancel` (`(x/y)*y = x`) and
   `Rat.div_add` (`(x+y)/z = x/z + y/z`), each with a gt and an lt branch where
   the branch matters. All ten apply from a downstream module -- `probe.bend`
   calls every one of them and derives `(x + y)/1 = x + y` from two of them.
   What is still out of reach is a *branch-free* statement at a variable
   divisor: `Nat.cmp(bp,bnn)` is stuck there and sits inside `Rat.inv`'s
   argument list next to the `{==}` whose type mentions it, where no `%` step
   can reach it. PROVING.md's round-four section has the measurement. On the
   QExt side the division-free
   rationalization is **in**: `QExt.conj` and `QExt.norm` are two cheap defs
   (`conj(x) = (re, -im)`, `norm(d,x) = a^2 - b^2 d` as a `Rat`), and
   `QExt.mul_conj` states `x * conj(x) = norm(d,x) + 0*sqrt d`, filled by two
   Rat chains over the coefficients -- `Rat.mul_neg` twice in the real
   coordinate, once in the imaginary one, then `Rat.mul_comm`/`Rat.add_comm`
   and `Rat.add_neg` to reach zero.
   The division form itself is **in** on both sides of zero:
   `QExt.inv.value.gt` and `QExt.inv.value.lt` state
   `x * (conj(x)/norm) = 1` with the divisor's sign in the *spelling*, i.e. the
   norm written as a raw pair `(1+ap)/(1+dp)` when positive and
   `-(1+bp)/(1+dp)` when negative, plus `hZ` saying the norm *is* that rational.
   Two things make them cheap, and both are measurements:
   `Rat.div` against a spelled divisor already unfolds to `mul(a, reciprocal)`
   by conversion at a *variable* dividend (no law, no rewrite -- the conversions
   `probe.payoff.bend` records), and each fill is then `QExt.mul_conj`'s own
   rearrangement with the reciprocal carried through it: `mul_neg`, `neg_mul`
   twice, `mul_add_left` backwards, one `cong` against `hZ`, and
   `Rat.mul_inv.gt`/`.lt`. The Rat laws the GT half needed -- `Rat.neg.den.pos`
   and `Rat.neg_mul` (negation on the *left*; `Rat.mul_neg` cannot be turned
   around) -- are in `rat.bend` too. `probe.payoff.bend` calls both laws from
   the caller's side at a variable `x`, and at `1/(2 + sqrt 2) = (2 - sqrt 2)/2`
   and `1/(1 + 2*sqrt 3) = (1 - 2*sqrt 3)/(-11)`.
   The LT half is not a courtesy twin: the norm is indefinite in `d`, so
   `1 + 2*sqrt 3` (norm -11) has no positive spelling at all and no `hZ` exists
   for the GT law -- measured, that extension against the positive spelling 11
   multiplies out to **-1**. The pair of laws covers every extension with a
   non-zero norm; norm = 0 is correctly uncovered, because `a^2 = b^2 d` is
   reachable for non-zero `x` when `d` is a square (`x = 2 + sqrt 4 = 4`), and
   such an extension is a zero divisor with no inverse to state. What is still
   out of reach on this side is the *branch-free* form, for the same stuck
   `Nat.cmp` reason as the division laws.
   The division payoff is now also an **operation**: `QExt.inv` is
   `(re/q, -im/q)` and `QExt.div` is `x * inv(y, q)`, both taking the divisor's
   rational as a parameter for the reason every Rat division law spells its
   divisor out -- `Rat.div` needs a constructor-headed divisor for the `Nat.cmp`
   in its argument list to compute. Four laws are stated over them:
   `QExt.mul_inv.gt`/`.lt` (the payoff's product read as a quotient; each fill is
   one call, since `QExt.inv`'s body is verbatim the divisor expression the value
   laws are stated over -- `probe.payoff.bend` records that conversion) and
   `QExt.div_add.gt`/`.lt`, `(x+y)/z = x/z + y/z`. No `x/x = 1` law exists, and
   none is needed: the quotient unfolds to the product `QExt.mul_inv` concludes,
   so a caller states the quotient and cites that law -- the probe does exactly
   that on both sides of zero. `div_add`'s fill is the mirror of
   `QExt.mul_distrib` (a bare helper `qext.mul_add_left`, shared by both
   branches) applied at the reciprocal, and its positivity hypotheses for the
   *quotient* are derived inside the fill rather than asked for: the reciprocal
   of a spelled rational has denominator `1n+ap`, so its positivity is `{==}`,
   and `Rat.mul.den.pos` lifts the divisor's.
   The field axiom `(x/y)*y = x` is now **in**, as `QExt.div_mul_cancel.gt`/`.lt`
   — one law per sign of the norm, at a canonical dividend, which is what the
   round-seven probes force: at a variable dividend every route passes through
   `x * 1 = x`, and that step is false at non-canonical values -- `mul(x,
   QExt.one())` comes back normalized (`Rat{Int{2,0},2}` prints as
   `Rat{Int{1,0},1}` against an `x` that keeps the unreduced spelling). So
   `QExt.mul_one` came first, presented over canonical spellings the way
   `QExt.neg_neg` is, and the field axiom is `mul_assoc`, `mul_comm` under a
   cong, `mul_inv`, then that law. What stays out of reach is the *branch-free*
   form at a variable dividend: `==` is structural on `QExt`, so there is no
   presentation-free statement of it to prove.
   The additive identity and inverse are in too, which closes the operation
   surface: `QExt.add_zero`/`zero_add` (canonical, the same two bridges as
   `mul_one`, and measured false at an unreduced coordinate — the same
   measurement, one operation over) and `QExt.add_neg` (`x + (-x) = 0` at an
   *arbitrary* value, because `Rat.add_neg` is unconditional in the spelling and
   `QExt.neg` produces no `mk`). The negation and conjugation block landed after
   that (round ten): `QExt.neg_add` (`-(x+y) = (-x)+(-y)` — the same *distribution*
   law its Rat namesake is, which is why the name could be used at all),
   `QExt.mul_neg`/`neg_mul` (the negation pulled out of a product, one factor at a
   time) and `QExt.conj_add`/`conj_conj`, whose pair says `conj` is an additive
   automorphism. All five are stated over *arbitrary* values: `QExt.neg` is
   componentwise and produces no `mk`, so no canonical presentation is needed, and
   the hypotheses are exactly the ones the Rat laws underneath want — both
   coordinates' positivity for `neg_add` (`QExt.neg` negates the real coordinate
   too, unlike `QExt.conj`), the imaginary coordinate's coprimality alone for
   `conj_conj`. The flipped additive inverse still has no law of its own: it is
   `QExt.add_comm` followed by `QExt.add_neg`, two steps, and naming *that*
   `neg_add` is the confusion the Rat files' names rule out.
   The other half of the homomorphism statement, `conj(x*y) = conj(x)*conj(y)`,
   landed in round eleven as `QExt.conj_mul` — but not for free: it is *false* at
   an arbitrary pair of spellings, so its spelling conditions travel as
   hypotheses: the two imaginary coefficients named as spelled pairs (the same
   coprimality hypothesis `conj_conj` asks for) and the four denominators'
   positivity. Round thirteen measured what stating it at `QExt.of`'s six
   coordinates cost — each side of the conclusion normalizes to 4.3 MB of `mk`
   chain, one conversion took about a second, and the law was 3.3 s of the file's
   5.5 — and round fourteen restated it at arbitrary values with those spellings
   supplied as hypotheses: the same statement, with the spelled one as its
   instance, and 3.3 s became 0.03 s. Its real coordinate is the Rat
   identity `mul(neg a, neg b) = mul(a, b)` at a reduced pair, which no law had
   reached: `Rat.mul.neg_neg.reduced` (rat.bend), the rung-2 twin of the canonical
   `Rat.neg_neg`, whose fill rewrites each negation through `Rat.neg.reduced` and
   leaves an `Int`-level identity, so coprimality is the only Nat fact it
   consumes. An earlier round recorded that obstruction here as unreachable; it
   was reached by stating the identity at a reduced pair rather than by
   rearranging a stuck product. The **norm is multiplicative** as well:
   `QExt.norm.mul` states `norm(d, x*y) = norm(d,x) * norm(d,y)` as an equation
   of QExt values — the two embedded norms, via `QExt.emb` — because the
   Rat-level spelling normalizes an `mk` chain at every conversion: a spelled
   draft of it exhausted a 4 GB heap in 41 seconds, and the first fill at that
   presentation was killed past four minutes. Restated at stuck terms, with the
   three norms named by hypotheses, the fill checks and costs nothing
   measurable. **No zero divisors when the norm is non-zero** is in as well, in
   the form this language can carry: `QExt.mul_eq_zero` states that `x*y = 0`
   together with `x*zi = 1` gives `y = 0`. The non-zero norm travels as that
   unit witness -- `zi` is the inverse the two payoff laws produce, and their
   branch evidence *is* what "non-zero" means here -- so the law carries no sign
   and never mentions the norm; and `y` is spelled at `QExt.of`'s six
   coordinates, because `y*1 = y` is false at an unreduced coordinate and
   `QExt.mul_one` is the first step of the chain. Its companion
   `QExt.mul_zero` (`0*x = 0`, the step the chain ends on) is componentwise like
   `QExt.add_zero` and needs the new `Rat.zero_mul` underneath. The hypothesis is
   exactly as strong as it has to be: at `d = 4` the element `-2 + sqrt 4` has
   norm zero and really is a zero divisor -- `(-2+x)(2+x) = x^2 - 4 = 0` -- which
   `probe.payoff.bend` records at literals. The norm's own identities close the
   story: `norm(d, 0) = 0`, `norm(d, 1) = 1`, `norm(d, conj x) = norm(d, x)` and
   `norm(d, -x) = norm(d, x)`, so with `norm.mul` the norm factors through
   conjugation, is even, and lands on the two constants -- and `conj(-x) =
   -conj(x)` is free (both sides are the same term once the projections come
   off). The two invariances are stated at arbitrary `x` with the spelled
   coordinate supplied as a hypothesis rather than at `QExt.of`'s coordinates:
   the spelled form cost 6.4 s and 6.7 s of a 15.3 s file, the restated one is a
   three-step transport at stuck terms, and the spelled statement survives as the
   instance where the hypothesis is `{==}`. The boundary is a pair of laws as
   well, `QExt.zero_divisor.d4` and its norm, at literals only -- a parametric
   version over a radicand `c*c` stops one step short, because `mk`'s divisor is
   then `gcd(c*c, 1)` and `Nat.gcd` cannot start on a product. The measurements,
   the route and the laws' own comments are in qrat.bend and PROVING.md, rounds
   ten through seventeen.
3. A binary-nat layer for proof land. The compiled lanes are already binary -- the
   C lane maps `Nat` to W64 with native `nat_add`/`nat_mul`/`nat_divmod`
   (`comp.ts:161`, `comp.ts:255`), and the JS lane uses BigInt -- but in proof
   land a literal is a tower of `Succ` around `Zero` (`bend.ts:2245`), so literal
   size *is* term size, and every `Nat` operation is defined by recursion over
   that tower.
