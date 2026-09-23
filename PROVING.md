# Proving in Bend: lessons learned

Notes from building `src/nat.bend`, `src/int.bend`, `src/qext.bend` (laws)
and their `*_proofs.bend` counterparts (exact
integer arithmetic and `QExt.mul_comm` from scratch, June 2026). Written for
whoever picks this up next. Everything here was learned by hitting the
checker; each pattern below appears in a file in this repo that currently
passes `All terms check.`

`Int` has since been re-represented as a `(pos, neg)` difference pair, which
retired the whole `Int.add_assoc` case-analysis campaign described below. See
"Why Int is a (pos, neg) difference pair" for the measurement, and the
campaign section (kept as the record of what the previous representation
cost). The rewrite discipline, the affinity rules, the `%` orientation trap
and the termination rules are unchanged by that switch: they are properties
of the checker, not of `Int`.

## Toolchain

- No `bend` binary needed: `node bend2/main.ts file.bend` from a bend
  checkout works (node 24 runs the TS directly; the JS *backend* fails under
  node, but checking and checker-normalized `main`s work fine).
- A file with no `main` just checks. A `main` returning a value is
  normalized by the checker and printed — a free, slow, trustworthy test
  harness: `def main() -> I.Int: I.Int.add(...)` prints the constructor.
- Read `guide/GUIDE.md` fully before writing anything. Read the header
  comment of `bend2/bend.ts` (first ~200 lines) for the real grammar; the
  guide glosses over details the grammar pins down.
- `tests/proof/` in the bend repo is the style reference. `add_comm.bend`
  there independently discovered the same idioms as this repo.

## The rewrite discipline (the one thing to internalize)

`%e : P` where `e : {a == b : T}`:

- `P` is the goal with `_` marking an occurrence of **`b`** (the RHS of `e`).
- The new goal is `P` with `a` (the LHS of `e`) there instead.

So `%` replaces **RHS-of-`e`** occurrences with the LHS. To rewrite
left-to-right you must `Equal.sym` first — or better, state the lemma
flipped so its RHS is the "complicated" side that shows up in goals. This
repo carries `add_assoc_rev` and flipped statements of `add_succ`,
`mul_succ`, `mul_distrib` for exactly this reason. When a rewrite "did
nothing" or produced a reflexive goal, the `_` marked the wrong side.

Motives must be written in the goal's *reduced* vocabulary: after
`case 1n+p:`, the goal's `Nat.add(1n+p, x)` has already unfolded to
`1n+Nat.add(p, x)`. When a motive fails, write out both sides by hand and
reduce each def call mentally (defs unfold transparently; `match` on a
constructor fires).

## Affinity applies to proofs

Law binders are live. If an induction hypothesis and a helper lemma both
mention `b`, you get `b (consumed more than once)`. Fix: `for +b: Nat` in
the law (fine for any `Data` type). Matching a `+` scrutinee hands out `+`
pattern fields, which you also need when the IH and another call both use
`ap`. Just mark every law binder `+` from the start; it costs nothing and
removes a whole error class.

Occurrences inside motives and in erased (`-`) arguments are dead and free.
`Equal.trans`/`sym`/`cong` erase their endpoints, so spelling them out is
verbose but never counts as a use.

## Evidence by conversion beats rewriting

If the goal is *convertible* to a lemma's statement, the lemma application
is the proof — no `%` needed:

```
case 1n+ap 0n:
  add_zero(1n+ap)   # goal was {Nat.add(Nat.sub(1n+ap,0n),0n) == 1n+ap}
```

The checker normalizes `Nat.sub(1n+ap, 0n)` away on its own. Before writing
a `%` chain, ask whether some helper's type already *is* the goal. See
`Int.add.same_comm` being called directly in `Int.add_comm`.

## Structuring tricks that worked

- **Helper laws over inline motives.** `Int.add_comm` contains no rewrites
  in its same-sign cases: the shuffle lives in `Int.add.same_comm`, proved
  once by its own small match, then applied by conversion. Every time a
  goal got big, factoring the next step into a named `law` with
  matchable parameters made it small again.
- **Push case splits into the program.** `Int.add.same` matches on the
  magnitude instead of wrapping everything in a canonicalizing `Int.mk`,
  because a `match` on a stuck variable makes conversion stuck too, and
  then proofs can't reduce past it. If a proof needs to know which branch
  an op took, the op should expose that branch as a top-level `match` on
  its parameters.
- **Canonicalize in ops, not invariants.** `Int.add` always returns
  `Int{False{}, 0n}` for zero, so `==` on results needs no "canonical"
  side conditions in laws.
- **`Equal.trans` chains for pure shuffles.** When no single rewrite
  orientation works (re-bracketing four summands in `mul_distrib`), build
  the chain explicitly. Spell the endpoints once in the calls; they're
  erased, so they're free at runtime and don't consume variables. Yes,
  it's ~20 lines where an SMT solver needs zero. That's the deal here.
- **Discrimination boilerplate, once.** Impossible `cmp` cases are closed
  by a predicate def returning `Type` (`CmpIsEQ`: `EQ{}` ↦ `Unit`, else
  `Empty`), then `%Equal.sym(Cmp, LT{}, EQ{}, e) : CmpIsEQ(_); Unit{}` —
  see `lt_ne_eq` in `src/nat_proofs.bend` (law stated in `src/nat.bend`). With an `Empty` in hand,
  `Empty.absurd(goal, it)` closes anything.
- **Evidence-carrying comparisons.** `Nat.cmp` returns a bare `Cmp`. The
  bridges `cmp_eq` / `cmp_gt_sub_add` (hypothesis `{Nat.cmp(a,b) == EQ{}}`
  etc. as a law parameter) are how a proof learns arithmetic facts from a
  comparison result. Any serious development needs these; expect each to
  be a small induction with two absurd cases.

## Laws vs proofs (the split-file mechanism, as observed)

This repo keeps laws and proofs in separate files per module
(`nat.bend`/`nat_proofs.bend`, `int.bend`/`int_proofs.bend`,
`qext.bend`/`qext_proofs.bend`). What the checker actually does, all
verified empirically on this checkout:

- **Filling**: `proofs.bend` does `import ./laws.bend as L`, then
  `def L.name(args): <proof>` fills `law name`. Dotted law names fill the
  same way: `law Int.add_comm` is filled by `def I.Int.add_comm(x, y)`.
- **Naming inside the proofs file**: the fill attaches the def to the
  *laws file's* module, so recursive and cross-proof calls go through the
  alias: `NL.add_comm(...)`, `I.Int.add.same_comm(...)`. Bare names do not
  resolve (the proofs file defines nothing under its own namespace), and
  chained aliases do not exist: `NP.NL.add_comm` is "not a defined name".
- **Third files** that want to *use* a proved law must import both the
  laws file (under the alias they call through) and the proofs file
  (under any alias — it may be unused; its presence in the import graph
  is what fills the laws). Calling an unfilled law errors with
  `a filled definition (an unfilled law is a dead claim: live code
  cannot use it)`.
- **A laws-only file does not check.** Open laws count as TODOs, so
  `node bend2/main.ts src/nat.bend` exits 1 with
  `Error: 84 TODOs found. The code is incomplete, and not a valid proof
  yet.` — and the count is transitive over imports (int.bend reports 22 on
  its own, since it imports only `Base`; qext.bend 24 = 22 Int + 2 QExt).
  This is expected; the `*_proofs.bend` files are the gates that print
  `All terms check.`
- **Defs are not laws**: a def a law *statement* needs (`Cmp.flip` in
  `cmp_antisym`, `flip_eq_lt`, ...) must live in the laws file; anything
  only proofs touch (`CmpIsEQ`, `CmpIsGT`, `NatIsPos`, `Nat.pred`) moves
  to the proofs file. int.bend used to need `import ./nat.bend as N` for
  `N.Cmp.flip` in `Int.add.opp_comm`; with the `(pos, neg)` representation
  no Int law statement mentions `Nat` at all, so int.bend imports only
  `Base` and the transitive TODO count no longer includes nat.bend.
- **Files with a `main`** that returns a value print only the normalized
  value, not `All terms check.` — scratch.bend printing
  `(src/int.Int{10n, 5n}, src/int.Int{10n, 5n})` with exit 0 *is* the pass
  signal there (both sides of `(3 + -5) + 7` land on the same non-canonical
  representative of 5, which is what `(pos, neg)` equality looks like).

## Gotchas

- **No nested matches on pattern variables** ("scrutinees in binder
  order"). Flatten: `case Int{False{}, xm} Int{True{}, ym}:` instead of
  matching the constructor fields in a second `match`.
- **Cross-module dotted names compose verbatim**: `Cmp.flip` defined in
  `nat.bend` is `N.Cmp.flip` after `import ./nat.bend as N`. Consider
  prefix-free names per file.
- **`match` scrutinees must be parameters or pattern-bound variables**,
  never computed values -- and never *let-bound* values either. Pass
  `Nat.cmp(xm, ym)` to a helper and match on the helper's parameter. This
  is why `Int.add.opp` takes `c: Cmp` as its first argument — and it makes
  the op *proof-friendly* for free (proofs can then call the helper with a
  literal `Cmp`). See the Rat section for the pending-binder rule behind
  it, and for what it costs when the thing to destructure comes out of a
  function call.
- **No `if`**: a branch is a `match` on `True{}`/`False{}`, and there is
  no `Bool` short-circuit sugar in proofs.
- **Termination is structural, left-to-right by argument**: the recursive
  call's arguments must pass unchanged until one is a strict subterm. Put
  the decreasing argument first and keep the others literally unchanged
  (`add_assoc(ap, b, c)`, not `add_assoc(ap, c, b)` reordered by
  rewriting).
- **Parsing**: `1n+x` is sugar for `Succ{x}` and chains (`1n+1n+x`).
  `-`/`+` glued to a name starts a binder, not an operator; space your
  operators. A parameterless `def` still needs its empty list: `def f() -> T:`
  parses, `def f -> T:` fails with `expected : '('` / `observed : '-'`.

## Int.add_assoc campaign (historical: sign-magnitude `Int`)

Kept as the record of what the old representation cost. Under the `(pos, neg)`
`Int` this whole campaign is seven lines (see the next section); nothing below
applies to the current `src/int.bend`. The `Nat` inventory it forced into
existence (`ci1`..`ci10`, the `cmp_*` bridges) is still in `src/nat.bend` and
is still what `Int.canon` and gcd will want.

How `Int.add_assoc` actually fell (int.bend 494 → 890 lines, no new Nat
lemmas needed — the ci1..ci10 inventory built for it covered everything):

- **Case split**: 8 sign patterns. fff/ttt reduce to `Nat.add_assoc`;
  ftf was the direct grind (9 cmp-combos, many absurd). fft and ttf are
  sign mirrors of each other, ground directly. The rest fell to symmetry:
  `Int.add.assoc.rev` (assoc of the reversed triple + `Int.add_comm` =
  assoc, a 5-step `Equal.trans` chain) gives tff from fft and ftt from
  ttf for free, and tft is two ttf instances plus three comms. Prove 3
  patterns directly, derive 3, reuse 2 — write `rev` before grinding.
- **A motive cannot mention a variable you still need to `match` on**
  ("scrutinees in binder order: unbound, consumed, or out of order").
  `%e : P` where `P` names `c` consumes `c`. So: `match c:` FIRST, then
  `%e` inside each branch — matching refines `e : {c == cmp(..)}` to
  `{GT{} == cmp(..)}` etc., which is what `%e` needs. Cost: the `%e`
  rewrite lines are duplicated per branch (fft.pos has 9 branches × 2).
- **sym-orientation was 100% of the ftf breakage.** `%e` replaces
  RHS-of-`e` occurrences; goals almost always contain the lemma's
  *complicated* LHS (`Nat.add(Nat.sub(xp,ym),ym)`, `Nat.sub(z,Nat.sub(y,x))`),
  so wrap nearly every ci/geometry lemma in `Equal.sym` before `%`.
  Also: `Equal.sym(T, a, b, e)` takes `e : {a == b}` and gives
  `{b == a}` — twice the fix was deleting a double-sym or swapping the
  two endpoint args, and the checker's expected/observed pair names the
  exact mismatch.
- **`cmp_add_sub` is the bridge that kills a parameter.** In fft/ttf the
  outer cmp is on `cmp(1+(xp+ym), zm)` and the inner one on
  `cmp(1n+xp, Nat.sub(zm, ym))`; instead of a third `Cmp` parameter with
  flipped evidence (the ftf.ltgt pattern), `cmp_add_sub` rewrites one
  into the other outright when `zm > ym`. Fewer helper laws, shorter
  statements.
- **The four impossible (c1, c2) combos in fft.pos/ttf.pos** all close
  by `cmp_gt_add_left` (or `cmp_gt_add` after a `cmp_eq`-transport) +
  `eq_ne_gt`/`lt_ne_gt` discrimination. Note `cmp_gt_add(a, b)` proves
  `cmp((1+b)+a, a) == GT` — the increment is the *second* argument.
- **Zero-magnitude sub-cases** (`Int.add.same`'s `Int.mk` branch): a
  `w == 0 + w` goal with `w` an `Int.add.opp` result needs the cmp
  exposed as a parameter (zl helpers), and its GT/LT branches need
  `sub_pos` to rewrite `Nat.sub(a,b)` to `1n+..` twice (once per
  occurrence) so `Int.mk` and `Nat.cmp(0n, ..)` unstuck by reduction.
- Cost reality check: the "300–500 lines" estimate below landed at +396,
  but ~120 of that is mechanical mirror text (ttf = fft with signs
  swapped) and per-branch `%e` duplication.

## Why Int is a (pos, neg) difference pair

The trigger was `Int.mul_distrib`, which turned out to be **false** under the
sign-magnitude representation, not merely unproved. `Int.add` canonicalized
its zero (through `Int.mk`), `Int.mul` did not, so the two sides of
distributivity disagreed on the *representation* of 0:

    Int.mul(Int{True,0}, Int{False,1} + Int{True,1}) = Int{True,0}
    Int.mul(Int{True,0},Int{False,1}) + Int.mul(Int{True,0},Int{True,1}) = Int{False,0}

and it fails even for the canonical zero: x = `Int{False,0}`, y = `Int{True,3}`,
z = `Int{False,1}` gives `Int{True,0}` against `Int{False,0}`. It holds only
for nonzero x. Making `Int.mul` canonicalize through `Int.mk` fixes it, but
`Int.mk` matches on its magnitude, so `Int.mul(Int.mk(s,m), y)` is a *stuck*
term while `m` is symbolic — which then infects every composite product in
every downstream proof. Two unfolding laws (`Int.mul.mk_left`,
`Int.mul.mk_right`, stated flipped so `%e` fires left-to-right) unstick just
the existing laws; the distributivity proof itself would still need sign cases
crossed with magnitude cases crossed with cmp cases.

`Int{pos, neg}` = `pos - neg` removes the problem at the root: every operation
is a constructor, so nothing is ever stuck and no law sees a case split.

Measured on a throwaway prototype of the same five laws, before committing:

| law | `(pos, neg)` proof lines | sign-magnitude proof lines |
|---|---|---|
| `add_comm` | 7 | 13 |
| `add_assoc` | **7** | **545** (+ ~124 lines of helper-law statements) |
| `mul_comm` | 14 | 7 |
| `mul_distrib` | **17, one branch, zero case analysis** | not proved; false as stated |
| `mul_assoc` | 38 (two `Nat`-half chains + assembly) | 9 (+16 lines of `Int.mul.mk_*` unfoldings) |

The trade, stated plainly so nobody re-derives it the hard way: `Int` is now a
*presentation*, not a canonical form. `Int{1,0}` and `Int{2,1}` are both 1 and
are not `==`, so `==` no longer decides equality. That obligation moves to
`Int.canon` (a `Nat.cmp` on the two sides) plus its quotient lemma
(`canon x == canon y` iff `xp + yn == yp + xn`), and then to `Rat`
normalization. It does not disappear — it relocates to exactly the gcd
territory that was always going to be the hard part, which is the right place
for it: the ring laws are bookkeeping, and `(pos, neg)` makes them formal.

## Splitting a law into its two Nat halves

When a `Z`-level goal is two independent coordinate equations, prove the
coordinates as their own laws and assemble:

    def Z.mul_assoc(x, y, z):
      match x y z:
        case Z{xp, xn} Z{yp, yn} Z{zp, zn}:
          %Equal.sym(Nat, <pos LHS>, <pos RHS>, Z.mul_assoc.pos(xp, xn, yp, yn, zp, zn))
            : {Z{_, <neg LHS>} == Z{<pos RHS>, <neg LHS>} : Z}
          %Equal.sym(Nat, <neg LHS>, <neg RHS>, Z.mul_assoc.neg(xp, xn, yp, yn, zp, zn))
            : {Z{<pos RHS>, _} == Z{<pos RHS>, <neg RHS>} : Z}
          {==}

Each chain's `%e` annotations then spell only one coordinate instead of the
whole goal — roughly half the text — and the assembly is three lines. The
`Equal.sym` is needed to orient the half-law's equation so `%` replaces the
half-LHS with the half-RHS; state the halves either way round, but pick one
and say so in the law comment.

## Rough cost model (calibrated on this spike)

- Nat lemma (comm/assoc class): ~15 lines, minutes each once the style
  clicks.
- Discrimination bridge: ~10 lines each, write the set once.
- mul_distrib-class shuffle: ~25 lines, the trans chain is the bulk.
- Int law under `(pos, neg)`: 3–8 lines each (`{==}` when the operation is
  structural in the right way, e.g. `Int.neg_invol`, `Int.neg_add`,
  `Int.sub_eq_add_neg`); a shuffle (distributivity, associativity) is 15–40.
  Under sign-magnitude the same laws were 7–545.
- `Rat` with gcd normalization needs a division correctness proof — the
  hardest single lemma on the path to the field axioms.
- `Nat` is unary in *proof land* only. A proof-land literal is a tower of `Succ`
  around `Zero` (`bend.ts:2245`), so literal size is term size and each `Nat`
  operation recurses over that tower; the compiled lanes are binary already (C:
  `Nat` is W64, `nat_add`/`nat_mul`/`nat_divmod` are native ops; JS: BigInt).
  Proofs don't care; CAD-sized coordinates will. A binary-nat layer for proof
  land is the right next investment. (This bullet said "O(value) at runtime"
  until the correction that the runtimes are binary.)

## The Rat route: remaining plan

State at handoff (updated after the Rat normalization unit): `Int` is
`Int{pos, neg}` = `pos - neg` with all 19 ring laws proved; `Int.canon` (+
`canon.pos`, `canon.neg`, `canon.idem`, `canon.scale`) is in, and so is the
quotient lemma in both directions (`Int.canon.eqv.fwd` / `.bwd`); the Nat
scaling groundwork (`cmp_add_left`, `cmp_mul_right`, `mul_sub_add`,
`sub_of_add`, `mul_sub`, `mul_one`) is in. `src/rat.bend` has the type,
`Rat.mk`, the operations, `Rat.mk.scale`/`Rat.mk.eqv` (so `==` decides rational
equality on canonical values) and the identity laws; the Rat laws that compose
two normalized results are still open. See "Rat: what the normalization cost"
for that work's shape and its traps.

Check with (from a bend checkout):

    cd /home/bepis/prog/verus-cad/bend
    node bend2/main.ts ../bend-quadratic-extension/src/nat_proofs.bend
    node bend2/main.ts ../bend-quadratic-extension/src/int_proofs.bend
    node bend2/main.ts ../bend-quadratic-extension/src/qext_proofs.bend
    node bend2/main.ts ../bend-quadratic-extension/scratch.bend

All four must print `All terms check.` (scratch prints a value instead). The
laws-only files are *supposed* to fail with `Error: N TODOs found.`

### The target

`Rat{num: Int, den: Nat}`, canonical when `den` is positive, `num` has one
side zero (i.e. is `Int.canon`'s output), and `gcd(num.pos + num.neg, den)`
is 1. `Rat.mk(n, d)` normalizes; `==` on canonical `Rat`s then decides
rational equality.

### The key move: prove canonicality by scaling, not by coprimality

To make the field axioms work you need the **forward** direction only:

    n1 * d2 = n2 * d1  implies  Rat.mk(n1, d1) == Rat.mk(n2, d2)

Get it from `norm(n*k, d*k) == norm(n, d)` for `k >= 1`, applied to
`(n1*d2)/(d1*d2)` on both sides. That needs:

- `Int.canon.scale`: `canon(x * K) == canon(x) * K`, where `K = Int{k, 0n}`
  and `k >= 1`. (Careful: `k = 0` is a separate branch, where
  `Int.mul_zero` collapses both sides to `Int{0n, 0n}`.)
- `gcd(m*k, d*k) == k * gcd(m, d)`.
- exact-division cancellation: `div(p*k, g*k) == div(p, g)` when `g | p`.

This deliberately avoids Euclid's lemma and coprime-ness (`gcd = 1` plus
`b | a*x` implies `b | x`), which are the deep part of "gcd correctness". The
*reverse* direction — `Rat.mk(n1,d1) == Rat.mk(n2,d2)` implies
`n1*d2 = n2*d1` — is trivial, because two equal canonical `Rat`s have equal
fields. What is *not* needed anywhere is that gcd is the *greatest*.

### Nat division correctness

`base.bend` has `Nat.divmod.go(n, m, d, r)` (fuel = `n`, structural) and
`Nat.divmod(a, b) = divmod.go(a, bp, 0n, 0n)` for `b = 1+bp`. With
`b = 1+bp`, the loop state satisfies

    a = d*b + r + n        and        r + m + 1 = b

(initially `n=a, m=bp, d=0, r=0`; each step either bumps `d` and resets
`r` when `m` runs out, or bumps `r`). At `n = 0` that gives
`div(a,b)*b + mod(a,b) == a` and `mod(a,b) < b`. Project the pair with
`Nat.div.fin` / `Nat.mod.fin` — a law statement cannot destructure.

The loop invariant is the whole proof; state it as a law parameterised by
`n, m, d, r, b` with the `r + m + 1 == b` hypothesis, and induct on `n`
(structural, and `n` is the first parameter, so the descent check passes).

### Nat gcd

Euclid's descent is *not* structural, so gcd has to be fuel-driven, exactly
like `divmod.go`. Keep the fuel first so the descent check passes:

    def Nat.gcd.go(s: Nat, y: Nat, c: Cmp, x: Nat) -> Nat:
      match s:
        case 0n: 0n                       # unreachable with enough fuel
        case 1n+sp:
          match y:
            case 0n: x
            case 1n+yp:
              match c:                    # c = cmp(x, y), passed in
                case EQ{}: x
                case LT{}: Nat.gcd.go(sp, Nat.sub(y, x), Nat.cmp(x, Nat.sub(y, x)), x)
                case GT{}: Nat.gcd.go(sp, Nat.sub(x, y), Nat.cmp(Nat.sub(x, y), y), Nat.sub(x, y))

    def Nat.gcd(a: Nat, b: Nat) -> Nat:
      Nat.gcd.go(Nat.add(a, b), b, Nat.cmp(a, b), a)

Match `s` then `y` then `c` — that *is* binder order (s, y, c, x), so it is
legal; matching out of order is not. The subtractive step is what makes
scaling easy: `gcd(m*k, d*k) == k*gcd(m,d)` then follows from `mul_sub`
plus the fact that each step lowers `x + y` by `min(x,y)`, so fuel `a + b`
suffices. A `mod`-based Euclid would instead need `(m*k) mod (d*k) = k*(m mod d)`,
i.e. more division correctness.

### Idioms this work will need, restated

- **Evidence as a parameter.** A `match` scrutinee must be a parameter or a
  pattern-bound variable, never a computed value, and a body that matches a
  *stuck* `Nat.cmp` never reduces. So every lemma about `Int.canon` takes
  `c: Cmp` plus `e: {c == Nat.cmp(xp, xn)}`, and callers with no comparison
  to hand pass `c := Nat.cmp(xp, xn)` with evidence `{==}`.
- **Unsticking `Nat.sub`.** `Nat.sub(a,b)` is stuck while `a` is symbolic, so
  anything downstream of it (a `Nat.cmp`, an `Int.mk`-style match) is stuck
  too. `sub_pos` rewrites it to `1n+Nat.sub(a,1n+b)` given `cmp(a,b) == GT`,
  which makes it a constructor and lets everything reduce. This is the single
  most-used move in the existing proofs.
- **`%e : P` orientation.** `P` is the goal with `_` at an occurrence of the
  *RHS* of `e`; the rewrite puts the *LHS* there. To rewrite the other way,
  `Equal.sym` first. `Equal.sym(A, a, b, e)` takes `e : {a == b}` and gives
  `{b == a}` — get the two endpoints the right way round or the rewrite
  silently does nothing.
- **Reading errors.** For `{==}` the checker prints `expected` = the goal's
  left side and `observed` = its right side. For a `%` step it prints
  `expected` = the actual goal and `observed` = the annotation you wrote. A
  long `expected`/`observed` pair that looks identical usually means an
  annotation was transcribed with the wrong sub-term somewhere.
- **Splitting a law into Nat halves.** When a goal is two independent
  coordinate equations, prove the coordinates as their own laws and assemble
  with two `Equal.sym` rewrites; each chain then spells half as much.

### Order to work in

1. `Nat.divmod` correctness (loop invariant) and the `div`/`mod` laws it
   gives. This blocks everything else. **Done** (`divmod.go.spec`,
   `divmod.go.mod_lt`, `div_add_mod`, `mod_lt`).
2. `Nat.gcd` + `gcd` divides both arguments + `gcd(m*k, d*k) == k*gcd(m,d)`.
   **Done**: scaling (`gcd.go.scale`, `gcd.go.fuel`, `gcd_scale`) and
   divisibility (`gcd.go.divides`, `gcd.divides_lt`/`gcd.divides_gt`,
   `gcd_divides`) -- see the last section for what the divisibility half cost.
3. `Int.canon.scale`, and `Int.canon.eqv` (the quotient lemma,
   `canon x == canon y` iff `xp + yn == yp + xn`). **Done**: scaling
   (`Int.canon.scale.go`/`Int.canon.scale`) and both halves of the quotient
   lemma (`Int.canon.eqv.fwd`, `Int.canon.eqv.bwd`), on top of the Nat
   cross-sum lemmas `cross_gt_gt`/`cross_cmp` -- see the last section for the
   route that turned out to be cheaper than the plan.
4. `Rat`: the type, `Rat.mk`, canonicality by the scaling route, then the
   field axioms. **Partly done**: the type, `Rat.mk`, the normalization lemmas
   (`mk.canon`, `mk.zero`, `mk.fixed`, `mk.scale`, `mk.eqv`), the commutations
   and the identity laws are in; the laws that compose two normalized results
   are not -- see "Rat: what the normalization cost".
5. `QExt` over `Rat`: field axioms plus the inverse
   `1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2*d)`.

Commit each unit once its gate is green; do not leave a law stated but
unfilled, since that turns every dependent gate into `N TODOs found.`

## Where the trust boundary is

`All terms check.` means the (human-written, per `AGENTS.md`) kernel in
`bend2/bend.ts` accepted the proofs. The README admits the Lean
formalization lags the checker and the theory rests partly on invariants
outside the kernel. Treat the proofs as strong evidence, not bedrock, and
re-check after any compiler upgrade.

## Nat divmod and gcd: what the work actually cost

Steps 1 and half of 2 above are done; `src/nat.bend` carries the laws and
`src/nat_proofs.bend` the fills. Notes for the next attempt.

### Two bugs in the gcd sketch above

The `Nat.gcd.go` sketch in "Nat gcd" does not compute the gcd as written.

- **The GT step.** `Nat.gcd.go(sp, Nat.sub(x, y), Nat.cmp(Nat.sub(x, y), y),
  Nat.sub(x, y))` puts the difference in the *y* slot as well as the x slot,
  so the state collapses to `(x-y, x-y)` and the loop answers `x-y` or 0.
  Run on literals (a `main` returning `G.gcd(...)` prints the value; write it
  down *before* proving anything): the sketch gives `gcd(10, 4) = 0` and
  `gcd(7, 5) = 2`, and the one-token fix -- the GT step leaves y alone,
  `Nat.gcd.go(sp, y, Nat.cmp(Nat.sub(x, y), y), Nat.sub(x, y))` -- gives
  `2` and `1`. A wrong loop is cheap to find this way and expensive to find
  through a failing proof: the scaled-gcd proof below fails on the sketch's
  version, which is how it surfaced here.
- **`a = 0.`** `Nat.gcd(0, b)` with the sketch's fuel `a + b` runs the LT
  step `(0, y) -> (0, y - 0) = (0, y)`, which never progresses: it burns the
  whole fuel and returns 0, but `gcd(0, b)` is `b`. `src/nat.bend` matches on
  `a` first (`case 0n: b`) so the loop only ever sees `x >= 1` -- which is
  also what makes the fuel `a + b` *provably* enough, since every step then
  strictly shrinks `x + y`.

### The gcd scaling proof, restated

`gcd_scale` needs two loop lemmas, and the shapes are not free choices:

- `gcd.go.scale`: `go(s, y*k, cmp(x*k,y*k), x*k) = k * go(s, y, c, x)`, for
  *every* fuel (both sides run out together), no hypothesis beyond
  `c = cmp(x,y)`. Each step is two rewrites: `cmp_mul_right` to collapse the
  scaled comparison to the branch constructor, `mul_sub` to collapse the
  scaled difference. The multiplier must sit on the right of each product
  (`Nat.mul(y, 1n+kp)`), because that is the shape `cmp_mul_right` and
  `mul_sub` are stated in; the k-on-the-left spelling has no counterpart for
  `cmp` (`cmp_add_left` does not apply to a product).
- `gcd.go.fuel`: fuel above the state's own measure is harmless. State it over
  a fuel `s1` *and* the slack `t` with `(x + y) + t = s1`, and induct on
  `s1`, **not** on the slack: one loop step takes `s1 = 1 + sp` to `sp` on
  both sides while the *difference* between the two fuels rides along
  untouched, so an induction on the difference never closes.
- `Nat.gcd(m*k, d*k)` runs the loop with fuel `m*k + d*k` while
  `Nat.gcd(m, d)` runs it with `m + d`, so the two loops cannot be matched
  directly at all: `gcd_scale` is `gcd.go.scale` at the big fuel, then
  `add_mul_slack` to see that fuel as `m + d` plus a slack, then `gcd.go.fuel`
  to throw the slack away, then one `Nat.mul_comm` for the product order.
- The state's x slot has to be written `1n + xp` in `gcd.go.fuel` (and in any
  law that reuses it), because the canonical fuel `x + y` must start with a
  *constructor* or the right-hand loop is stuck on its fuel match. The cost is
  that every law of this family needs `sub_pos` to undo the loop's own
  `Nat.sub` in the GT branch before the induction hypothesis applies.

### "gcd divides both arguments": solved, and what the obstacle actually was

Proved. The laws are `gcd.go.divides` (the loop invariant), `gcd.divides_lt` /
`gcd.divides_gt` (one step each, as helper laws) and `gcd_divides` (the top
level); the fills are in `src/nat_proofs.bend`, and the shape of the witness
type in `src/nat.bend` is part of the proof, not a style choice.

The arithmetic was never the problem. The step needs the quotients and the
equations from *both* halves of the induction hypothesis's witness pair, plus
the pair back, and the checker's rules around that cost three attempts:

1. `match` refuses a computed scrutinee ("a match cannot scrutinize a computed
   value"), so the returned pair cannot be taken apart where it is produced.
   The step therefore runs inside a helper `def` whose binder *is* the pair, and
   the recursive call's result is passed straight in as that binder -- the pair
   is never destructured in place.
2. Fields of a `Sigma` are linear and each quotient/equation is needed twice, so
   the fields have to be copied. `Sigma<&2, &2, ..>` does not do it (a field's
   *own* quantity is what counts, and `Tuple`'s default is `&1`).
3. The copy spelling `+e = e` (or a `+e` pattern field) is where the checker
   stops. `+p = p` makes it *re-check the field's type*; for a `Sigma` that type
   is the dependent field `B(fst)`, which after whnf sharing arrives as
   `App(Var("_", -1, <the lambda>), fst)` -- an application whose head is a
   *cell holding a lambda*. `term_infer`'s App rule beta-steps a literal `Lam`
   head but not a cell wrapping one, so inference falls to the `default` branch
   and reports `expected : an annotated term (cannot infer) / observed : q => {x
   == Nat.mul(g, q) : Nat}`, with the span pointing at `Nat.divides`'s body --
   the lambda's own source. The check that triggers it is `check-let`'s
   `term_check(v_inf.ty, .., Typ(Qua(lhs_kind(lhs, q))))`: the `Let` is the
   re-bind, `v_inf.ty` is the field type, and inferring *that* is what dies.
   (Traced with a throwaway patched copy of the checker in `/tmp`, never
   touching `bend2/`: the diagnostic there is `console.error(new
   Error().stack)` inside `Err` plus a dump of `tm.k[j]`, `tm.v[j]` and
   `v_inf.ty` in `check-let`. That is the cheap way to localize this class of
   failure.)

Two properties of a `+field` in a hand-written `Data` ADT make all three
problems disappear, and that is what `Nat.Div` is:

    type Nat.Div<+g: Nat, +a: Nat> is Data:
      Div{+q: Nat, +e: {a == Nat.mul(g, q) : Nat}}

- a `+field` is Many *at the declaration*, so a plain pattern already yields it
  Many and no re-bind is ever written -- nothing to type-check, nothing to
  break;
- a constructor's field types mention its own earlier fields *directly*, so
  there is no family parameter applied to `fst` and no cell-headed redex is
  ever rebuilt;
- the pair itself is not copied (each half is destructured once), so
  `Nat.divides_both` can stay the `A & B` `Sigma` it was.

Two shape details that are not free choices:

- the destructure pattern must be the ADT's own constructor (`NL.Div{q, e} =
  d`); `(q, e) = d` is a `Tuple` pattern, and the checker reports "a constructor
  of Nat.Div (missing, or already matched)".
- `gcd.divides_gt`'s `d` parameter is `Nat.divides_both(g, 1n+xp, y)`, *not*
  `Nat.divides_both(g, s, y)`: `gcd.go.divides` always states the state's x slot
  as a successor, so the recursive call's first dividend is literally `1n + xp'`
  and a law stated over an arbitrary `s` cannot be fed it. The GT branch of the
  loop rewrites the goal with `sub_pos` first (replacing the stuck
  `Nat.sub(xp, yp)` with `1n + Nat.sub(xp, 1n+yp)` in both places the loop term
  mentions it) and then needs `ge_sub_add` rather than `cmp_gt_sub_add` for the
  helper's equation, since the helper's subtraction is now `xp - (1+yp)`.
  `Equal.cong(Nat, Nat, u => 1n+u, ..)` adds the successor.

Cost: `nat.bend` +~90 lines of statement and comment, `nat_proofs.bend` +~120 of
fill. The two helper laws and the loop induction were each right on the first
run once the witness type was a `Data` ADT with `+` fields.

The same trick is the general lesson: **when a proof has to use a witness twice,
give the witness a `Data` ADT with `+` fields rather than an `Exists`, and never
write a `+` re-bind.**

## Int.canon: what the scaling and quotient lemmas cost

`Int.canon.scale` (`canon(x*(1+kp)) == canon(x)*(1+kp)`) and both halves of the
quotient lemma (`Int.canon.eqv.fwd`: equal canonical forms force
`xp + yn == yp + xn`; `Int.canon.eqv.bwd`: the reverse) are proved. Notes for
whoever picks up the rest.

### Shape: thread the comparison, or you cannot case on it

`Int.canon.go`'s body matches on its `Cmp`, and `Nat.cmp(xp, xn)` is a computed
value -- not a legal match scrutinee -- so *every* law that reasons about canon
per branch takes `c: Cmp` plus `e: {c == Nat.cmp(xp, xn)}` as parameters and
spells the right-hand canon as `Int.canon.go(c, xp, xn)`. That is why
`Int.canon.scale.go` exists next to the statement anyone wants to use
(`Int.canon.scale`), which is one call with `c := Nat.cmp(xp, xn)` and `{==}`.

### Scaling is bookkeeping, not mathematics

`Int.mul(Int{xp, xn}, Int{1+kp, 0})` reduces to
`Int{add(xp*(1+kp), xn*0), add(xp*0, xn*(1+kp))}`. The `Nat.mul`-by-zero slots do
*not* reduce (`Nat.mul` matches on its first argument, a variable), so each
branch starts with `mul_zero` and `add_zero` rewrites; each of those fires in two
places at once (the `Nat.cmp` argument and `canon.go`'s own argument), which is
what a motive with the hole repeated is for. `cmp_mul_right` then collapses the
scaled comparison, the branch evidence collapses it to the constructor just
matched, and `mul_sub_right` (already in nat.bend, the right-scaled twin of
`mul_sub`) says the scaled difference is the difference of the scaled slots. The
one non-obvious spelling: `e` has to be a `+` binder, because the GT and LT
branches read it twice. An equation is `Data`, so a `+` equation binder costs
nothing -- and unlike a `+` *field* of a Sigma it is not a dependent type, so the
copy is unremarkable.

### Int.eq.pos / Int.eq.neg: constructor injectivity, and the projections it needs

`Int.canon.eqv.fwd` needs to get `a == c` out of `{Int{a, b} == Int{c, d}}`. Bend
has no injectivity rule, so it is the J axiom (`%e : P`) with a motive whose two
sides are *projections* of the two Ints:

    %e : {Int.proj.pos(Int{a, b}) == Int.proj.pos(_) : Nat}

At `_ := Int{c, d}` that motive is the goal `{a == c}`, and at the left-hand
Int it is `{a == a}`, which `{==}` closes. The projections
(`Int.proj.pos` / `Int.proj.neg`) are proof-only defs in `int_proofs.bend`; no
law statement mentions them. This is the general recipe for extracting a
constructor's fields from an equation in Bend: define the projection as a *def*
(a motive cannot contain a `match`), then use it in the J motive.

### The forward half: nine branches, two shapes

Case on `c1` and `c2`. The canon forms are `Int{sub(xp,xn), 0}` (GT),
`Int{0, sub(xn,xp)}` (LT) and `Int{0,0}` (EQ), so:

- **the two forms agree** (GT/GT, LT/LT, EQ/EQ): `Int.eq.pos` / `Int.eq.neg`
  turn the Int equation into a coordinate equation, and the goal is then Nat
  shuffling -- `cmp_gt_sub_add` / `cmp_lt_sub_add` say the coordinate is the
  difference, so both sides are "difference + common part" and the equation
  follows by reassociating.
- **they disagree** (a difference against zero, or differences of opposite
  sign): the coordinate equation says a truncated difference is `0`, `sub_pos`
  says that same difference is `1 + something`, and a successor is not zero.
  That last step is `Nat.succ_ne_zero` (`0 = 1 + a` is impossible), stated over
  `0` on the left because that is the orientation the callers build, with
  `NatIsZero` as the discrimination -- both proof-only, next to `Nat.pred` in
  nat_proofs. `Empty.absurd` then closes the branch, which is why the goal type
  has to be written out in those branches.

The one thing that cost real time here was `%`-orientation, twice per branch:
`Equal.sym(A, a, b, e)` takes `e : {a == b}` and gives `{b == a}`, and its
endpoints are *erased* -- so whatever you write as the second argument is what
ends up on the left, and the checker does not complain if it disagrees with `e`.
The reliable spelling is: to replace the goal's subterm `X` with `Y`, write the
evidence `{Y == X}`, i.e. `Equal.sym(T, X, Y, <lemma stated {X == Y}>)`.

### The backward half: proved, and the plan it did not need

`Int.canon.eqv.bwd` is in the tree (statement in `src/int.bend`, fill in
`src/int_proofs.bend`), so the two halves together are the quotient lemma. The
plan above works, but it is not the cheap route: the disagreeing branches need
neither three helper laws nor `sub_pos`/`succ_ne_zero`, and the agreeing
branches want their `add_cancel` chain *factored into Nat* rather than written
inline twice. Two moves replaced the whole thing:

- **State the whole case analysis as one lemma whose conclusion is what the
  caller refutes.** `cross_cmp` (`src/nat.bend`) concludes `{c1 == c2 : Cmp}`,
  so its own fill has no case split at all: `cmp_add_right` says adding the
  same amount to both sides preserves a comparison, so the cross sum rewrites
  `cmp(add(xp,yn), add(xn,yn))` (which is `c1`, by `cmp_add_right(xp,xn,yn)`)
  into `cmp(add(yp,xn), add(yn,xn))` (which is `c2`, same law on the other pair
  plus `add_comm`) -- congruence and commutation, no arithmetic, one `Equal`
  chain. The *caller* then refutes the equation with whichever of the six
  discrimination laws names its branch (`gt_ne_eq`, `gt_ne_lt`, `eq_ne_lt`, ...:
  the file ships all six orientations), which makes each of the six vacuities
  two lines. Compare the plan's three GT/EQ, GT/LT, EQ/LT laws, each with its
  own induction and its own `sub_pos`/`succ_ne_zero` endgame: one lemma whose
  fill is a `trans` chain beats three whose fills are case analyses.
- **Push the arithmetic down to a Nat law whose statement *is* the caller's
  goal.** `cross_gt_gt` states GT/GT as the Nat equation
  `sub(xp,xn) == sub(yp,yn)`; its fill expands both differences with
  `cmp_gt_sub_add` and cancels the common `add(xn,yn)` -- that is the plan's
  6-link chain, written once, in Nat, where no goal-orientation decision is
  left to get wrong. LT/LT is the same law with the two arguments swapped
  (`cmp_gt_of_lt` flips both evidences, the cross sum is commuted, and the
  conclusion `sub(xn,xp) == sub(yn,yp)` is exactly what the LT canon form
  holds), so the second agreeing branch costs no new mathematics either.

What is left in the Int fill is nine branches of assembly -- a `Equal.cong`
into the `Int` constructor for the two agreeing non-zero branches, `Empty.absurd`
for the six vacuities and `{==}` for EQ/EQ -- and the only thing that needs
care there is that the goal in a branch has already reduced
(`canon.go(GT{}, ..)` is `Int{sub(xp,xn), 0n}`, which is what the `cong`'s
endpoints and the `Empty.absurd` goal have to spell).

`Int.canon.eqv` as a single "iff" statement is still not in the tree: what the
two halves give is the pair of implications, and the `Rat` route consumes only
the forward one (`canon.scale`), with the reverse direction of the *quotient*
lemma coming for free because two equal canonical `Rat`s have equal fields.


### Small harness facts that cost time

- A law may conclude a pair type (`{A} & {B}`), but *inside braces* the parser
  reads `&` as the exists binder and fails on the missing `:`: a pair type
  must be written bare (`Empty.absurd(A & B, e)`) or, better, behind a `def`
  (`Nat.divides_both`), which also keeps `%` motives to a single application.
- A proof-only helper `def` must be named *bare* (`Nat.pred`,
  `Nat.succ_add_ne_zero`), not `NL.`-prefixed: an `NL.`-prefixed name lives in
  nat.bend's namespace, resolves while nat_proofs.bend is the main file, and
  becomes "a defined name is expected" as soon as another file imports it.
- `%e : P` replaces the *right* side of `e` with its *left* side. Restated as
  a rule to write code by: **to replace a goal subterm X with Y, the evidence
  must be `{Y == X}`.** Every orientation mistake in this work was forgetting
  that and reaching for `Equal.sym` in the wrong place (and `Equal.sym(A, a,
  b, e)` itself takes `e : {a == b}` and gives `{b == a}`).
- A `%` motive may mention the hole more than once, and that is how two
  occurrences of the same stuck subterm get rewritten together (`sub_pos` on
  the GT branch touches four positions in one step).
- A `%` motive that is not an equation must be written *without* braces. `{P}`
  parses as the annotation form `{x : T}` and fails with `expected ':' observed
  '}'`; `{a == b}` is the equation form. So a motive that is a bare predicate
  application (`Nat.divides_both(..)`) goes in bare:
  `%e : NL.Nat.divides_both(<hole>, ..)`.
- A destructure pattern must name the constructor the scrutinee's type actually
  declares: `(q, e) = d` only ever matches `Sigma`/`Tuple`, so a hand-written
  witness ADT needs `Div{q, e} = d`. The error when you forget is `a
  constructor of <your type> (missing, or already matched)`.
- `+field`s in a hand-written `Data` ADT are the copy mechanism that works: a
  `+` re-bind or `+` pattern field of a *Sigma* field makes the checker re-check
  the dependent field type `B(fst)`, which after whnf sharing is an application
  whose head is a share cell holding a lambda -- `term_infer` cannot see through
  the cell and reports `an annotated term (cannot infer)`. `Data` ADT `+field`s
  are Many by declaration, so a plain pattern suffices and nothing is
  re-checked.

## Rat: what the normalization cost

`src/rat.bend` / `src/rat_proofs.bend` are in the tree: the type, `Rat.mk`, the
operations (`add`, `neg`, `sub`, `mul`, `zero`, `one`), the normalization lemmas
and the identity laws. `Rat.mk.scale` (`mk(n*(1+kp), d*(1+kp)) == mk(n, d)`) and
`Rat.mk.eqv` (`n1*d2 == n2*d1` implies `mk(n1,d1) == mk(n2,d2)`) are the point
of the whole exercise -- `==` on canonical Rats decides rational equality -- and
both are proved, and so is the value keystone `Rat.mk.value`
(`num(mk(n,d))*d == n*den(mk(n,d))`) that the composing laws need. Notes from
doing it; the first three are what the value lemma hit.

### Rat.mk is match-free on purpose, and that is what makes it provable

`Nat.div`/`Nat.gcd` are total functions, so the normalization needs no case
split of its own:

    Rat.mk.go(np, nn, d) = Rat{Int{div(sub(np,nn), g), div(sub(nn,np), g)}, div(d, g)}

for `g = Rat.g(np, nn, d) = gcd(sub(np,nn) + sub(nn,np), d)`, and `Rat.mk(n, d)`
just destructures `n` and calls it. Nothing in the definition matches on a
comparison, so the result is a constructor whose fields are `div`/`gcd` terms
and never a stuck `match`. Every case split therefore lives in the laws, where
the comparison can arrive as a parameter (`c: Cmp` with its evidence) exactly as
`Int.canon` does it. The numerator it produces is the difference pair
`sub(np,nn), sub(nn,np)`, which has one side zero by construction -- that is the
"canonical shape" the rest of the file assumes, and it costs nothing.

### A def application reduces only through its *arguments*, so laws go in the `go` spelling

This is the trap that decides the shape of every Rat statement. Empirically (a
two-line law with a `{==}` fill shows it): `T.mk(T.mk2(x), 2n)` reduces to
`T{T.mk2(x), 2n}` -- the body is a constructor, so substituting is enough --
while `Rat.mk(Rat.num(np,nn), d)` does *not* reduce to the same thing as
`Rat.mk.go(sub(np,nn), sub(nn,np), d)`: `Rat.mk` destructures its argument, so
what it sees is the difference pair's *own sides* re-used as raw coordinates,
not the pair `(np,nn)`. Two consequences, both load-bearing:

- The scaling lemma is stated over `Rat.mk.go` and *raw coordinates*
  (`mk.go(mul(np,1+kp), mul(nn,1+kp), mul(1+dp,1+kp)) == mk.go(np, nn, 1+dp)`),
  i.e. exactly what `Rat.mk(Int.mul(n, Int{1+kp,0}), d*(1+kp))` reduces to once
  the `Int.mul`'s two zero products (`mul_zero`, `add_zero`) have come off. The
  wrapper `Rat.mk.scale` is then three `Equal.cong`s and one call.
- The fixed point of `mk` -- "canonical" for this representation -- is stated
  *not* about a Rat but about a numerator pair: `Rat.mk.fixed` proves
  `mk(Rat.num(np,nn), 1+dp) == Rat{Rat.num(np,nn), 1+dp}` from
  `gcd(Rat.mag(np,nn), 1+dp) == 1` and a comparison, with `sub_diag` (the double
  truncation of a one-sided pair is a no-op, at the given comparison and at the
  swapped one) as the bridge. The identity laws (`mul_one`, `add_zero`, ...)
  then take the *fixed-point equation itself* as their hypothesis
  (`for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}`), which makes their fills three
  lines each and keeps the double-sub bookkeeping in one place.

### `%`, as the checker actually enforces it

The rule from the earlier sections, restated as the thing to write code by, now
confirmed against the error messages: **the evidence must be `{new == old}`**
(the old term is the one currently in the goal), the annotation `P` is the
*current* goal with `_` at an occurrence of the evidence's **right** side, the
checker verifies `P`-with-the-right-side against the goal and makes the new goal
`P`-with-the-left-side. A step that "did nothing" or produced a reversed goal is
almost always an evidence orientation (`Equal.sym`'s endpoints are erased, so
whatever you write as the second argument is what ends up on the left); two
branches of `mk.scale.num` were exactly that, and the error message names it
(its `expected` shows the goal, its `observed` shows your annotation with the
*hole filled in*).

### Scaling: split the law into its Nat halves, or drown in motives

Normalization is a Rat of three Nats, so a motive over a whole Rat is ~500
characters per rewrite and there are a dozen rewrites per branch. The way out is
the "splitting a law into its two Nat halves" trick from earlier in this file,
generalized: `mk.scale` is *three* Nat laws (`mk.scale.num`, `.neg`, `.den`),
each with a one-term goal, plus an assembly law of three rewrites. `.neg` is
`.num` at the swapped comparison (one call, after commuting the two arguments of
each gcd's sum with `add_comm`), so only `.num` and `.den` are real work, and
each branch is short: `cmp_mul_right` collapses the scaled comparison,
`mul_sub_right` (GT) or `sub_of_lt` (the other side) collapses the scaled
difference, `gcd_scale` collapses the scaled gcd, and `div_scale` says the
scaled quotient is the unscaled one. The EQ branch needs `div_self` (both sides
are `d/d`) and `div_zero` (a `div(0, d)` with a *variable* divisor is stuck --
that is why `div_zero` is a law and not a reduction).

### Exact division: uniqueness, not correctness

`div_add_mod`/`mod_lt` give quotient-and-remainder; the normalization needs the
other direction, and the whole content is *uniqueness*:

    div_unique: d1*b + r1 == d2*b + r2, r1 < b, r2 < b  =>  d1 == d2

-- a structural induction on `d1` needing no division correctness at all, only
cancellation and ordering. The step's peel (`Nat.mul` of a successor puts the
common factor *inside* the summand) is its own law (`add_assoc_cancel`), and the
vacuous branches are `lt_ne_add` (`a < b` and `a = b + s` is impossible:
`cmp_add_right` moves it to `cmp(s,0)`, which `cmp_lt_zero` refutes -- no sub,
no induction). `div_exact` is then one call, `div_exact_mul` its scaled form,
and `div_one` the gcd = 1 case.

### Witnesses: `Pair.fst`, not destructuring

`div_scale` and `divides_pos_wit` are stated over a `Nat.divides(g, a)` *binder*
rather than over `(q, e)` because the caller's witness comes out of
`gcd_divides`, i.e. it is a field of a computed pair, and a computed pair cannot
be destructured where it is produced (the `Nat.Div` ADT fixed the *other* half
of this problem -- a pair that arrives as a parameter -- and `Pair.fst` fixes
this one: it takes one component out of the Sigma `Nat.divides_both` returns
without any destructure). If a future lemma needs a second component, that is
`Pair.snd` with the same type arguments, and no annotation is needed.

### Cross-file proof helpers: the naming rule, verified

A `*_proofs.bend` file defines nothing under its own namespace, so a helper that
another file must call has to be written with the *laws* module's prefix:
`def Nat.wit_q(...)` in `nat_proofs.bend` is exported as the key `Nat.wit_q`,
which an importer reaches as `Nat.wit_q` (not `nat.wit_q`, not `N.wit_q`).
`def NL.div_self_scale(...)` -- the fill spelling -- is exported as
`nat.div_self_scale`, so it is *not* reachable from another file at all. Two
consequences worth knowing before designing a helper:

- a helper meant for callers must be defined with the laws-module prefix;
- the cheapest alternative is to make it a *law* in the laws file and fill it,
  which is what `div_self_scale` did.

Two corollaries for the value lemma, both hit and confirmed this session:

- **A law binder's type may only mention names an *earlier binder* introduced.**
  `for w: {p == Nat.mul(g, q) : Nat}` is rejected with `a defined name /
  observed : q` -- a quotient invented in the statement is not writable. So the
  value step has to take its quotients as *binders* and their equations as
  further hypotheses, and the caller reads the quotient off a `Nat.Div` at the
  one point where the goal determines its type parameters (the fill's own
  binder, i.e. `NL.Div{q, we} = w` in a `def NL.<law>(...)`).
- **`Nat.div` gets rewritten where it appears in `Nat.divmod.go` form, not as
  `Nat.div`.** A `%` step whose annotation spells `Nat.div(p, g)` reports
  `expected : Nat.div.fin(Nat.divmod(p, g))` and does nothing. `Equal.cong` over
  a variable's argument is the reliable spelling.

Verified by listing the loader's export keys (import the `.bend` file under
`node` with `bend2/main.ts` registered and read `Object.keys(m.default)`).

### The value keystone, and the three checker rules it had to satisfy

`Rat.mk.value` is landed: `num(mk(n,d))*d == n*den(mk(n,d))`, the cross product
`Rat.mk.eqv` consumes and therefore the one bridge every law that composes two
normalized results crosses. The stack under it, bottom to top:

- `Nat.div_cross`: `div(p,g)*d == p*div(d,g)` given `p = g*q` and `d = g*r` --
  the quotients are binders and the divisor is a *variable* with a positivity
  hypothesis, so a caller whose divisor is a computed gcd does not have to
  re-spell its goal as a successor first. Its fill does that rewrite once
  (`pos_witness`) and then both divisions collapse with `div_exact`.
- `Int.mul_scale`: `Int.mul(Int{xp,xn}, Int{d,0}) == Int{xp*d, xn*d}`. A shape
  law, not a ring law -- it is what turns the raw scaling spelling (the one
  `Rat.add`/`Rat.mul` write) into the coordinate pair the value equation is
  provable coordinate-wise in.
- `Rat.mk.value.go`: the value equation in mk.go's coordinate spelling, two
  `div_cross` calls per branch. The two coordinates are not the same proof: the
  gcd's dividend is `mag = P + Q` (the difference pair's own sides, one always
  0), so `g | P` is only in hand once the comparison says which side is zero.
- `Rat.mk.value`: two `Int.mul_scale` bridges around `.go`, with the witnesses
  handed in as `Pair.fst`/`Pair.snd`.

Three checker rules decided every shape above; none is in the language docs.

- **A match must head its body, and its scrutinee must still be *pending*.**
  `body_flatten` resets the pending list at every `let` to that let's own names,
  and `match_flatten` errors -- "match scrutinees in binder order (this variable
  is unbound, consumed, or out of order: reorder the match)" -- once the list
  runs out. So the scrutinee must be a parameter or a field bound by an earlier
  case/destructure *of the same body*, and the match cannot be preceded by
  unrelated `let`s. This is why the case split is the first thing in
  `Rat.mk.value.go`'s fill.
- **A `let`-bound value can never be destructured**: `w = Pair.snd(..)` followed
  by `Div{q, e} = w` is rejected with "a match cannot scrutinize a local binder
  (give it its own def)". A witness that comes out of a *call* therefore has to
  reach its destructure as a **parameter** -- that is the whole reason
  `Rat.mk.value.go` takes `wm`/`wd` as binders (and `div_scale`,
  `divides_pos_wit`, `div_pos_wit` take theirs the same way), and the caller
  hands in `Pair.fst`/`Pair.snd` of the pair `gcd_divides` returns.
- **A family application is not `Data`, so it cannot be a `+` binder.** A
  copyable binder of type `Nat.divides(g, a)` is rejected with `expected : Data /
  observed : Type`: a parameterized family never unfolds to its ADT node (the
  angle-bracket `Nat.Div<g, a>` spelling is the one that does). Witnesses are
  linear binders -- and that is fine, because the *fields* of `Nat.Div` are
  `+fields` (Many), so what a proof reads twice is the quotient and the
  equation, and a witness it needs again is rebuilt from them: `N.Div{dr, dwe}`.
- On `div_cross`, confirmed once more: the `%` hole marks an occurrence of the
  evidence's **right** side, so the evidence has to be written `{new == old}`.
  `Equal.sym(A, a, b, e)` with `e : {a == b}` yields `{b == a}`, and getting the
  two endpoints the wrong way round is reported with the two orientations side
  by side (`expected : {d == ..}` / `observed : {.. == d}`).

### What is left

`Rat.mul_assoc` is in, and it is the template for the rest. Four notes from
doing it, all load-bearing for the siblings:

- **The composing laws must be stated over `Rat{Rat.num(np,nn), 1n+dp}`** --
  the difference pair -- with the comparison as a parameter. The obvious
  alternative (inputs `Rat{n, 1n+dp}` with a fixed-point hypothesis `fx`) does
  not survive contact with `Rat.mk.value`: that law's right side names the
  numerator in `Rat.num` spelling, and `Rat.num(np,nn)` is a *different pair*
  from `Int{np,nn}` (`Int{sub(np,nn), sub(nn,np)}`, one side zero). Relating
  the two needs the sign, which `fx` does not hand over (`fx` only says
  `numof(mk(n,d)) == n`, i.e. `n` is the div/gcd term, not a difference pair).
- **The product of two difference pairs is one again, but that is a theorem.**
  `Rat.num.mul` proves `Int.mul(Rat.num(np1,nn1), Rat.num(np2,nn2)) ==
  Rat.num(U, V)` (U, V the product's own coordinates) by nine branches: which
  side of the product vanishes is exactly the sign of the two factors, so the
  two comparisons come in as parameters and each branch derives the zeros with
  `sub_of_lt` at the flipped comparison and closes with `dp.eq.right` /
  `dp.eq.left`. With it, a value equation's difference-pair numerator can be
  replaced by the raw product and `Int.mul_assoc` applies. Without it the whole
  route is stuck: `R1*zn == xn*R2` is simply *false* for raw pairs (take
  `xn = Int{5,3}`, `yn = Int{1,0}`, `zn = Int{1,0}`: `R1*zn = Int{2,0}` but
  `xn*R2 = Int{5,3}`).
- **The assembly is a cancellation, not a substitution.** The denominators the
  value equations carry are *normalized* (`a = div(d1,g1)`), so
  `A*d1 == R1*a` and `B*d2 == R2*b` do not hand over the composed cross product
  directly: both sides are scaled by the factor the two denominators share
  (`yd`, since `d1 = xd*yd` and `d2 = yd*zd`), the two sides meet at the single
  middle product, and `Int.scale.cancel` (with `Nat.mul_right_cancel` under it)
  takes the factor off again. `Int.scale_cross` is that law; its fill is one
  `%` step per rewrite -- split the scales with `Int.scale.pair` and walk them
  past the factors they must sit next to with `mul_swap`/`mul_assoc`/`mul_comm`
  -- which is affordable only because the statement is letters, not spelled-out
  fractions.
- **A constructor literal cannot head a `let`** ("an annotated term (cannot
  infer)"), and `+x: T = v` does not parse, so a proof that wants to name a
  scaled unit binds a def application instead: `def Int.unit(n) = Int{n, 0n}`
  exists for exactly that. Likewise a comparison a law needs twice must be a
  `+` binder (`for +c: Cmp`), or the fill is rejected with "consumed more than
  once".

Still open, in dependency order: the other composing laws (`add_assoc`,
`add_exchange`, `mul_distrib`, `mul_add_left`, `neg_add`, `neg_neg`). They need
one thing `mul_assoc` did not: an `Int.add` numerator is a *sum* of coordinates,
so the `Rat.num`-of-a-sum facts (and the `Int.canon` projections under them)
have to be stated before the same four-call fill can be written. Then `QExt`
over `Rat`.

### The composing laws: what `neg_neg` actually costs (measured, not guessed)

The attempt to land the siblings went one law deep and stopped, and the reason
is worth writing down before anyone re-pays for it: **`neg_neg` is not the
one-congruence law it looks like, and `mk`'s output is not the difference pair
the composing laws are stated over.** Two concrete findings, both from running
the checker.

**1. A composing law cannot be stated directly over an operation's output.**
The first draft of `Rat.neg_neg` was

    for +c: Cmp, +np, +nn, +dp ... {Rat.neg(Rat.neg(Rat{Rat.num(np,nn), 1n+dp})) == Rat{Rat.num(np,nn), 1n+dp} : Rat}

and `{==}` does *not* close it: the goal's left side is `mk(neg(neg(A)), d)` with
`A = numof(mk(neg(Rat.num(np,nn)), d))` -- a `div`/`gcd` pair, not
`sub(np,nn), sub(nn,np)` -- and `Int.neg_invol` cannot be applied to it because
the inner `Rat.neg` did not produce `Rat{neg(Rat.num), d}`, it produced
`mk(neg(Rat.num), d)`, whose fields are `div(sub(...), G)`. Measured directly:
the `{==}` fill was rejected with the goal `Rat{Int{div(divmod(...)), ...},
div(...)}` against the observed `Rat{Int{sub(np,nn), sub(nn,np)}, 1n+dp}`.

So the siblings need the identity laws' *own* hypothesis -- `mk(n,d) == Rat{n,d}`
for the value in hand -- or a lemma that discharges it. The parent's read is
confirmed: without that bridge the composing laws are unreachable from the
canonical statements the layer's own identity laws use.

**2. The bridge is `Rat.mk_idem`, and it *is* provable.** The useful form is not
`mk(n,d) == Rat{n,d}` (that needs coprimality of `mk`'s output, the deep part
this route avoids) but

    Rat.mk(numof(mk(n,d)), denof(mk(n,d))) == mk(n,d)

-- `mk` is the identity on its own output, stated over `numof`/`denof` because
that is exactly what a caller holds after an operation. Its proof is
`Rat.mk.eqv.raw` at the cross product `mul(numof(M),denof(M)) == mul(n,denof(M))`,
which is `Rat.mk.value`'s own equation once `Int.mul(x, Int{k,0})` is unfolded
with `Int.mul_scale` -- i.e. *no coprimality and no case split*. Two dead ends
found on the way (both cost time, both are avoidable):

- the `Nat` half is not free: `denof(mk(n,1+dp)) = div(1+dp, G)`, so the equation
  `mul(G,q) == 1+dp` that `div_scale`/`mul_right_cancel` want has to be *built*
  (`div_exact` at the gcd witness' quotient, then `pos_witness` on `G` and a
  congruence on `mul(u,q)`), and it is needed on both sides.
- `Rat.mk` **destructures its argument**, so a numerator spelled through another
  function (`Int.sub(Int{np,0n}, Int{0n,nn})`) is *seen differently* from
  `Int{np,nn}`: `mk` sees `add(np,nn), 0`, not `np, nn`. An `Int` value that is
  going to be handed to `mk` must be spelled `Int{np,nn}` exactly, which also
  means it *cannot be a `let`* ("an annotated term (cannot infer)" for a
  constructor literal) -- it has to be written inline at every mention.

**3. Two checker facts that cost the most time here, neither documented before.**

- **A proof-only `def` in a `*_proofs.bend` file must be annotated**: `def F(x)`
  with a bare parameter list works *only* when `F`'s name is a law in the book
  (that is the fill mechanism). For any other helper the parameter list needs
  types, and a dependent binder type forces a return annotation too --
  `def NL.f(g: Nat, a: {p == q : Nat}) -> Nat:` parses; the same without
  `-> Nat` fails with `expected : '->' / observed : ':'` pointing at the *def*
  line, which reads like the body is at fault and is not.
- **Reaching a law's fill from another file is not the same as calling the
  law.** Probing with a file that imports both `nat.bend` (as `N`) and
  `nat_proofs.bend` (as `NP`), *all four* spellings of a proved Nat law --
  `N.mul_assoc`, `NP.mul_assoc`, `Nat.mul_assoc`, `nat.mul_assoc` -- were
  rejected with `expected : a defined name`, even though
  `rat_proofs.bend` calls `N.sub_diag` and friends successfully. Inside its own
  file the fill's own spelling (`NL.mul_assoc`) is what resolves. Do not assume
  a law key is callable by its laws-module name; check with a one-line probe.
  `Pair.fst`/`Pair.snd` for their part only infer when spelled *inline* with
  `Nat.divides(...)` type arguments at the call site -- binding the
  `gcd_divides` pair to a `let` first makes the type argument fail with
  `expected : Data / observed : Type`.

Next step for the next round, in order: land `Rat.mk_idem` (statement in
`rat.bend`, fill in `rat_proofs.bend`, using `Int.mul_scale` + `Rat.mk.eqv.raw`
and the `Nat` equation built with `div_exact`/`pos_witness`), then `neg_neg`
(one `Equal.cong` on `Int.neg_invol` after the `mk_idem` rewrite), then
`neg_add` (a cross product through `Int.neg_mul`), and only then the
associativity/distributivity four -- whose `Int.add` numerator also needs the
sum form of `mk_idem`'s right-hand side, so budget for a `Rat.num`-of-a-sum
family there.

### `Rat.mk_idem` is a *statement* problem, not a fill problem (measured)

A round was spent on the `mk_idem` statement above and it does **not** go
through as handed over: everything in its fill lands (the comparison, the
`mk.value` cross product, `eqv.raw`'s two positivity slots) except the one step
the handover described as bookkeeping -- the *positivity* of `denof(M)`. The
tree was left green with the law and its fill removed; nothing about the route
below is a fill bug, and three separate spellings of it were tried and measured
against the checker.

**1. `mk(Rat.num(np,nn), d)` is `mk(Int{np,nn}, d)` in everything but the cross
product's right-hand side.** `mk` destructures its argument, and when the
argument is `Rat.num(np,nn)` -- i.e. `Int{sub(np,nn), sub(nn,np)}` -- the fields
`mk.go` receives are the pair's *own sides*, so:

    numof(mk(Rat.num(np,nn), d)) = Int{div(sub(np,nn), G), div(sub(nn,np), G)}
    G                            = gcd(add(sub(np,nn), sub(nn,np)), d)

i.e. `G` is `Rat.g(np,nn,d)` **unexpanded**, and `denof(M) = div(d, Rat.g(np,nn,d))`.
This is the measurement that kills the "bridge" framing: `Rat.mk.den.pos(np,nn,dp)`
is stated at *exactly* that gcd, so `mk.den.pos` looked like it should apply
verbatim -- and it does not, because of the fit rule in (2).

**2. A type-level `Rat.mag(A, B)` is not the same term as `Rat.mag(np, nn)`, and
the checker will not fit them.** `mk.den.pos`'s conclusion prints its gcd as
`gcd(add(sub(np,nn),sub(nn,np)), 1n+dp)` -- the *unexpanded* magnitude, because a
`def` applied to concrete arguments is only forced one level in a type -- while
the goal's denominator carries the *expanded* one,
`gcd(add(sub(sub(np,nn),sub(nn,np)), sub(sub(nn,np),sub(np,nn))), 1n+dp)`. The
two are equal (one `sub_diag` per coordinate: the second at the comparison with
the arguments swapped, `cmp_antisym` + `Cmp.flip`), but `div_pos_wit` and
`Equal.cong` both *fit* rather than unify, so the equation cannot be transported
across the `Nat.div` the two spellings sit under. Building the evidence at the
term the goal actually has is not available either: the witness for `g | 1n+dp`
has to come from `gcd_divides` at the *same* magnitude, and its conclusion is
stated at whatever spelling the caller passes -- so the caller is back at (2).

**3. No congruence seems to reach under `Nat.div`** (this is the load-bearing
new fact, and it generalizes far past this law): `%` expands `Nat.div` into
`Nat.divmod(x,y).fin` form *before* rewriting, and in `Equal.cong` the
substitution of the argument lands **after** that expansion, so the two ends of
the congruence differ by the shape of the substituted argument. Measured on a
two-line probe with no Rat in it at all:

    Equal.cong(Nat, Cmp, u => Nat.cmp(0n, Nat.div(1n, ZZ(u, v))), a, a, {==})

is rejected with `expected : ... ZZ(Nat.add(np,nn), ...)` against
`observed : ... ZZ(Nat.sub(np,nn), ...)` -- the ends disagree in the *argument*,
not in the division. So `Rat.gden` was introduced as a named head
(`def Rat.gden(np,nn,d) = Nat.div(d, Rat.g(np,nn,d))`) on the theory that a named
application substituted one level at a time would keep the ends equal; it does
not change the outcome (same mismatch, printed with the substituted argument).
Two more spellings were rejected on the way and are worth not re-trying:
`Cmp.flip(c)` as a value anywhere (let value, local binder, argument, clause
kind, def return type) is `expected : a defined name` -- the *only* producer of a
flipped comparison is a lambda body whose binder is a variable, i.e. a cong whose
lambda **is** `N.Cmp.flip`; and the lambda's type arguments in `Equal.cong` must
be written out (`Nat, Cmp`, not `Cmp, Cmp`) or the binder comes back typed `Cmp`.

**What the next round should try, in order.** (a) State `mk_idem` with the
positivity of `denof(M)` as a *hypothesis* and let the caller supply it (the
caller holding an operation's output has `mk.den.pos` at its own value, so the
hypothesis is exactly what it can write) -- this needs no new Nat lemma and no
transport; (b) if the law must be self-contained, give `mk` a *variant* whose
cross product names the numerator in the *expanded* spelling
(`Int{div(sub(np,nn),G), ...}` rather than `numof(M)`), proved by the same
coordinate argument as `mk.value.go` -- i.e. extend `mk.value` with a second
statement rather than trying to bridge to the first; and (c) only then
`neg_neg`, which is two congs once `mk_idem` exists (the whole reason the
composing laws need it). Note for (b): `mk.value`'s own fill is content to take
`pd` as `{==}` because its `d` is a successor literal; `mk_idem`'s `d` is
`denof(M)`, which is why its positivity is the whole difficulty.

### mk_idem landed, and the "no congruence under Nat.div" rule is too strong

`Rat.mk_idem` **is** in, and **unconditional**:
`mk(numof(M), denof(M)) == M` for `M = mk(Rat.num(np,nn), 1n+dp)`, with the
comparison as the only parameter. `Rat.mk_idem.raw` is the same identity with a
general denominator plus the two positivity hypotheses (`pd`, `pq`) that a
caller with a product denominator needs. `Rat.neg_neg` is in too (below).

The two steps the previous round could not discharge are one call each, and both
were a *spelling* problem rather than a missing lemma:

- **The positivity of `denof(M)` is one `div_pos_wit`** at the gcd spelling the
  *goal* carries -- `Rat.g(P, Q, d)` for `P = sub(np,nn)`, `Q = sub(nn,np)`, the
  raw coordinates `mk` destructured -- with the witness `gcd_divides` returns
  for that same magnitude:

      N.div_pos_wit(G, dp,
        Pair.snd(N.Nat.divides(G, R.Rat.mag(P, Q)), N.Nat.divides(G, 1n+dp),
          N.gcd_divides(R.Rat.mag(P, Q), 1n+dp)))

  Nothing is transported. `Rat.mk.den.pos`'s conclusion is at the *unexpanded*
  `Rat.g(np, nn, 1n+dp)`, i.e. a different spelling of the same gcd -- that, and
  not the law's truth, is what the previous round measured when it found that
  `mk.den.pos` "looked like it should apply verbatim and does not". A caller of
  `mk_idem.raw` whose value is `mk(Int{U,V}, d)` gets the same fact the same way
  (`gcd_divides(Rat.mag(U,V), d)`), which is exactly how `Rat.mul_assoc` already
  derives its two denominators' positivity.
- **The numerator spelling** (`mk.value` names `Rat.num` of the raw coordinates;
  the statement is written over the difference pair) is two `sub_diag`s, one at
  the comparison and one at the flipped one -- reachable by `Equal.cong` because
  they sit under `Nat.mul`/the `Int` constructor, not under `Nat.div`: the same
  two rewrites `mk.fixed`'s fill already makes, with the same flip evidence.

**Correction to the previous round's load-bearing claim.** "No congruence seems
to reach under `Nat.div`" is too strong. `Equal.cong` *with an explicit motive*
transports all four of these, each measured with `All terms check.` (probe file
deleted; the text is the whole probe):

    def divarg(a: Nat, g: Nat) -> {Nat.div(Nat.sub(a, 0n), g) == Nat.div(a, g) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(u, g), Nat.sub(a, 0n), a, N.sub_zero(a))

    def divarg2(+U: Nat, +V: Nat, g: Nat)
      -> {Nat.div(Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), g) == Nat.div(Nat.sub(U, V), g) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(u, g),
        Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), Nat.sub(U, V),
        N.sub_diag(Nat.cmp(U, V), U, V, {==}))

    def divdvs(a: Nat, +U: Nat, +V: Nat, +d: Nat)
      -> {Nat.div(a, N.Nat.gcd(Nat.add(Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), Nat.sub(V, U)), d))
          == Nat.div(a, N.Nat.gcd(Nat.add(Nat.sub(U, V), Nat.sub(V, U)), d)) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(a, N.Nat.gcd(Nat.add(u, Nat.sub(V, U)), d)),
        Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), Nat.sub(U, V),
        N.sub_diag(Nat.cmp(U, V), U, V, {==}))

    def divsucc(+d: Nat, +a: Nat, G: Nat, e: {d == 1n+a : Nat})
      -> {Nat.div(1n+a, G) == Nat.div(d, G) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(u, G), 1n+a, d, Equal.sym(Nat, d, 1n+a, e))

i.e. (a) a rewrite of `Nat.div`'s dividend, (b) `sub_diag`'s shape inside that
dividend, (c) a rewrite inside the gcd that *is* the divisor, (d) the dividend's
successor re-spelling that `div_pos_wit` concludes at. What fails is the `%`
spelling measured before: a `%` step whose annotation does not match the goal
after `Nat.div` has been expanded (the two ends then disagree in the *argument*).
So the usable rule is: reach for `Equal.cong` with a motive, not `%`, when a
`Nat.div` is in the way. Two consequences worth having: deriving `pq` inside
`mk_idem.raw`'s fill (a variable denominator, so the *witness type* has to be
re-spelled from `divides(G, d)` to `divides(G, 1+ap)` -- an evidence-type
rewrite, which is why the raw form keeps the hypothesis), and a proof of the
representative lemma below.

### `Rat.neg_neg` (landed) and what it costs

The unconditional difference-pair statement is **false**, evaluated:

    neg(neg(Rat{Rat.num(4,0), 2})) = Rat{Int{2,0}, 1}   vs   Rat{Rat.num(4,0), 2} = Rat{Int{4,0}, 2}

`==` on `Rat` is structural, so negation of a non-canonical term comes back
mk-headed with div/gcd fields. With coprimality (`Rat.mk.fixed`'s own
hypothesis, which the identity laws' `fx` also carries) the law is two
`mk.fixed` calls around one congruence: `neg` of `Rat{Rat.num(np,nn), 1+dp}` is
`mk` of the swapped pair, whose gcd is the stated one because `Rat.mag` is
symmetric by `add_comm` -- so the intermediate is a fixed point too. No value
equation and no case split: negation never touches the denominator.

### The additive composing laws: the statement is true, the obstruction is the numerator representative

Measured, so that the next round starts from the right place:

- `add_assoc` and `neg_add` (over `Rat{Rat.num(np,nn), 1n+dp}`, no coprimality)
  are **true**: at `x = 2/3, y = -3/5, z = 5/4` both sides of each evaluate to
  the same `Rat` (`Rat{Int{79,0}, 60}` and `Rat{Int{0,1}, 15}`).
- The obstruction is not `mk_idem` and not positivity. An `Int.add` numerator is
  a *sum* of two difference pairs, and `Rat.mk.value`'s right-hand side names it
  as `Rat.num(U, V)` of the sum's raw coordinates -- which for a mixed-sign sum
  is a pair with **both** sides non-zero, i.e. a *different representative* of
  the same integer from the raw pair the `Int` ring laws see. At
  `add(2/3, -3/5)` the sum's raw coordinates are `(10, 9)`, evaluated:

      Rat.num(10, 9) = Int{1, 0}        Int{10, 9} = Int{10, 9}
      canon of both  = Int{1, 0}

  `mk.eqv.raw` consumes a cross product of raw numerators, so it can never
  equate the two: the multiplicative sibling's middle step (`Rat.num.mul`, which
  says a *product* of difference pairs is one-sided again) has no additive
  counterpart, because a sum of difference pairs is not one-sided. The bridge
  the additive family needs is at the level of the value, not of the cross
  product:

      Rat.mk(Rat.num(U, V), d) == Rat.mk(Int{U, V}, d)

  ("mk is blind to which representative of the numerator's value it is handed").
  Its *statement* is true at exactly the ambiguous point above -- evaluated:
  `mk(Rat.num(10,9), 3)` and `mk(Int{10,9}, 3)` both print `Rat{Int{1,0}, 3}` --
  and its proof should be the shapes measured in this section: one `divarg2` per
  coordinate, plus the gcd/divisor transports. **The rest of this paragraph is
  an argument, not a measurement.** With it, each additive law should read as
  the mul_assoc recipe the other way round (rewrite the side whose numerator is
  raw into the `Rat.num` spelling, then consume the two value equations with
  `mk.eqv.raw`), and `pq` for such a side is the four-line `div_pos_wit` call
  above -- also verified at the raw spelling, for a caller whose value is
  `mk(Int{U,V}, 1+ap)` rather than `mk(Rat.num(np,nn), ·)`.

Next, in order: (1) the representative lemma above; (2) `neg_add` from it (the
negated value equation is one `Int.neg_mul` plus `Rat.num` of the swapped pair);
(3) `add_assoc`/`add_exchange` (needs the two summands' `Rat.num.mul`-style
shapes as well); (4) `mul_distrib`/`mul_add_left`; (5) `QExt` over `Rat`.

### The additive block: three units in, and the composite bridge that is still missing

Committed, each with the whole gate set green:

- **`Rat.mk.rep`** -- `mk(Rat.num(U,V), d) == mk(Int{U,V}, d)`, unconditional
  and with no comparison parameter. The two `sub_diag`s that collapse the `mag`
  of a one-sided pair are instances at the *explicit* comparisons
  (`sub_diag(Nat.cmp(U,V), U, V, {==})` and the swapped one), so nothing has to
  be flipped in, and every rewrite is an `Equal.cong` with a motive (never a
  `%`), because all of them reach under a `Nat.div`. No witness, no positivity,
  no `div_pos_wit`: no division is ever *evaluated*, only its arguments are
  rewritten.
- **`Rat.add.value`** -- `add(mk(Rat.num(np1,nn1),1+dp1), mk(Rat.num(np2,nn2),1+dp2))
  == mk(<raw sum>, mul(1+dp1,1+dp2))`, the additive twin of the product shape.
  A sum of two difference pairs is *not* one-sided, so no `Rat.num.mul`-style
  shape law can relate it, and its cross product has to be assembled: two
  `mk.value` calls scaled into the shared denominator and merged by the Int ring
  laws (`R.Rat.add.piece`, then `R.Rat.add.cross` -- proof-only helpers in
  `rat_proofs.bend`), then `mk.eqv.raw`. What makes the raw sum reachable at all
  is that each summand's coordinates `(sub(np,nn), sub(nn,np))` *are*
  truncations, so `Rat.num(ai,bi) == Int{ai,bi}` is two `sub_diag`s -- the same
  collapse `mk.fixed`'s fill makes.
- **`Rat.neg_add`** -- `-(x + y) = -x + -y` for the canonical presentation, no
  coprimality. One `Rat.add.value` at the two negated summands, one `mk.eqv.raw`
  at the value equation `mk.value` gives after `Int.neg_mul` has moved the
  negation inside, one `mk.rep`, and four `Nat.add` commutations under the
  constructor. Negation never touches a denominator, so no scaling appears.

Two rules the fills paid for, both worth not re-discovering:

- **`Equal.sym(A, a, b, e)` is called with `(a, b)` in the evidence's own
  order, and its result is `{b == a}`** -- the argument check does not
  re-orient, so passing the pair the other way round silently produces the
  reversed equation (and the goal then fails with two enormous types). The
  discipline that works: the evidence must have type `{new == old}` read against
  the goal, so pass `(old, new)`.
- **A proof-only helper `def` is not callable cross-file.** A probe importing
  `rat_proofs.bend` and calling `R.Rat.add.piece` is rejected with
  `expected : a defined name` -- the same wall the law keys hit. Fills that call
  helpers must live in the file that defines them, so `neg_add` was probed by
  editing `rat_proofs.bend` directly rather than in a scratch file.

**The four remaining additive laws all hit one bridge that is not in yet: a
*composite* representative problem, one level up from the one `mk.rep`
closes.** The shape of it, at `add_assoc` (this derivation is an argument, not a
measurement -- nothing below was run):

    LHS = add(add(x,y), z)    RHS = add(x, add(y,z))

The inner sum is `M1 = mk(S1, d1)` with `S1` a raw pair whose coordinates
`(P1, Q1)` are *sums* of scaled truncations, and the outer add reads
`numof(M1)`; the left side is therefore `mk(nL, k1*zd)` with
`nL = numof(M1)*zd + r3*k1`. The value equations (`mk.value` on each composite)
name those projections in `Rat.num` spelling, and the cross product `mk.eqv.raw`
would want is

    [Rat.num(P1,Q1)*zd + r3*d1] * xd*d2  ==  [r1*d2 + Rat.num(P2,Q2)*xd] * d1*zd

-- an equation between two *pairs* of equal value and different representative:
`Rat.num(P1,Q1)` is `Int{sub(P1,Q1), sub(Q1,P1)}`, while the right-hand side is
built from the raw `r1 = Int{a1,b1}`. And unlike the summands of
`Rat.add.value`, `P1` and `Q1` are **not** truncations, so `sub_diag` cannot
collapse them; `mk.rep` does bridge exactly this gap, but only where the pair is
the *argument of an mk*, not where it sits inside a sum. (The gap itself is the
one already measured above: `Rat.num(10,9) = Int{1,0}` against
`Int{10,9} = Int{10,9}`.) Note also that `Rat.add.value`, as it stands, needs
*both* summands spelled `mk(Rat.num(np,nn), 1+dp)`; `add_assoc`'s outer add has
one mk summand and one constructor summand, so that law does not apply to it
verbatim.

**What the next round should try, in order.** This is a plan, not a
measurement; the first item is the one that looks cheap now.

1. **`Rat.mk.canon`: `mk(X, d) == mk(canon(X), d)`**, with the comparison as a
   parameter. It looks like *two* steps: `canon(X) == Rat.num(Xp,Xn)` up to the
   comparison (both are `Int{sub(Xp,Xn), sub(Xn,Xp)}`, and `canon`'s one-sided
   form is exactly that pair), so one `Equal.cong` over the constructor puts the
   goal at `mk(Rat.num(Xp,Xn), d)`; and then `Rat.mk.rep` is that statement
   verbatim. With it, "two pairs of equal value have equal mks" follows from the
   already-proved `Int.canon.eqv.fwd` (cross-sums give `canon X == canon Y`),
   which is the bridge the four laws need. `mk.eqv.raw` cannot see it on its
   own: `mul(X, unit d) == mul(Y, unit d)` is simply false for two different
   representatives, so no cross product will ever close these laws.
2. The "mixed" value law for `add` -- one summand an mk, the other a
   constructor, which is the shape the outer add of `add_assoc` really has. It
   should go through by the `add.value` recipe, with the composite's equation
   spelled in `Rat.num(P1,Q1)` (that is what `mk.value` hands over) and the
   constructor's in its raw `Int{ai,bi}`.
3. Only then `add_assoc`/`add_exchange` themselves, and then
   `mul_distrib`/`mul_add_left`, which have the same composite shape with a
   product as the outer operation.

### `Rat.mk.canon.go` landed; the planned name was taken, and the fill is two steps

Item 1 of the plan above is in, under the name **`Rat.mk.canon.go`** --
`Rat.mk.canon` was already the *fixed-point* law (`mk.go(np,nn,1+dp) ==
Rat{Rat.num(np,nn),1+dp}` under coprimality), so the new law's name had to
differ; `.go` is the file's marker for a comparison-threaded coordinate
spelling (`Int.canon.go`, `Rat.mk.go`, `mk.scale.go`, `mk.value.go`), which is
exactly what this is:

    law Rat.mk.canon.go:
      for c: Cmp, +xp, +xn, +d, +e: {c == Nat.cmp(xp,xn)}
      {Rat.mk(I.Int{xp,xn}, d) == Rat.mk(I.Int.canon.go(c,xp,xn), d) : Rat}

The planned fill ("a cong putting canon(X) where `Rat.num(Xp,Xn)` sits, then
`mk.rep` verbatim") is right, with one orientation detail: what the cong needs
is `Rat.num(xp,xn) == canon.go(c,xp,xn)`, i.e. the *branch value* of `canon.go`
spelled as the difference pair, and the two are the same pair because the
branch's own sign forces one truncation to zero (GT: `sub(xn,xp) = 0` by
`sub_of_lt` at the flipped comparison; LT: `sub(xp,xn) = 0`; EQ: both, via
`cmp_eq` + one cong + `sub_self`). `Rat.mk.rep(xp,xn,d)` then closes it read
backwards. No positivity, no divisibility witness, no case split on a gcd:
every rewrite is an `Equal.cong` over the `Int` constructor.

One checker detail paid for by the fill: a **let-bound `Equal.cong` needs an
expected type**. `+ev = Equal.cong(Nat, I.Int, u => ...)` is rejected with
`expected : an annotated term (cannot infer)` (the motive's codomain is the
cong's second type argument and nothing determines it), while the same cong
inline as an argument of `Equal.trans`/another `cong` is fine, because the
endpoints of the surrounding term fix it. So the congs live inline; only the
`Equal.trans` chains (whose endpoints are all spelled) are let-bound.

Measured state after this commit: `rat.bend` alone 188 TODOs (was 187), the
other three unchanged (nat 124, int 32, qext 34), and all five gates green.

### `Rat.add.value.mixed`: the mixed summand, and what it actually costs

Landed: **`Rat.add.value.mixed`** -- `add(mk(Rat.num(np1,nn1), d),
Rat{Rat.num(np2,nn2), 1+dp2})` is `mk` of the unreduced sum, with each summand's
numerator scaled by the *other* summand's denominator. This is the shape
`add_assoc`'s outer add really has (one mk summand, one constructor summand), and
it is the second item of the plan above.

Two things about the statement are load-bearing, and both were decided by what
the fill can reach:

- the mk summand is named by the **presentation's** coordinates `(np1, nn1)`,
  because mk destructures `Rat.num(np1,nn1)` into the truncations
  `(sub(np1,nn1), sub(nn1,np1))` -- and being truncations, their own
  diagonal is a `sub_diag` away from vanishing, which is exactly what makes the
  cross product close. (That is the difference from the *composite* case: the
  coordinates of a sum of two difference pairs are not truncations of anything,
  so no `sub_diag` applies there. The mixed law is not the composite bridge.)
- `d` is a general Nat with two hypotheses (`pd`: `d` positive, `pq`: the
  *output's* denominator positive), the same pair `Rat.mk_idem.raw` takes and for
  the same reason: `div_pos_wit` concludes at the successor spelling of its
  dividend, so the output denominator's positivity cannot be derived for a
  variable `d`, and a caller at a product denominator (`d = xd*yd`) supplies it
  with its own `gcd_divides` + `div_pos_wit`, exactly as `Rat.mul_assoc` does.

The fill is **one helper plus one `mk.eqv.raw`**, and the helper is pure Int ring
permutation around the mk summand's own value equation:

    (A*Y + C*k1) * (d*Y)  ==  (R*Y + C*d) * (k1*Y)

with `A` the projection (`numof`), `R` its difference pair (`Rat.num(P1,Q1)`),
`C` the constructor's numerator, `Y = 1+dp2` and `k1 = denof(M1)`. Push each
outer scale into its sum (`mul_add_left`), turn each pair of scales into one
(`Int.scale.pair`, read backwards), apply the value equation scaled by `Y*Y`, and
the two sides meet. The only "new" facts are two `sub_diag`s putting the raw pair
`Int{P1,Q1}` where `Rat.num(P1,Q1)` sits (the same collapse `Rat.mk.fixed`'s fill
makes, and legal because they sit under the constructor, not under a `Nat.div`).

Measured: it lands with no truncation case split, no coprimality and no scale of
the goal itself; the rat gate is green, `rat.bend` alone reports 189 TODOs.

### `Rat.mk.eqv.val`: "mk is determined by the value", and why a cross sum

Landed: **`Rat.mk.eqv.val`** -- for positive `d1`, `d2`,

    Rat.mk(Int{xp,xn}, d1) == Rat.mk(Int{yp,yn}, d2)
      whenever   xp*d2 + yn*d1 == yp*d1 + xn*d2

This is the general quotient lemma, and it is the item the additive block was
actually blocked on: `Rat.mk.eqv.raw`'s hypothesis is a cross *product* of the
two numerators as pairs, and that equation is simply **false** for two different
representatives of one value. Measured: `6/24` and `-14/24` (the two sides of
`add_assoc` at `2/3, -3/5, 5/4`) have equal value, and their numerators `(6,20)`
and `(0,14)` give `(144,480)` against `(0,336)` -- equal as integers, different
as pairs. So no rearrangement of cross products can close the additive laws; the
hypothesis has to be the value equation read as Nats, which is
`Int.canon.eqv`'s own cross-sum shape and what the value equations of the
composing laws can actually produce. (The forward direction of
`Int.canon.eqv` is the one whose *conclusion* is that cross sum, but the
direction consumed here is `bwd`, from the cross sum to the equality of the
canonical forms; both were needed in the end, which retires the note in
`int.bend` that "nothing downstream needs the reverse direction".)

The fill is five steps per side and they are all spelled in `rat_proofs.bend`:

    mk(Int{xp,xn}, d1)
      -> mk(Int{xp,xn}, da)                    pos_witness (da = 1 + (d1-1))
      -> mk(mul(Int{xp,xn}, db), D)            Rat.mk.scale by db, read backwards
      -> mk(Int{xp*db, xn*db}, D)              Int.mul_scale (the raw spelling)
      -> mk(canon.go(cx, xp*db, xn*db), D)     Rat.mk.canon.go
      -> mk(canon.go(cy, yp*da, yn*da), D)     Int.canon.eqv.bwd, one cong

with `D = da*db`, and the right side the same chain with the denominators
exchanged; the right chain is then read backwards by one `Equal.sym`. Two
checker facts the fill paid for:

- **the `Int.mul_scale` step is not optional.** `Nat.mul` matches on its *first*
  argument, so `Int.mul(Int{xp,xn}, Int{db,0n})` is stuck at
  `Int{add(xp*db, xn*0), add(xp*0, xn*db)}` -- `mul(a, 0)` is not definitional,
  `mul_zero` is a law -- and the term therefore does *not* convert to the raw
  pair the canonical laws are stated over. `Int.mul_scale` is the only bridge,
  exactly as its own comment says.
- **a let-bound `Equal.cong` has no determined type** (the motive's codomain is
  the cong's own second type argument and nothing fixes it: `+e = Equal.cong(...)`
  is rejected with `expected : an annotated term (cannot infer)`), while the same
  cong inline in an argument position of `Equal.trans`/`Equal.sym` is checked
  against the endpoints spelled there. So the fills write their congs inline and
  bind only the `trans` chains. A related trap: a **bare constructor literal**
  cannot be let-bound either (`+R = I.Int{P1, Q1}` is rejected the same way, and
  `+R: I.Int = ...` is a syntax error), so literal pairs are written where they
  are needed, or bound as an application (`Int.mul(Int{..}, Int.unit(..))`).

Measured: rat gate green, `rat.bend` alone reports 190 TODOs. With `mk.eqv.val`
and `Rat.add.value.mixed` in, `add_assoc` has all of its pieces except the cross
sum itself -- the (★) equation below -- which needs one Nat law for the
truncation cross sum (`sub(a,b) + b == sub(b,a) + a`) and the criss-cross
combination of two of them.

### The two Nat laws the additive block needs, and why they are Nat laws

Landed, each with its fill: **`Nat.sub_cross`** and **`Nat.cross_add`**.

    sub_cross:  (a - b) + b == (b - a) + a              [comparison threaded in]
    cross_add:  A + t == A' + t' and B + t == B' + t'  =>  A + B' == A' + B

`sub_cross` is the *only* place the sign information of an arbitrary pair of
naturals is consumed, and it is the bridge between a pair and its own truncation
pair -- the shape the canonical coordinates of a sum of two difference pairs
have. Its fill is three branches, each two existing facts (`cmp_gt_sub_add` /
`cmp_lt_sub_add` for the non-zero side, `sub_of_lt` for the zero one, `cmp_eq` +
`sub_self` in EQ); the comparison is a parameter because the fill cases on it,
and callers pass `Nat.cmp(a, b)` with `{==}` evidence, so **no caller ever
case-splits**.

`cross_add` is the criss-cross combination: two equations with a common padding
determine the difference of their left-hand constants. In integers both
hypotheses read "A - A' = t' - t" and "B - B' = t' - t", so A - B = A' - B'; Nat
has no negative values, so the statement is over the two padded equations and the
fill pads both sides by `t + t'` and cancels with `add_cancel`. Its fill is the
one place with real shuffling (three `add_assoc`/`add_comm` steps per side to
reach `(A + t) + (B' + t')`), which is why it is a law and not an inline chain.

Neither is a Rat law, and they are here because the alternative -- deriving the
sign facts inside each Rat fill -- is exactly the case analysis the whole
`Rat.mk` design avoids: `Rat.mk` is match-free so that all sign analysis can be
threaded in as a parameter, and these two laws are what that buys for the
additive block. Both are unconditional, both take their comparisons (or nothing)
as parameters, and both are green: nat gate green, `nat.bend` alone 126 TODOs
(was 124), `rat.bend` alone 192, the other two counts unchanged.

### `Rat.mk.trunc`: the bridge for a *composite* numerator

Landed: **`Rat.mk.trunc`** -- `mk(Int{U,V}, d) == mk(Rat.num(sub(U,V), sub(V,U)), d)`.

This is the piece the plan's item 1 was after, and it turns out **not** to need
the comparison parameter at all. `Rat.mk.canon.go` threads one in because it is
stated in `canon.go`'s own spelling; but the pair
`(sub(U,V), sub(V,U))` *is* canon.go's branch value (one side is zero), and
`sub_diag` reaches the collapse at the two explicit comparisons `Nat.cmp(U,V)`
and `Nat.cmp(V,U)` -- so the same content is available with no case analysis
whatsoever, which is what a fill can actually use. (`mk.canon.go` is still the
right tool inside `Rat.mk.eqv.val`, where the canonical forms have to be compared
through `Int.canon.eqv`; the two laws are the same fact in the two spellings the
two consumers need.)

Why a *new* law rather than `mk.rep`: `mk.rep` collapses the mag of a one-sided
pair, and a **sum of two difference pairs is not one-sided** -- its coordinates
are not truncations of anything, so `sub_diag` has nothing to bite on. Its
*canonical* coordinates, on the other hand, are exactly `(sub(U,V), sub(V,U))`,
and that is what this law names. With it, a value whose numerator is an
operation's output -- `Int.add` of two scaled difference pairs, which is what
`add(add(x,y), z)` hands the outer `add` -- is one step from the presentation
`Rat.add.value.mixed` and the composing laws are stated over.

The fill is `mk.rep`'s fill with the two representations exchanged: four
`sub_diag` instances collapse `sub(sub(P,Q),sub(Q,P))` to `P` and
`sub(sub(Q,P),sub(P,Q))` to `Q` (two per coordinate, chained), one cong pair
carries that into the gcd's sum, and the three divisions and the numerator pair
follow by congs. Every rewrite is an `Equal.cong` with a motive, because each one
reaches under a `Nat.div`; measured: rat gate green, `rat.bend` alone 193 TODOs.

**What `add_assoc` still needs.** With `mk.trunc` in, the left-hand side of
`add_assoc` can be put in the mixed law's shape, and the mixed law's conclusion is
spelled in the coordinates `(P1, Q1)` of the inner sum -- the truncation pair --
so the cross sum `Rat.mk.eqv.val` wants is a *pure Nat* equation in
`P1,Q1,P2,Q2,xp,xn,yp,yn,zp,zn,Xd,Yd,Zd` (no `div` anywhere: the mixed law's fill
already consumed the value equations). It reduces to

    P1*Zd + zp*Xd*Yd + Q2*Xd + xn*Yd*Zd == P2*Xd + xp*Yd*Zd + Q1*Zd + zn*Xd*Yd   (★)

times the common factor `Xd*Yd*Zd`. (★) follows from exactly two instances of
`sub_cross` -- `P1 + (xn*Yd + yn*Xd) == Q1 + (xp*Yd + yp*Xd)` and the same for
`P2, Q2` -- scaled by `Zd` and `Xd` respectively and combined with `cross_add`:
the padded equations are `A + t == A' + t'` and `B + t == B' + t'` with
`A = P1*Zd + xn*Yd*Zd`, `t = yn*Xd*Zd`, `A' = Q1*Zd + xp*Yd*Zd`, `t' = yp*Xd*Zd`,
and `B = P2*Xd + zn*Yd*Xd`, `B' = Q2*Xd + zp*Yd*Xd` with the *same* `t, t'` -- so
`cross_add` gives `A + B' == A' + B`, which is (★). Scaling the two cross sums by
`Zd*Xd*Yd*Zd` instead (i.e. by `(Zd*F)` and `(Xd*F)` with `F = Xd*Yd*Zd`) makes
`cross_add`'s conclusion *be* the cross sum `Rat.mk.eqv.val` consumes, with the
common factor already distributed -- that is the one remaining Nat law, and the
fill of `add_assoc` is then: `mk.trunc` + `mk.rep` to re-spell the inner sum, one
`Rat.add.value.mixed` per side, two `sub_diag` congs to collapse the mixed law's
`sub(P1,Q1)` spellings, the Nat law above, and `Rat.mk.eqv.val`. Nothing else was
measured here: the paragraph is a derivation, not a run.

### `Rat.add_assoc` landed, and the sketch's last step needed one more shuffle

Landed: **`Rat.add_assoc`** -- `(x + y) + z = x + (y + z)` for the canonical
presentation `Rat{Rat.num(np,nn), 1n+dp}`, with no coprimality hypothesis and
**no comparison parameter** (nothing is cased on: every `sub_diag` and
`sub_cross` instance is called at an explicit `Nat.cmp` with `{==}`), exactly
the shape `Rat.mul_assoc` has. The decomposition of the last section was right
in outline -- `Rat.mk.trunc` + `Rat.add.value.mixed` per side, the two
`sub_diag` congs on the mixed law's `Nat.sub(P1,Q1)` spellings, the cross sum
from two `Nat.sub_cross` instances through `Nat.cross_add`, closing at
`Rat.mk.eqv.val` -- and it needed no new Nat law. Five things about it were
only visible once the fill was written, and four of them cost an iteration
each:

- **`Nat.cross_add`'s conclusion is not grouped the way `mk.eqv.val`'s pairs
  are.** The scaled instances give `(x1 + x3) + (x2 + x4)`: the two summands
  of one inner sum in each group. The cross sum wants `(x1 + x4) + (x2 + x3)`,
  because `TLp` pairs the *first* summand with the *third* (`P1*Zd + a3*d1`)
  and `TRn` the second with the first. So the "re-association" the sketch ends
  with is really a four-term exchange (`x1 + (x3 + (x2 + x4))` -> ... ->
  `(x1 + x4) + (x2 + x3)`, five `add_assoc`/`add_exchange`/`add_comm` steps,
  the helper `R.Rat.nat.exch4`), and on the mirrored side the same exchange
  plus one `add_comm`. This is not avoidable by choosing the padding
  differently: the only summand both instances carry is the middle one, so the
  padding is forced, and with it the grouping.
- **The two scale factors have to be chosen together.** `cross_add`'s padding
  `t` and `t'` are single terms, so the two scaled instances must share them
  *as spelled*. Scaling the first instance by `Zd*D` and the second by `Xd*D`
  (with `D = Xd*(Yd*Zd)` the common denominator `mk.eqv.val` is finally called
  at) makes the two paddings `(b2*Xd)*(Zd*D)` and `(b2*Zd)*(Xd*D)` -- equal
  after re-associating and commuting `Xd` with `Zd` (`R.Rat.nat.pad`, four
  steps). A uniform scale does not work at all: the paddings would be `b2*Xd*S`
  and `b2*Zd*S`, two different terms with no equation to respell one into the
  other.
- **The inner sums must be re-spelled before anything else touches them.** The
  raw pair an operation writes is `Int.add(Int.mul(num, unit), Int.mul(num,
  unit))`, whose coordinates contain `mul(x, 0n)` terms that are *stuck*
  (`Nat.mul` matches on its first argument), so `sub_cross`'s instance would
  have to be stated at a spelling that first needs four zero collapses; and
  `P1 = sub(Up,Un)` computed at that spelling is not the `P1` the plan's
  equation is written in. Two `Int.mul_scale` congs under one cong on mk's
  argument (one per summand) put the inner sums in the clean coordinates
  `(U,V)`, after which `sub_cross` applies verbatim. That is inference from the
  stuck shapes, not a measurement -- the clean-first route was taken from the
  start.
- **`%`'s `_` marks exactly the occurrence of the evidence's RHS.** An
  annotation whose `_` sits *inside* a wrapper (`{Nat.add(x1, _) == ...}` when
  the whole side is the RHS) does not fail loudly: the checker reports
  `expected : <the real goal type> / observed : <what the annotation demanded>`
  (i.e. `expected` is the goal, `observed` is the demand), which reads backwards
  until one notices. Two steps were spent on this, both time in
  `exch4`/`split`.
- **`Nat.mul_add_left` and `Nat.mul_distrib` are stated flipped** (`sum ==
  product`), so folding a sum into a product is the direct `%mul_add_left`
  while unfolding needs `Equal.sym` -- and `Equal.sym(A,a,b,e)` wants `(a,b)`
  in the *evidence's* order. `Nat.mul_assoc` and `Nat.add_assoc` are the other
  way round (`(a*b)*c == a*(b*c)`), so their `sym`s are the re-associations.

One measurement worth recording for the next unit: **a third file cannot
import `rat_proofs.bend`.** A two-line file that imports `rat.bend as R` and
`rat_proofs.bend` and calls `R.Rat.mk` fails with

    - expected : a defined name
    - observed : R.Rat.add.piece

-- the proof-only helpers that live under `R`'s namespace (`R.Rat.add.piece`,
`R.Rat.add.mixed.cross`) are what trips it, since the same two-line test for
`nat.bend`/`nat_proofs.bend` and `int.bend`/`int_proofs.bend` checks fine. So
the Rat chain had to be developed *inside* `rat_proofs.bend` (which is where
its helpers have to live anyway); `PROVING.md`'s "a third file imports both" is
true for nat and int and false here.

Cost: `rat_proofs.bend` 1981 -> 2465 lines -- nine proof-only helpers
(`R.Rat.nat.d3/xy/pad/exch4/split/flip2/foldA/foldB/cross4`; 155 lines) plus
the 232-line fill and the comments; `rat.bend` 879 -> 915 (the law and its
comment). All five gates green, `rat.bend` alone reports **194** TODOs (was
193). Nothing in `nat.bend` changed: the Nat half of this proof is a *proof*,
not a law.

Next, on the same recipe: `Rat.add_exchange`, then `Rat.mul_distrib` and
`Rat.mul_add_left`. Each is a mixed sum plus a cross sum; the shuffle
inventory (`exch4`, `foldA`, `foldB`, `split`, `pad`) is reusable as it stands,
and `flip2` is the only piece that is specific to which two inner sums meet.

### `Rat.mul_distrib`: the route, and the two measurements that pin it

Not landed -- this is the spelled-out plan for the next unit, plus two
measurements that were *run*, and it is written down because the route is not
the additive block's and the obstruction that decides its shape is easy to
walk into.

The law is true as stated. Measured with the checker's own normalizer, at
`X = 1/2, Y = -1/3, Z = 1/5` (all three canonical presentations):

    Rat.mul(X, Rat.add(Y, Z))                    = rat.Rat{int.Int{0n, 1n}, 15n}
    Rat.add(Rat.mul(X, Y), Rat.mul(X, Z))        = rat.Rat{int.Int{0n, 1n}, 15n}

both sides reduce to the same constructor, so `==` on Rat does decide this
instance (the two sides are equal because `mk` is determined by the value, not
by computation).

**The obstruction: `Rat.mk.eqv.raw` cannot close it as written.** Same
instance, printing the mk arguments and denominators *exactly as the two
operations write them* (`B, b` the projection and reduced denominator of
`M2 = add(Y,Z)`, `B1, b1` of `mul(X,Y)`, `B3, b3` of `mul(X,Z)`):

    LHS  = mk(Int.mul(xn, B), mul(Xd, b))                 arg Int{0n, 2n}  den 30n
    RHS  = mk(add(mul(B1, b3), mul(B3, b1)), mul(b1, b3)) arg Int{6n, 10n} den 60n

    mk.eqv.raw's hypothesis, as the operations write it:
      Int.mul(Int{0n,2n}, Int{60n,0n}) = Int{0n,120n}
      Int.mul(Int{6n,10n}, Int{30n,0n}) = Int{180n,300n}      -- NOT equal

so the raw cross product fails here for the same reason it failed in the
additive block: the two numerators are different *representatives* of one
value (the LHS's is a product with a projection, the RHS's is a sum of
products of projections). Measured, and it is the one thing that has to be
decided before writing any of the fill.

**The route it leaves.** Re-spell the RHS's numerator with `Rat.mk.trunc`
before comparing -- the RHS's raw numerator is a *sum of two difference pairs*
(mk.trunc's own case), whose truncation pair is `(sub(nRp,nRn), sub(nRn,nRp))`
-- and the same instance's cross product then *does* agree:

    Int.mul(Int{0n,2n}, Int{60n,0n})       = Int{0n,120n}
    Int.mul(Int{0n,4n}, Int{30n,0n})       = Int{0n,120n}      -- equal

(the truncation pair of `Int{6n,10n}` is `Int{sub(6,10), sub(10,6)} =
Int{0n,4n}`). Measured. So the closing step is `mk.eqv.raw` after one
`mk.trunc` (plus `mk.rep`/`Int.mul_scale` for the spellings), not `mk.eqv.val`:
the cross sum `mk.eqv.val` would want is in terms of the *projections*, which
are opaque `div` terms, and every way of eliminating them from a Nat equation
runs into a factor that cannot be cancelled.

**A warning about the two measurements above.** Both were reproduced (the
cross products `Int{0,120}` against `Int{180,300}` before `mk.trunc` and
`Int{0,120}` against `Int{0,120}` after), but `mk.trunc` on the RHS numerator
alone is *not* enough in general: checked at nine further instances of the
canonical presentation (including `X=1/2, Y=-1/3, Z=1/5` itself, and one with
two-sided coordinates) the cross product with the RHS truncated and the LHS as
`Int.mul(xn, numof(M2))` is equal at exactly one of them
(`X=1/4, Y=-5/3, Z=5/5`). So the closing step is *not* "`mk.eqv.raw` after one
`mk.trunc`" as the text below says; either both numerators have to be
canonicalized first, or the comparison has to be made between the coordinate
*pairs* rather than the raw numerators. Whoever takes this next should measure
the closing step before writing the fill -- the two sides of the identity the
fill actually proves are unambiguous (the coordinate equations give

    A*C + D2*E2 == G1*C + q2*dd        (A, G1, q2, D2E2 as below)

at every one of the ten instances checked), but which `Rat.mk` lemma consumes
it is not settled by the two measurements recorded here.

#### The remeasurement: `mk.eqv.raw` is refuted, and the consumer is the *value* lemma

Both spellings of `mk.eqv.raw` were re-measured at ten canonical instances and
**both fail, including at the section's own instance** -- this closes the
question the warning above left open:

- the raw cross product (`Int.mul(xn, numof(M2))` against the RHS's unreduced
  sum), and
- the truncated one (`mk.trunc`'s pair on the RHS), and
- the truncated-on-the-left spelling that had not been tried.

At `X=1/2, Y=-1/3, Z=1/5`, in the four Nats `(numerator pos, numerator neg,
denominator)`:

    LHS = mk(Int{6,10}, 12)     cross product  Int{360, 720}
    RHS = mk(Int{6,10}, 60)     cross product  Int{360, 720}

so *this* spelling agrees at the section's instance -- while the spelling the
recorded recipe names (`mk.trunc` of the RHS numerator, `Int{0,4}`) does **not**:
it gives `Int{360,720}` against `Int{240,480}`, and it is the truncation that
breaks it, because the RHS numerator's coordinates `(6,10)` are already the
truncation-free reading the value equations produce.

**Which lemma consumes the coordinate identity, by structure rather than by a
numerical probe.** `Int.mul(xn, B)` and `Int.add(Int.mul(..), Int.mul(..))` are
*already* constructor pairs -- `Int.mul`'s and `Int.add`'s bodies are
`Int{..}`-headed, so both arguments of the two closing `mk`s are `Int{a, b}`
terms and **no `Int.mul_scale` arises at the closing step at all**. That is the
structural fact the earlier rounds missed: the three-spelling trap belongs to
`Rat.num`'s difference pairs (and to `Rat.mk.scale`), not to mul-distrib, whose
numerators are ordinary products and sums of pairs. And for two `mk`s whose
arguments are constructor pairs, the closing lemma that speaks in value terms is
`Rat.mk.eqv.val` -- `mk.eqv.raw` asks for a *product* equation between the pairs
and is false whenever the two representatives differ, which is exactly what the
measurement above shows.

So the corrected recipe is: **`Rat.mk.eqv.val` at the two raw constructor
pairs**, with the hypothesis being the Nat cross sum of those pair coordinates,
and the hypothesis is the coordinate identity scaled -- which is why the
`R.Rat.value.scaled.pos` / `.neg` pair (landed, above) is the right bridge:
each call hands over exactly one coordinate equation of one value equation, at
the scale the cross sum needs. What is *not* settled, and is the next
measurement, is the exact pair of Nat equations the fill has to combine: the
cross sum is stated over `numof(M2)`'s coordinates, and `numof(M2)` is a
`div`/`gcd` term, not a difference pair, so the step that replaces it by the
inner sum's own value pair `(P2, Q2)` is a re-spelling *inside* the cross sum
and was not measured. Three numerical probes of candidate spellings disagreed
with each other under a hand-written model of `Rat.mk`, which is a sign the
model -- not the spelling -- was wrong; the honest state is that the consumer is
settled and the last re-spelling is not.

One harness note that cost time and generalizes: **a probe cannot import a
laws-only file at all.** `import ./src/rat.bend` plus a one-line `main` is
rejected with `Error: 195 TODOs found.` before anything runs, and the same file
importing `nat.bend` reports `126` -- the CLI counts every law body the parser
saw as a `?TODO` in the *whole closure* (`main.ts`'s `book_read` sums
`book.hols + book.open`, and `book.hols` is bumped in the parser, before the
loader's `done` bookkeeping that keeps a filled file out of `book.open`). So a
measurement that needs the *definitions* of a laws-only file has to import a
law-stripped copy of it (`sed` out the `law` blocks; the `def`s are
self-contained).

**The cross product itself** is then assembled the way `Rat.mul_assoc` and
`Rat.add.value` assemble theirs: scale both sides of the equation by
`d2 = Yd*Zd` (the inner sum's own denominator) and use the three value
equations `Rat.mk.value` gives -- `B*d2 == R2*b`, `B1*(Xd*Yd) == R1*b1`,
`B3*(Xd*Zd) == R3*b3`, with `R2 = Rat.num(U2,V2)` the inner sum's difference
pair and `R1, R3` the two products' -- each read at its coordinate level
(`Int.eq.pos`/`Int.eq.neg`). After the substitution both sides are

    b*b1*b3 * [ (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd ]        (left)
    b*b1*b3 * [ P1*Zd + P3*Yd + a1*Q2 + b1*P2 ]          (right)

with `Pi = sub(Ui,Vi)`, `Qi = sub(Vi,Ui)` the truncation pairs of the three
involved pairs, so what is left is the pure Nat identity

    (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd  ==  P1*Zd + P3*Yd + a1*Q2 + b1*P2    (T)

-- the common factor `b*b1*b3` is *not* cancelled: it sits on both sides, and
the identity is multiplied by it. (T) is the distributivity fact at the Nat
level: its two sides differ by `(a1-b1)*(U2-V2) - Zd*(U1'-V1') -
Yd*(U3'-V3')`, which is zero because `U2-V2 = (a2-b2)*Zd + (a3-b3)*Yd`,
`U1'-V1' = (a1-b1)(a2-b2)` and `U3'-V3' = (a1-b1)(a3-b3)`.

**Correction.** The first version of this paragraph claimed (T) is a
`Nat.cross_add` combination of two padded equations it wrote out as

    (a1*P2 + b1*Q2) + (b1*U2 + a1*V2)  ==  (a1*Q2 + b1*P2) + (b1*V2 + a1*U2)
    (P1*Zd + P3*Yd) + (b1*U2 + a1*V2)  ==  (Q1*Zd + Q3*Yd) + (b1*V2 + a1*U2)

-- and that is wrong twice over. `cross_add` consumes *one* padding pair
`(t, t2)`, so two hypotheses only combine if their paddings agree: here the
first carries `b1*U2 + a1*V2` and the second `b1*V2 + a1*U2`, two different
terms (they are the cross sum of the truncation pair in the two orders, and
they agree only when `a1*U2 + b1*V2` does). And the paddings are not the
`b1*U2 + a1*V2` shapes at all: what the value equations actually produce are
the *truncation pairs* `(P2, Q2)`, so every term of the padding and of the
coefficient is a product with `P2` or `Q2`, never with `U2` or `V2`. Written
in the truncation spelling, with `C = Yd*Zd`, `dd = (Xd*Yd)*(Xd*Zd)`,
`bd = b1*b3` and

    A  = a1*P2 + a2*Q2        G1 = a1*P2 + a2*Q2 + b2*P2
    q2 = b1*Q2 + b2*P2        G2 = b2*P2 + b1*Q2 + a2*Q2

(the two summand-groups `cross_add` needs), the padded hypotheses that *do*
combine are

    A*C + q2*X*C           ==  G1*C + G2*X*C          (padding q2*X*C, q2X = q2*X)
    q2*dd + q2*X*C*bd      ==  (q2*X*C)*bd + D2*E2

with `D2*E2 = b1*Q2 + b2*P2`: the first is the positive coordinate reading of
the inner sum's value equation scaled by `X*C`, the second the negative one of
the two products' readings, and `cross_add` at

    (A, A2, B, B2, t, t2) := (A*C, G1*C, q2*dd, D2*E2, q2*X*C*bd, G2*X*C*bd)

gives `A*C + D2*E2 == G1*C + q2*dd`, which is mk.eqv.raw's hypothesis once the
two sides are respelled by `Int.mul_scale` (and the `b*bd` factor is carried
along both sides -- it is never cancelled). Neither hypothesis is a `sub_cross`
instance: `sub_cross` is the *one-coordinate* cross sum of a single inner sum
(what the additive block uses, since there the inner sums are never scaled),
while here the inner sum's value equation is scaled by the two product
denominators and read at both coordinates.

Two statements in this neighbourhood are false as they stand and are recorded
here so that nobody re-derives them:

  - the four-scale `cross_sum` -- `e1 : s3*f3 + s1*f1 == (f1+f3)+f4`,
    `e2 : s4*f4 + s2*f2 == (f2+f4)+f3`, conclusion `T1+T2 == T3+T4`. It is
    false for free scales, and the `s1 = s3`, `s2 = s4` the intended use has
    do not rescue the *statement*: it is the hypothesis set that is too weak,
    not the instantiation that is wrong.
  - `swap` in the shared-*value* form: `u+v == w`, `x+y == w` gives
    `u+y == x+v`. Witness `u=0, v=1, x=1, y=0, w=1`: both hypotheses hold
    (`0+1 == 1`, `1+0 == 1`) and the conclusion asks `0+0 == 1+1`, i.e.
    `0 == 2`. The two hypotheses share a *value*, not a term, and nothing
    forces the pairs to be the same pair.

Nothing in the route needs a new law; what it needs is the shuffle inventory
already in `rat_proofs.bend` (`exch4`, `foldA`/`foldB`, `split`) plus a
Nat-level ring block for the projection-to-truncation identities. Estimated at
the size of `Rat.add_assoc`'s Nat half, i.e. a few hundred lines -- it was not
attempted in this round.

`Rat.mul_add_left` is then free: `(x + y)*z = z*(x + y) = z*x + z*y =
x*z + y*z` is `Rat.mul_comm`, `Rat.mul_distrib`, and two `Rat.mul_comm`s under
a congruence, the same shape `Rat.add_exchange` has on the additive side.

### `Rat.mul_distrib` landed: three comparisons, and (T) needs no case split

Landed, and the last two Rat laws the field needs:

- **`Rat.mul_distrib`** -- `x*(y+z) = x*y + x*z` over the canonical
  presentation, no coprimality hypothesis and no comparison parameter (nothing
  is cased on anywhere in the fill).
- **`Rat.mul_add_left`** -- `(x+y)*z = x*z + y*z`, and the previous round's
  prediction held exactly: `mul_comm`, `mul_distrib`, one congruence per
  summand, three steps and no arithmetic. It was written after `mul_distrib`
  landed and checked on its first run, so the "free" claim is now a measurement
  rather than an expectation.

Cost: `rat_proofs.bend` 2665 -> 3469 lines -- fourteen proof-only helpers
(`R.Rat.nat.swap`, `add2`, `scale.eq`, `scale.eq.r`, `gather`, `distrib`,
`pair.scale`, `cross1`, `dist4`, `align.zd`, `align.yd`, `tl.scaled`,
`tr.scaled`, `cross2`; 554 lines with their comments) plus the 208-line
`mul_distrib` fill and the 42-line `mul_add_left` fill; `rat.bend`
945 -> 1023 (the two laws and their comments). All five gates green,
`rat.bend` alone reports **197** TODOs (was 195, one per new law).

#### The design fix: three `mk.eqv.val` comparisons, not one

The previous round settled the *consumer* (`mk.eqv.val`, not `mk.eqv.raw`)
but left one step unmeasured -- "spilling `numof(M2)`, a `div`/`gcd` term,
into the inner sum's own value pair inside the cross sum" -- and that step is
where the route looks hard. It is hard, and it does not have to be taken:
comparing the two sides **directly** puts every quotient of both operations
into *one* cross sum, which then needs the whole equation multiplied by
`K = d1*d2*d3`, the six value equations substituted inside it, and `K`
cancelled at the end (`Nat.mul_right_cancel`) -- the substitution is real
work and it is bookkeeping for a single comparison.

Comparing in three hops removes all of it, because each hop is at its own
denominators:

    mk(num(x)*numof(M2), xd*denof(M2))
      == U_L = mk(num(x)*Rat.num(U2,V2), Xd*d2)        [the inner sum's value]
      == U_R = mk(P1*d3 + P3*d1, Q1*d3 + Q3*d1 over d1*d3)
      == Rat.add(M1, M3)                               [Rat.add.value, exactly]

- the first hop needs only the **two coordinates of `Rat.mk.value` at the
  inner sum**, scaled by `Xd` -- i.e. exactly the `Rat.value.scaled.pos`/`.neg`
  pair the previous round landed, used for the first time here;
- the second hop is `(T)` multiplied by `d1*d3` and nothing else -- no value
  equation, no `div`, no `gcd`;
- the third hop is `Rat.add.value`: `U_R` *is* that law's own conclusion, so
  this step is two `Rat.mk.rep` rewrites (backwards), two `pos_witness`
  rewrites to the successor denominators `Rat.add.value` is stated over, the
  law, and `Int.mul_scale` on the sum's two products. No cross sum at all.

That is the general lesson for the remaining Rat work: an identity that can be
decomposed through the *value* of an intermediate result should be, because
each hop is then a comparison the existing laws already state, and the one
hard Nat identity stays small.

#### (T) from the padded hypotheses -- the letters the previous round got wrong

`R.Rat.nat.distrib` proves

    (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd  ==  P1*Zd + P3*Yd + a1*Q2 + b1*P2

with **no case analysis**. The route one reaches for first -- split on the sign
of `x`'s numerator, where the identity collapses to the inner sum's cross sum
scaled by `a1` (in the `b1 = 0` branch) or by `b1` (in the `a1 = 0` branch) --
is not needed: the identity is uniform in the two coordinate pairs, and what
proves it is the padded-hypotheses idea this file's earlier paragraph described
with the wrong letters:

    e1 : a1*P2 + b1*Q2   + (a1*V2 + b1*U2) == a1*Q2 + b1*P2   + (a1*U2 + b1*V2)
    e2 : (P1*Zd + P3*Yd) + (V1*Zd + V3*Yd) == (Q1*Zd + Q3*Yd) + (U1*Zd + U3*Yd)

Both carry the padding `(V1*Zd + V3*Yd, U1*Zd + U3*Yd)`, and `Nat.cross_add`
at `(A, A2, B, B2, t, t2) := (a1*P2 + b1*Q2, a1*Q2 + b1*P2, P1*Zd + P3*Yd,
Q1*Zd + Q3*Yd, V1*Zd + V3*Yd, U1*Zd + U3*Yd)` gives the goal after one
re-association. Where the two facts come from:

- `e1` is the inner sum's cross sum `P2 + V2 = Q2 + U2` scaled by `a1` and by
  `b1` and added (`R.Rat.nat.scale.eq` twice, then `R.Rat.nat.add2`, whose
  `swap` shuffle is the five-step association `(A+B)+(t+s) -> (A+t)+(B+s)`);
  no truncation reasoning, so both scales are the *raw* coordinates.
- `e2` is the same two-step construction on the two product pairs, scaled by
  the other summand's denominator `Zd` and `Yd`.
- The padding equality is where the two `R.Rat.nat.gather` facts enter: they
  are the pure ring facts

      a1*U2 + b1*V2 = U1*Zd + U3*Yd        a1*V2 + b1*U2 = V1*Zd + V3*Yd

  i.e. distributing each multiplier over the inner pair's coordinates and
  folding the products back into the product pairs' coordinates -- which is
  also the sentence the whole identity *means*: `(a1-b1)(P2-Q2) =
  Zd(P1-Q1) + Yd(P3-Q3)`.

The previous round's restatement of `e1`/`e2` was wrong in the way this file
recorded (its paddings were `b1*U2 + a1*V2` shapes, which are also swapped
between the two hypotheses and so cannot both match `cross_add`'s single
padding pair); the two written above do combine, and the fact that makes them
combine is that the inner sum is scaled by `a1` on one side of `e1` and by
`b1` on the other, so the *shared* piece is the pair `(V1*Zd + V3*Yd,
U1*Zd + U3*Yd)` and not a middle summand.

The two hops that do not feed `(T)` are ring bookkeeping with no arithmetic
content, and they are the bulk of the helper block:

- `R.Rat.nat.cross1` + `pair.scale`: the first hop's cross sum, four products
  re-associated from the shape `(c1*x1 + c2*x2)*(d2*Xd)` to
  `(c1*y1 + c2*y2)*(Xd*m2)` -- one commutation each because the left side's
  own denominator is `Xd*m2` (written by `Rat.mul`) while the scaled value
  equations come out of `Rat.value.scaled` in the `m2*Xd` order;
- `R.Rat.nat.cross2` + `tl.scaled`/`tr.scaled`/`dist4`/`align.zd`/`align.yd`:
  the second hop, `(T)` multiplied by `d1*d3` and re-associated into
  `ULp*(d1*d3) + URn*(d2*Xd) = URp*(d2*Xd) + ULn*(d1*d3)`. Every alignment is
  a commutation of the multiset `{Xd, Yd, Zd}` with its multiplicities -- four
  or five steps each, and pure `mul_comm`/`mul_assoc` after that.

Nothing in the block needs a new Nat law: three `Nat.sub_cross` instances, one
`Nat.cross_add`, and `mul_comm`/`mul_assoc`/`mul_add_left`/`mul_distrib`.

#### Four checker rules this round paid for

- **`%`'s semantics, exactly.** `%E : {P}` takes the *current* goal `T`, solves
  `P`'s hole against `T`, and rewrites the occurrence the hole marks -- which
  must therefore be an occurrence of `E`'s **right** side -- into `E`'s left
  side; the rest of the chain then proves the rewritten goal. So the annotation
  is the goal *before* the step, not after, and it must place the hole at the
  exact subterm being rewritten: **there is no automatic congruence.** An
  annotation whose hole sits at a larger term (`{Nat.mul(x, Nat.mul(Yd, _))}`
  when only `mul(Xd,Zd)` inside it is being rewritten) demands an evidence
  about that larger term and fails. The rule is now measured rather than
  guessed, and the two alignment helpers are written with it.
- **A let-bound `Equal.cong` cannot be inferred** -- the earlier note is
  confirmed, with the exact symptom: `+u3s = Equal.cong(Nat, I.Int, v =>
  I.Int{v, 0n}, ds3, d3, e3s)` fails with `expected : an annotated term
  (cannot infer)` and `observed : int.Int{...}` (the *substituted* argument),
  which reads like a problem with the constructor literal and is not one; the
  same cong inlined in a `Equal.trans` checks. Let-bound `Equal.trans` values
  are fine, and so are let-bound *applications* of helper defs.
- **A hypothesis can be made reusable with `+`.** `R.Rat.nat.distrib` needs
  the same cross sum twice (once per scale), and the default linear hypothesis
  gives `expected : e2 / observed : e2 (consumed more than once)`. `+e2: {...}`
  in the telescope fixes it, which is the same quantity discipline the laws
  use on their own fields.
- **Constructor literals in argument positions**: `I.Int{ds, 0n}` as the `a`
  or `b` argument of a `cong` goes through `I.Int.unit(ds)` in this codebase's
  idiom; the failure above was *not* this, but the units are what the landed
  fills spell and there is no reason to write the literal.

Next, on the same recipe: **QExt over Rat** -- the field axioms, then the
multiplicative inverse `1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)`, whose
denominator is a difference of two squares and so is the first place the two
distributive laws meet a `Rat.sub`.


## Cross-file imports: the helper-naming rule that cost three rounds

`import ./laws.bend as L` plus `import ./proofs.bend` from a third file **does
work** -- that is the nat/int/qext pattern in "Laws vs proofs" above, and it is
how `int_proofs.bend` uses proved `Nat` laws. When it appears not to work, the
cause is almost always the naming rule below, not the split itself.

**The rule.** In a proofs file, two kinds of `def` share one namespace:

- a **fill** of a law must be spelled `def <laws-alias>.<law key>(...)` --
  that prefix is the mechanism that attaches the proof to the law;
- a **proof-only helper** must be named **bare** (`Nat.pred`, `NatIsPos`,
  `Nat.succ_add_ne_zero`), never with the laws-file alias.

A helper that carries the alias resolves only while the proofs file itself is
the *main* file. The moment another file imports it, the internal reference
becomes

    Error:
    - expected : a defined name
    - observed : R.Rat.add.piece

which reads as "this file cannot be imported" and is not.

**What it cost here.** All three of `Int.canon`-adjacent rounds were fine, but
`rat_proofs.bend` had **35 helpers** named with the alias (`R.Rat.add.piece`,
`R.Rat.add.cross`, `R.Rat.nat.d3`, ...). The symptom above was measured
faithfully and then generalised into "a `*_proofs.bend` file is not importable
at all", which is false. That mis-diagnosis produced `src/qrat_rat.bend` -- a
684-line transcription of `rat.bend`'s statements -- plus the ported fills for
them in `qrat_proofs.bend`, i.e. a hand-maintained duplicate of the whole Rat
layer whose copies nothing mechanically checked.

Commit `c921dbf` renamed the 35 helpers bare. `rat_proofs.bend` still checks,
and a probe that imports `rat.bend` **and** `rat_proofs.bend` and calls
`R.Rat.add_comm` checks too (it failed with exactly the error above before the
rename). The duplicate is therefore unnecessary and **it is gone**: `src/qrat_rat.bend`
(684 lines) is deleted, `qrat_proofs.bend` keeps only the QExt-specific fills
(the two coordinate witnesses, the two `QExt.mul` coordinate chains, and the
four law fills) and calls rat.bend's laws as `R.Rat.<law>`, filled by its
`rat_proofs.bend` import -- 1929 lines to 181. The whole QExt layer above the
Rat one now costs one call per Rat law: `QExt.neg_neg`, which used to carry a
port of `Rat.neg_neg` plus the Nat helper `nat.sub.min` and the two Rat helpers
`rat.mk.fixed.neg`/`rat.neg.neg`, is two `R.Rat.neg_neg` applications at the
law's own telescope (a literal `Nat.cmp` and `{==}` evidence, exactly as
`rat_proofs.bend` passes them to its own inner `mk.fixed`). So: **no layer of
this project needs to restate another layer's laws and proofs.**

**The mechanical check**, before concluding that anything is unimportable:

    # any def in the proofs file whose name is not a law key in the laws file
    # is a helper, and must be bare
    comm -23 <(grep -o '^def <alias>\.[A-Za-z0-9_.]*' proofs.bend | sed 's/^def <alias>\.//' | sort) \
             <(grep -o '^law [A-Za-z0-9_.]*' laws.bend | sed 's/^law //' | sort)

Every line it prints is a helper to rename. Empty output means the rule is
satisfied.

**Import order**: the round that deleted the duplicate tested it, and it is
*not* load-bearing here. `qrat_proofs.bend` lists the laws files first
(`nat.bend`, `int.bend`, `rat.bend`, `qrat.bend`) and the proofs files after
(`nat_proofs.bend`, `int_proofs.bend`, `rat_proofs.bend`), which is the order
`int_proofs.bend` uses; a copy of the same file with `rat_proofs.bend` imported
**first**, before `rat.bend`, checks just as green (`All terms check.`). So both
orders work at this size, and the laws-first order is kept as the convention
rather than as a rule.

**The lesson worth keeping.** A symptom that is measured honestly can still be
generalised wrongly. When a wall appears, compare it against the mechanism this
document already describes -- the helper-naming rule was written down for
`nat_proofs` long before it bit `rat_proofs`.

## The composing QExt laws: what the canonical presentation buys, what blocks the general form

`QExt.add_assoc` landed in the *canonical presentation* -- six coordinates, each
`Rat{Rat.num(np,nn), 1n+dp}` -- and its fill is exactly what the componentwise
shape promised: one `R.Rat.add_assoc` per coordinate, two calls, no hypothesis
and no case analysis. That is the same convention `QExt.neg_neg` already uses and
the one qrat.bend's header documents, and it is what makes the call possible at
all: `Rat.add_assoc`'s nine parameters *are* that presentation.

**The form over arbitrary QExt values is not in, and the reason is a proof-side
wall, not a false statement.** Both halves of that claim were measured.

*Truth side: nine witnesses, no counterexample.* Law-level reasoning is not
available here (the checker cannot reduce `Rat.add` on a variable), so the law
was **evaluated**: the operations were called on witnesses outside the canonical
presentation -- zero denominators, non-successor denominators, two-sided and
gcd-reducible numerators -- and the two sides compared. Writing
`Rat{Int{p,q}, d}` for `(p - q)/d`, all nine triples agree:

    (1/0, 1/1, 1/1)         both Rat{Int{1,0}, 0}
    (1/1, 1/0, 1/0)         both Rat{Int{0,0}, 0}
    (9/4, 2/6, 7/0)         both Rat{Int{1,0}, 0}
    (0/0, 3-1/2, 1-1/0)     both Rat{Int{0,0}, 0}
    (3-1/2, 1/3, -2/5)      both Rat{Int{14,0}, 15}
    (7-2/4, 1-5/6, 3-3/2)   both Rat{Int{7,0}, 12}
    (2-1/0, -3/0, 5/0)      both Rat{Int{0,0}, 0}
    (2-3/0, 5-1/0, -4/0)    both Rat{Int{0,0}, 0}
    (4/6, -5/0, 2-2/2)      both Rat{Int{0,1}, 0}

The pattern behind them is that a zero denominator makes both sides collapse to
the *sign* of one coordinate (the gcd of the inner sum's magnitude with a zero
denominator is that magnitude, so `div` turns the numerator into +-1 and the
outer denominator into 0), and the two sides collapse with the same sign. So no
evaluated witness justifies a hypothesis.

*Proof side: the closing lemma needs positivity, which nothing can supply.* For
arbitrary coordinates the Rat-level goal's two sides are `mk`-headed terms, and
the only lemma that compares two such terms is `Rat.mk.eqv.val`, whose
hypotheses include `Nat.cmp(0n, d1) == LT{}` and `Nat.cmp(0n, d2) == LT{}` --
positivity of the two denominators it compares. An arbitrary `Rat` has none:
`Rat{Int{1,0}, 0}` is a legal argument, `mk`'s behaviour there is junk (rat.bend
says so where it defines `mk.go`), and every value lemma in the layer carries the
same hypothesis for the same reason (`mk.value`, `mk_idem.raw`,
`add.value.mixed`, and `Nat.div_pos_wit` under them). Reaching the general form
therefore needs one of:

- an mk-headed `Rat.add_assoc` stated at those same hypotheses -- and then a way
  to *discharge* them for arbitrary coordinates, which does not exist (an
  arbitrary coordinate's denominator is not positive, and no bridge turns an
  arbitrary `Rat` into a canonical one: `==` is structural, so
  `Rat{Int{4,0}, 2}` is not `Rat{Rat.num(4,0), 2}`); or
- a proof of the zero-denominator cases on their own: a case analysis on which of
  the three input denominators is zero, with the collapse lemmas under it
  (`gcd(a, 0) = a`, `div(a, a) = 1`, `mul(x, 0) = 0`, `div(0, g) = 0`), which the
  nine witnesses above say would work but which is a campaign of its own.

**The multiplicative composing laws are further out, for a second reason.**
`QExt.mul`'s coordinates are *sums of products* (`xa*ya + d*xb*yb`), so
`QExt.mul_assoc` and `QExt.mul_distrib` are not componentwise
`Rat.mul_assoc`/`Rat.mul_distrib` calls at all -- the derivation needs those Rat
laws at **mk-headed** arguments (every product and every sum in the goal is an
operation's output), i.e. the same rung-2 work, and it needs it for three Rat
laws rather than one.

**The rung-2 shape, when it is built.** The statement that both a fill and a
caller can use is over *arbitrary Rat variables*
(`for +x: Rat, +y: Rat, +z: Rat {add(add(x,y),z) == add(x,add(y,z)) : Rat}`), not
over `Rat.mk(...)` applications: a caller's coordinates are pattern variables,
`Rat.add` on a variable is stuck, and a law whose arguments are constructor
literals cannot be instantiated at a stuck term. Its fill is reachable in the
same way the fills in this repo already reach past a match -- one helper def per
level of destructuring, since a def's *parameters* may be matched at its body
head (`match xa ya za:` inside the helper that takes them), which sidesteps the
"no nested matches on pattern variables" rule without weakening anything.

## The rung-2 mk-headed `Rat.add_assoc`: the one bridge, and why the `Int` endpoint cannot carry it

The rung-2 additive law over arbitrary Rat variables with the positivity of the
three inputs as hypotheses (`{Nat.cmp(0n, Rat.denof(x)) == LT{}}` on `x`, `y`,
`z`) is settled except for **one bridge**: "mk of a projection pair is mk of
`Rat.num(a,b)`". Everything else about it was derived and nothing about it is a
fill problem; the bridge is where the round stopped, and the three measurements
below are why it is not the step it looks like.

**What the bridge's left side actually is.** `Rat.mk_idem.raw`'s left side is
`mk(Rat.numof(M), denof(M))` with `M = mk(Rat.num(a,b), d)`, and `mk` reduced its
argument, so it is

    mk(I.Int{Nat.div(Nat.sub(P, Q), G2), Nat.div(Nat.sub(Q, P), G2)}, W)
    P = sub(a,b)   Q = sub(b,a)   G2 = gcd(sub(P,Q) + sub(Q,P), d)   W = denof(M)

-- note the *outer* gcd: its magnitude is `mag(P,Q)`, a sum of two truncations,
not `mag(a,b)`. Naming `Rat.num(a,b)` means two **`sub_diag` collapses that reach
under a `Nat.div` dividend**, one per coordinate, and the two sit in *different
positions of the same `Int`*.

**Why one congruence cannot do both.** `Equal.cong(Nat, Int, u => Int{div(u,G2),
r}, sub(P,Q), P, sub_diag(...))` puts `P` in the first coordinate and leaves the
second untouched, so the second coordinate's own collapse is unreachable by the
same motive; a 2-step `Equal.trans` using two such congs then leaves

    Nat.div(Nat.sub(Nat.sub(a,b), Nat.sub(b,a)), G) == Nat.div(Nat.sub(a,b), G)

which **`{==}` cannot close** although `sub_diag` proves the two dividends equal:
once one coordinate of an `Int` has been rewritten, the two `Int`-level endpoints
stop being convertible, so the checker no longer sees the pair it would have to
compare. (A let-bound `u => Nat.div(u, G2)` cong is rejected outright --
`cannot infer` -- the rule this file already records.)

**The measurement that retires the "bridge" framing.** `R.Rat.num(p,q)` and
`I.Int{p,q}` **are definitionally equal** -- `Rat.num` unfolds to
`Int{sub(p,q), sub(q,p)}` -- so there is no gap of *that* kind to bridge anywhere.
The difficulty is only the truncations inside the projection's two `div`s, and
that is why the honest statement of the missing fact is
`mk(Int{div(P',G2), div(Q',G2)}, W) == mk(Rat.num(a,b), W)` with `P'`, `Q'` the
projection's own arguments, not a respelling of `Rat.num`.

**Consequence for the statement.** `mk(I.Int{p,q}, W) == mk(Rat.num(p,q), d)` is
**false as a universal statement**: it would demand
`Int{p,q} == Rat.numof(mk(Rat.num(p,q),d))`, i.e. that the projection's two
quotients reproduce the raw pair. So the helper has to be **parameterized by the
truncation equalities** and both collapses have to be performed in **one pass**
(a single `Equal.cong` whose evidence is the pair equation, not two steps).

**Last measured error, for the record:**

    - expected : Nat.sub(a, b)
    - observed : Nat.sub(Nat.sub(a, b), Nat.sub(b, a))
    Location: Rat.mk_idem.form

**The one spelling this round did not try**, and the reason it is the right next
move: state the helper over
`mk(I.Int{sub(sub(a,b),sub(b,a)), sub(sub(b,a),sub(a,b))}, W)` on the left --
exactly the pair `mk_idem.raw` produces, written as one term -- and reach the
goal's `mk(Rat.num(a,b), W)` by **one `Equal.cong` on `Rat.mk`'s second argument
plus the two coordinate collapses in one pass**, so that no `Int`-level endpoint
is ever left half-rewritten. The alternative, if that fails too, is to have the
worker supply positivity at the projections' own `Rat.denof` spelling (`pq`),
which `mk_idem.raw` requires but which no caller can currently write
definitionally.

### The bridge, attempted: the coordinates do not reduce, and the reducer is `Nat.sub` (measured)

The spelling above **was** tried, and the attempt turned the three guessed facts
below into measurements. The helper was written out in full, in five variants, in
`rat_proofs.bend`; each one failed at the same place, and the tree was restored.

- **`Nat.div(sub(sub(a,b),sub(b,a)), G2)` does not reduce to `Nat.div(sub(a,b), G2)`**,
  and neither do the two `Nat.sub` terms alone. `Nat.sub` matches on **both**
  arguments (`base.bend`: four cases, `0n 0n` onwards), so a diagonal
  `sub(sub(X,Y), sub(Y,X))` is stuck: nothing about it is a constructor, and the
  comparison that would collapse it lives in `sub_diag`'s *fill*, not in the
  evaluator. Measured directly: the goal `{sub(sub(sub(a,b),sub(b,a)), ...) == sub(sub(a,b),sub(b,a))}` is
  `All terms check.` (that is `sub_diag`'s own statement), while
  `{Nat.div(sub(sub(a,b),sub(b,a)), G2) == Nat.div(sub(a,b), G2)}` is **not**,
  with `{==}`. So "the collapse is definitional under the division" -- the
  assumption the round above was built on -- is **false**, and the two collapses
  are genuinely needed as rewrites.

- **`sub_diag` is only half an answer, and that is a statement and not a fill
  problem.** It gives `sub(sub(X,Y),sub(Y,X)) == sub(X,Y)`; the cross sum
  `mk.eqv.val` asks for needs `sub(X,Y) == sub(sub(X,Y),sub(Y,X))` -- the same
  equation read the other way -- and `Equal.sym` is the only thing that turns one
  into the other. `sub_diag` in that orientation is rejected, and `Equal.sym`
  around it is rejected too, with the two ends of the error **swapped**:

      - expected : {sub(sub(b,a),sub(a,b)) == sub(b,a)}
      - observed : {sub(sub(sub(b,a),sub(a,b)), sub(sub(a,b),sub(b,a))) == sub(sub(b,a),sub(a,b))}

  Swapping `Equal.sym`'s arguments, and swapping the `Equal.cong`'s `(a, b)`
  pair, each only swap the same two messages: every one of the four combinations
  was run, and in each the demand and the evidence come back as each other's
  reverse. So at this argument shape **`Equal.sym` cannot be composed with
  `Equal.cong`**, whichever way round it is written -- a new checker entry for
  this file's list, and the reason the "one pass" plan above cannot be assembled
  the obvious way. (What *does* work at these shapes: a **named def** as the
  congruence motive. `u => Nat.mul(u, W)` is rejected where
  `def Rat.mul.W(+W, u) = Nat.mul(u, W)` checks, and
  `u => Nat.add(A, u)` is rejected where a named `Rat.add.L`/`Rat.add.R` checks --
  both measured, both at the real argument shapes.)

- **The cross sum needs the *first* coordinate stated non-collapsed**, which is
  why `mk.rep` cannot be the closing step either. `mk.eqv.val` instantiates
  `xp := div(sub(P,Q), G2)`, and the first coordinate of a *quotient* has no
  collapse (`div(Pq, G2)` is not `div(sub(P,Q), G2)`), so the cross sum's left
  side is stuck with `Pq` and the right with both raw coordinates. The only
  product identity that then closes it is `sub_cross`'s cross sum
  (`(a-b) + b == (b-a) + a`) at the raw pair, lifted through `mul_add_left` on
  both sides and `add_comm` -- and that lift is exactly where the `sub_diag`
  orientation above bites.

**State of the rung-2 law after this round.** The mathematics is settled: the
cross sum is `Nat.sub_cross` at `(sub(a,b), sub(b,a))`, the two product spellings
are two `Nat.mul_add_left`s, and the closing is `Rat.mk.eqv.val` + `Rat.mk.trunc`
-- all four verified in isolation (`All terms check.`). What is missing is one
composition: a `Equal.cong` whose evidence is a `sub_diag` used in the reverse of
its stated orientation. The two ways out that the measurements leave open are (a)
a `sub_diag`-shaped law **stated in the reverse orientation** (which is legal and
would make the evidence direct -- no `Equal.sym` anywhere), and (b) a cross-sum
law stated over the collapse so that no re-orientation is needed at all.

## The reverse law landed -- and what the write path actually costs (measured)

Way (a) above was taken. `nat.bend` has `sub_diag_rev` (`sub(np,nn) ==
sub(sub(np,nn), sub(nn,np))`, the twin spelling of `add_assoc_rev` /
`cmp_gt_of_lt` / `mul_add_left`), its fill in `nat_proofs.bend` is one
`Equal.sym` around `sub_diag`, and both check. Counts move transitively as the
README records: nat 126 -> 127, rat 197 -> 198, qrat 202 -> 203. **The law is
correct, filled and green; it does not by itself close the rung-2 fill.** The
round stopped at a *different* wall, and the three measurements below are what
the next round should start from.

**`Equal.cong`'s orientation, read off the source, is a rule worth writing
down.** `Equal.cong(A, B, f, a, b, e)` is defined as `%e : {f(a) == f(_) : B}`
and `Equal.sym(A, a, b, e)` as `%e : {_ == a : A}`, i.e.

    e : a == b      |- cong f a b e : f(a) == f(b)
    e : a == b      |- sym a b e   : b == a

At the shapes this file uses that is exactly what the checker does: the call
`cong(Nat, Int, u => Int{u, c}, sub(X,Y), sub(sub(X,Y),sub(Y,X)), sub_diag_rev)`
synthesizes `Int{sub(X,Y),c} == Int{sub(sub(X,Y),sub(Y,X)),c}` -- the collapsed
side first, the diagonal side second -- and `sym` around the same evidence
yields the reverse. So a rewrite in the orientation "collapsed -> diagonal"
takes `sub_diag_rev` and one in the orientation "diagonal -> collapsed" takes
`sub_diag` through `sym`; the spelling is what makes the evidence direct, and
that part of the round's premise is confirmed.

**A `cong` **nested** inside another `cong` does not compose at this shape, and
the two message pairs are the reverse of each other.** Every one of the four
combinations of `(inner a, inner b)` with `(plain evidence, Equal.sym around
it)` was run at the product-collapse goal
`Int{Xp,Yp} == Int{sub(X,Y),sub(Y,X)}` (`Xp = sub(sub(X,Y),sub(Y,X))`,
`Yp = sub(sub(Y,X),sub(X,Y))`, under the motive `u => Int{u, 0n}`):

    expected : {sub(X,Y) == Xp}          observed : {Xp == sub(X,Y)}
    -- and the reverse pair for each of the other three spellings.

The outer `cong` wants `f(a) == f(b)` at its own endpoints; the inner one
delivers `f(a') == f(b')` at whatever its own endpoints are, and no choice of
the four spellings makes the two meet. This is the same "the demand and the
evidence come back as each other's reverse" shape the section above records for
`Equal.sym`, now one level down: **the congruence has to be *standalone* (a
direct argument of `Equal.trans`) for the orientation rule to apply.** Three
rewrites of this kind are therefore written as
`trans(a, b, c, cong(...), cong(...))` with the intermediate type spelled out --
which is the repo's own idiom, and the measurement says it is the only one.

**The wall is now `Int.mul`, not the evidence.** With the two standalone congs
in place the chain reaches

    Int.mul(Int{Xp, Yp}, Int{d, 0n})  ==  Int{mul(sub(X,Y), d), 0n}

and the remaining step is `Int.mul_scale` at `(sub(X,Y), Yp)`, whose own fill
(`int_proofs.bend:154`) proves that product reduces in exactly that way. What the
checker reports instead is a *reduction* mismatch: the goal's left side comes
back **stuck** as `Int.mul(...)` while the very same term inside the `trans`
argument is observed **unfolded** to
`Int{add(mul(Xp,d), mul(Yp,0)), add(mul(Xp,0), mul(Yp,d))}`:

    - expected : {Int.mul(Int{Xp,Yp}, Int{d,0n}) == Int{mul(sub(X,Y),d), mul(Yp,0n)} : Int}
    - observed : {Int{add(mul(Xp,d), mul(Yp,0n)), add(mul(Xp,0), mul(Yp,d))} == ...}

So the same application is unfolding on one side of the comparison and staying
stuck on the other. Two routes are open and neither was run to ground: force the
unfold once, at `Int` level, so that both sides are the same *term* rather than a
term and its reduct (the repo already has the shape -- `Rat.add.value`'s fill
writes `Int.mul_scale` as the first `trans` step and never relies on the goal
reducing); or state the collapse helper over the *unfolded* pair
(`Int{add(mul(...),mul(...,0n)), ...}`), which is `I.Int.mul_scale`'s own source
spelling, so that the motive never has to see `Int.mul` at all. The second is
the smaller change and is the one to try first.

**Not run, and therefore not claimed:** the rung-2 `Rat.add_assoc` statement is
not in `rat.bend`, `QExt.mul_assoc` / `QExt.mul_distrib` / the multiplicative
inverse are not started, and `QExt.add_assoc` is still the canonical-presentation
form. Nothing was left stated-but-unfilled: `scratch.bend` was restored to its
committed state and all six gates are green at that commit.

## The rung-2 additive law landed, and the bridge was not needed (measured)

`Rat.add_assoc.arb` is in `rat.bend` and filled in `rat_proofs.bend`: arbitrary
`Rat` variables `x`, `y`, `z` with `{Nat.cmp(0n, Rat.denof(_)) == LT{}}` on each
of the three, conclusion `add(add(x,y),z) == add(x,add(y,z))`. Counts move as the
README records: rat 198 -> 199, qrat 203 -> 204 (the canonical `Rat.add_assoc`
stays *stated*, so no existing call site moved; its fill is now one call of the
general law -- see the ordering rule at the end of this section).

**The route that worked is not the route the last two rounds were on.** Those
rounds tried to reach the law by *bridging a mk-headed summand*: to turn
`mk(numof(M), denof(M))` into `mk(Rat.num(a,b), W)` (`Rat.mk_idem` and its five
attempted forms), which is where the `Int.mul` wall and the nested-`cong` wall
were measured. The fill that landed never writes those terms: it destructures the
three inputs **twice** -- once into the Rat fields, once into the three `Int`
numerators -- and after that second level *every* term on both sides is a
constructor-headed `mk` whose arguments reduce by themselves. No `mk_idem`, no
projection bridge, no `Int.mul`-stuck-against-its-reduct comparison appears
anywhere in it. The two measurements that stopped the previous round are still
true statements about the terms *that route* produces; they are simply not on
this one. (The three `*_proofs` gates and `scratch` are green at this commit, and
`rat_proofs.bend` has no unfilled law.)

**Why two levels, and why the two matches are helpers.** `Rat.add(x, y)` on a
*variable* is stuck -- `Rat.add` destructures its arguments -- so the first match
(Rats into fields) is what makes the operations reducible at all. After it the
numerator of each input is still an `Int` *variable*, so `Int.mul(numerator, unit
den)` is stuck in turn (`Int.mul` matches on its first argument), and the `mk`
around the stuck sum cannot destructure its argument. The second match (the three
`Int`s into their coordinate pairs) is what makes all of that reduce. Each level
is a `def` whose *parameters* are matched at its body head, which is the repo's
way around "no nested match on a pattern variable"; the level-2 helper's
statement is the law's own conclusion written over the three `Int` numerators,
and the coordinates cannot appear in a type (they are bound by the match inside).

**A dependent match does refine the hypotheses, measured.** The law's positivity
hypotheses are stated over `Rat.denof(x)`; in the level-1 branch `px` is usable at
`{Nat.cmp(0n, xd) == LT{}}` (the checker rewrites `Rat.denof(Rat{xn,xd})` to
`xd`), so the hypotheses pass straight into the level-2 helper. A two-line probe
(a helper taking `{Nat.cmp(0n, d) == LT{}}` called with `xd` and `px`) checks,
and that is what the fill relies on.

**The chain is the old canonical chain, at raw coordinates -- and it is now the
only copy.** The three
inputs' numerators are the pairs the match bound -- *truncations of nothing*, the
whole difference from rung 1 -- the inner sums' clean coordinates are the two
`Int.mul_scale` re-spellings `U1/V1`, `U2/V2`, the mk-headed summands become
`mk(Rat.num(P,Q), d)` by `Rat.mk.trunc`, each outer add is one
`Rat.add.value.mixed`, and the closing is `Rat.mk.eqv.val` at
`Rat.nat.cross4`'s cross sum from the two `Nat.sub_cross` instances. That whole
Nat block is *verbatim* what the canonical fill had: its hypotheses are gaps in
the raw coordinates, so it never saw the presentation at all. `R.Rat.add_assoc`
(the canonical law's fill) is now one call of this one --
`Rat.add_assoc.arb(Rat{Rat.num(np1,nn1), 1n+dp1}, ..., {==}, {==}, {==})` -- since
at `Rat{Rat.num(np,nn), 1n+dp}` each hypothesis is `Nat.cmp(0n, 1n+dp)` up to the
definition of `Rat.denof`, i.e. `LT{}` by computation. The 227-line canonical
chain is gone; the general fill carries it.

**One ordering rule this cost, measured.** The wrapper's *first* spelling put the
canonical fill before the general one in the file, and the checker rejected it
with

    - expected : a filled definition (an unfilled law is a dead claim: live code
                 cannot use it)
    - observed : rat.Rat.add_assoc.arb

-- a *law* may only be used in live code once its fill has been processed, and
fills are processed in file order. Moving `R.Rat.add_assoc.arb`'s definition
above the wrapper's fixed it with no other change. So in a proofs file that
wraps one law with another, the wrapped law's fill has to come first.

**Two pieces had to be new, and both are general.**

- `Rat.add.value.mixed` (same key, statement generalized): its second summand was
  `Rat{Rat.num(np2,nn2), 1+dp2}`, and rung 2 has `Rat{Int{Zp,Zn}, D}` -- a *raw*
  pair, which is a different pair from `Rat.num(Zp,Zn)` unless a coordinate is
  zero, over a denominator that is carried rather than computed. The old
  statement is the reading `Zp := sub(np2,nn2)`, `Zn := sub(nn2,np2)`,
  `D := 1n+dp2` of the new one (since `Rat.num(np2,nn2)` *is*
  `Int{sub(np2,nn2),sub(nn2,np2)}`), which is why the canonical fill's two call
  sites only gained three arguments. `D`'s positivity is a third hypothesis of
  the same kind as the two it already had. The fill did not change its shape at
  all: `Rat.add.mixed.cross` was already stated over an `Int` numerator and a
  `Nat` denominator.
- `Rat.div.pos` (a bare proof-only helper, no new Nat law): the positivity of
  `Rat.denof(mk(Rat.num(P,Q), d)) = div(d, G)` at the *dividend's own spelling*.
  `Nat.div_pos_wit` is stated at `div(1+ap, G)`, and here `d` is a variable
  product (`Xd*Yd`), so no `1+ap` reduces to it -- which is exactly why
  `Rat.mk_idem.raw` and `Rat.add.value.mixed` take the fact as a hypothesis and
  why the earlier rounds called the derivation unavailable. It is available, by
  two rewrites: `pos_witness` turns `d` into `1 + (d-1)`, the *witness type*
  `Nat.divides(G, d)` is transported to `Nat.divides(G, 1+(d-1))` (**the `%`
  rewrite form, `%e : {P(_)}; body`** -- the witness type is indexed by the
  dividend and no conversion re-spells it), and the conclusion comes back along
  the same equation. The helper is stated over `{Nat.cmp(0n, d) == LT{}}` and a
  witness, so any caller with a carried denominator can use it.

**A measurement about `%` worth keeping.** `%e : {T}; body` is a *goal rewriting*
step, not an assertion: the motive `T` has `_` as its endpoint binder, the check
is `T(b) <= goal` (where `b` is `e`'s second endpoint) and the body is checked
against `T(a)` with the trivial equation. That is the only mechanism in the
language that re-spells a *type* -- `Equal.cong`/`Equal.sym`/`Equal.trans` build
equations between terms, and conversion is not a transport -- and it is what
`Rat.div.pos` uses. `Equal.cong`/`Equal.sym` are themselves written with it
(`base.bend`), which is also why the cong-orientation rule the section above
records holds.

**Not done, and therefore not claimed:** `QExt.mul_assoc` and `QExt.mul_distrib`
are not started, and the inverse is not started. The multiplicative laws need
`Rat.mul_assoc`/`Rat.mul_distrib` at mk-headed arguments, i.e. the same two-level
treatment. The first of those is now available (see the section at the end of
this file, which also corrects this paragraph's earlier claim that "no new value
lemma is needed"). The second is not, and *that* is the concrete next blocker,
measured by reading the statements rather than by running anything: `Rat.mul_distrib`
and `Rat.mul_add_left` are stated over `Rat{Rat.num(np,nn), 1n+dp}` only, and no
unconditional distributive law exists in rat.bend at all -- while a `QExt.mul`
coordinate is `Rat.add(Rat.mul(..), Rat.mul(..))`, an mk-headed sum of mk-headed
products, and `==` on Rat is structural. So a QExt multiplicative fill has to
expand `(a*c + d*(b*e))*f`, which is distributivity at three arbitrary Rats; the
canonical law cannot be instantiated there, and no value law or bridge turns an
arbitrary Rat into a canonical one. The rung-2 distributive block (the additive
fill's *linear* Nat closing, not this one's bilinear one) is therefore the next
piece of work, and `QExt.mul_assoc` is downstream of it. The inverse
`1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)` is not started; and
`QExt.add_assoc` **is** the form over arbitrary values now: same key, statement
replaced, and its fill is one `Rat.add_assoc.arb` per coordinate with the six
positivity hypotheses spent three per coordinate. The canonical statement is gone
rather than kept beside it, because at this layer the general form *does*
subsume it (a canonical caller supplies each hypothesis with `{==}`, since
`Rat.denof(Rat{Rat.num(np,nn), 1n+dp})` is `1n+dp`) -- unlike the Rat layer, where
the canonical `Rat.add_assoc` stays stated because its positivity slot is empty.
Two new `def`s came with it, `QExt.re`/`QExt.im`, since a statement has no body to
put the destructuring match in.

## The rung-2 multiplicative law landed, and the analysis was half right (measured)

`Rat.mul_assoc.arb` is in `rat.bend` and filled in `rat_proofs.bend`: arbitrary
`Rat` variables `x`, `y`, `z` with `{Nat.cmp(0n, Rat.denof(_)) == LT{}}` on each
of the three, conclusion `mul(mul(x,y),z) == mul(x,mul(y,z))`. Counts move as the
README records: rat 199 -> 201, qrat 204 -> 206 (the new law is
`Rat.mul.value.mixed`; the canonical `Rat.mul_assoc` stays *stated*, its fill
unchanged, and no call site moved). The six gates are green.

**What the earlier analysis got right.** The raw product pair of two coordinate
pairs *is* a constructor: after the level-2 match,
`Int.mul(Int{a1,b1}, Int{a2,b2})` reduces by itself to
`Int{add(mul(a1,a2),mul(b1,b2)), add(mul(a1,b2),mul(b1,a2))}`, so the additive
fill's two `Int.mul_scale` steps and its whole sum-assembly block have no
counterpart -- measured as the `{==}` steps in `Rat.mul.arb.coords` and by the
absence of any shape law from the fill. And `Rat.mk.value` does name its
numerator in `Rat.num` spelling, so the raw-pair presentation has to be reached
by a value equation and not by conversion -- also measured.

**Where it was wrong, in both directions.** The old comment said the fill "goes
through `Rat.mk.trunc` and `Rat.mk.rep`, exactly as the additive one does" and
that "no new value lemma is needed". Measured: `Rat.mk.rep` alone bridges the
inner product (`mk(Int{U1,V1},d1)` against `mk(Rat.num(U1,V1),d1)`; `mk.trunc` is
its truncation-spelled twin and was *not* used), and a new value law **was**
needed -- `Rat.mul.value.mixed`, whose right side is the raw product pair
`mk(Int.mul(Int{P1,Q1}, Int{Zp,Zn}), d*D)`. What makes that law cheap is the same
constructor fact: the additive twin's cross block (`Rat.add.mixed.cross` over a
sum of scaled pairs) collapses to a pure ring permutation with no sums in it
(`Rat.mul.mixed.cross`, eleven steps). The law's fill is then the additive fill's
four pieces with the cross swapped.

**The Nat closing is where the port genuinely fails, and the reason is linearity
versus bilinearity.** The additive law's two sides have coordinates
`P1*Zd + a3*(Xd*Yd)`: a *linear* combination, so the padded equations scale to
them directly and the shared padding reconciles with `Rat.nat.pad`. The
multiplicative coordinates are `P1*a3 + Q1*b3`: the *bilinear* contraction of the
truncated pair with the third factor's pair, so the two sides are different
products of the same six numbers and what reconciles them is an associativity
identity, not a padding. Three helpers carry it:

- `Rat.nat.mulpad`, from one `Nat.sub_cross` instance `p + v = q + u`, gives
  `(p*r + q*s) + (u*s + v*r) = (u*r + v*s) + (p*s + q*r)` -- each side's
  contracted coordinates plus the rest of the two pairs' products as padding.
  The proof is `Nat.mul_add_left` twice per side plus `Rat.nat.swap`.
- `Rat.nat.mul3` cancels the two paddings against each other. This is exactly
  `Int.mul_assoc.pos` and `Int.mul_assoc.neg` -- the laws the *canonical*
  `Rat.mul_assoc` fill already had -- read at the six raw coordinates, plus four
  `Nat.mul_comm` steps and one exchange of the two groups.
- `Nat.add_cancel` then strips the common padding from the two combined
  equations, and `Rat.nat.scale.eq.r` puts the result in the D-scaled form
  `Rat.mk.eqv.val` consumes.

**Checker rules this round paid for (all measured).**

- `Equal.sym`'s first argument is the type of its two endpoints. Passing `Nat`
  for `Int` endpoints produces an *empty* error message -- just `Error:` and a
  location -- which is what an ill-typed type argument looks like.
- A hypothesis binder without `+` is linear. Using it twice gives
  `expected : h / observed : h (consumed more than once)`; `+h` is the fix.
- In a nested `Equal.trans` the *declared* middle endpoint must be the term the
  first evidence actually produces, not the term the chain is heading for.
  Writing the final form there makes the checker demand that the first evidence
  span the whole chain, and writing an outer endpoint that disagrees with the
  inner chain's end makes it demand the inner chain's type one level up. Both
  were hit and both are fixed by spelling the intermediate exactly.
- `Int.mul` of two constructor pairs reduces, so `{==}` can carry a step whose
  two sides differ only by that unfolding. The additive fill's `Int.mul_scale`
  calls exist because one of its factors is a *unit* (`Int{d,0n}`), where the
  reduction leaves `mul(x,0n)` stuck; with two general pairs there is no such
  residue and no law is needed.

## The rung-2 distributive laws landed, and the closing was already there (measured)

`Rat.mul_distrib.arb` and `Rat.mul_add_left.arb` are in `rat.bend`, filled in
`rat_proofs.bend`. Counts: rat 201 -> 203, qrat 206 -> 208. Six gates green.

**The canonical fill's closing transposed verbatim, which was the one thing this
round did not have to build.** `R.Rat.mul_distrib`'s right-hand chain (M1/M3
through `Rat.mk.rep`, `pos_witness` and `Rat.add.value` to UR), its pure Nat
identity (T) from `Rat.nat.distrib`, and its two `mk.eqv.val` comparisons are
stated over terms this law has too: U1,V1 and U3,V3 are the same two products'
coordinates, U2,V2 the same sum's raw coordinates, P1/Q1/P3/Q3 the same
truncations, and UR's coordinates and denominator (P1*d3 + P3*d1 over d1*d3) come
out identical -- so `T`, `cross2f`, `val2` and r1/r2/r3 are the canonical calls
with only the two positivity arguments changed from `{==}` to the hypotheses.
`Rat.mul_add_left.arb` is the canonical mirror's three-step derivation.

**The left side is the new part, and the mixed value law does it in one call.**
The canonical fill computes `mk(Int{TLp,TLn}, Xd*m2)` -- the div/gcd-spelled
numerator mk's own reduction produces -- and bridges it to UL with a third
`mk.eqv.val` at `Rat.nat.cross1`'s cross sum, which needs `Rat.value.scaled` and
the value equation's two scaled coordinates. Here `Rat.mul_comm` (to put the
mk-headed sum on the left, where `Rat.mul.value.mixed` takes it), `Rat.mk.rep`
(to re-spell the sum's raw pair as its truncation pair) and that one law land
directly on `mk(Int.mul(Int{P2,Q2}, Int{a1,b1}), d2*Xd)`, whose pair is UL's up
to four `Nat.mul_comm` steps inside the two coordinates. No cross1, no
value.scaled, no div/gcd spelling anywhere -- the same saving the multiplicative
assoc fill got, for the same reason.

**One more checker rule, measured.** In a `%`-free chain every intermediate has
to be *written*: the second coordinate's rewrite here is two steps
(c2 -> c2b -> c2c), and passing only the second step's evidence to the cong that
consumes the first step's result fails with the expected/observed pair showing
the skipped intermediate. Unlike the `%` orientation rule this one is not a trap
in the checker -- it is just that a cong's evidence must have the endpoints the
cong names.

## The QExt multiplicative laws landed (measured)

`QExt.mul_assoc` and `QExt.mul_distrib` are in `qrat.bend`, filled in
`qrat_proofs.bend`. Counts: rat 203 -> 205, qrat 208 -> 212. Six gates green.

**The blocker was exactly the one predicted, and two more Rat laws closed it.**
`Rat.mul_distrib`/`Rat.mul_add_left` are stated over `Rat{Rat.num(np,nn), 1n+dp}`
only, and a `QExt.mul` coordinate is `Rat.add(Rat.mul(..), Rat.mul(..))` -- an
mk-headed sum of mk-headed products -- so the QExt fills need the rung-2
distributive laws, which is what the previous section landed. They also need two
more facts that did not exist: **`Rat.mul.den.pos` and `Rat.add.den.pos`**, the
positivity of a product's (resp. a sum's) denominator from its operands'. Every
rung-2 law takes `{Nat.cmp(0n, Rat.denof(t)) == LT{}}` for *three arbitrary*
Rats, and a QExt coordinate is a product of products, so a fill that instantiates
them has to build those facts itself -- and it cannot call `Rat.div.pos`, which
is a proof-only helper of rat_proofs.bend and unreachable from a third file
(measured again this round: `Rat.div.pos` there fails with "expected : a defined
name"). Both new laws' fills are one `Rat.div.pos` at the coordinates mk
destructures, with the second destructuring level written out because `Int.mul`
(resp. `Int.add` of two scaled pairs) is stuck while its arguments are variables.

**A stale checker note, remeasured.** `qrat_proofs.bend`'s header recorded that a
`cong` whose function is a lambda cannot be handed to anything -- four
measurements, and the conclusion that every fill had to be a whole-coordinate
rewrite or a def with the position as a parameter. That is no longer true:
lambda congs check as a def body, as an argument of `Equal.trans`, and nested
under another cong, in a third file importing rat.bend and rat_proofs.bend. The
old measurements were symptoms of the alias-prefixed helper names that same
header describes; with those renamed bare, all three placements check, and
`QExt.mul_assoc.re`/`.im` below are built out of them. The header is corrected in
place.

**What each fill is.** `QExt.mul_assoc` is two coordinate chains. Both sides of
each are expanded to the same flat sum of four products by `Rat.mul_assoc.arb`,
`Rat.mul_distrib.arb` and `Rat.mul_add_left.arb`, and the two groupings are
reconciled with `Rat.add_assoc.arb`/`Rat.add_comm` (a five-step rearrangement,
the same shape the rung-2 distributive fill uses for its own two groupings).
`QExt.mul_distrib` is the same shape with two `Rat.mul_distrib.arb` calls per
coordinate (three for the real one, where the radicand coefficient also
multiplies a sum) and no associativity shuffle at all. The radicand coefficient
`QExt.nat(d)` is `Rat{Rat.num(d,0), 1}`, so its denominator's positivity is
`{==}` at every call site, by computation.

## The negation laws landed, and the shape the previous round stated was not the provable one (measured)

`Rat.mk.diag`, `Rat.mul_neg` and `Rat.add_neg` are in `rat.bend`, filled in
`rat_proofs.bend`. Counts: rat 205 -> 208, qrat 212 -> 215. Six gates green
(nat, int, qext, rat, qrat `*_proofs.bend` and `scratch.bend`).

**The round before this one ended red, and the rerun said so.** Both
`rat_proofs.bend` and `qrat_proofs.bend` failed at `Rat.mk.diag` with the same
error: the fill's first `Equal.trans` declared `0n` as the middle endpoint of a
cong that actually produces `add(0n, u)`, and the file also called a
`Rat.mk.split` helper that does not exist. That is the nested-`trans` rule
already recorded in the gotchas -- the declared middle must be the term the
first evidence produces -- plus its usual cause, a chain written before it was
checked. `Rat.mul_neg`'s fill was ill-typed (`R.Rat.mul(xn, ...)` with `xn` an
`Int`) and `Rat.add_neg` had no fill at all, so the previous round's
"Six gates green" was never true of the tree it left. Everything below starts
from that measurement.

**`Rat.mk.diag` is one chain and no new machinery.** The divisor collapses
because `mag(T,T) = (T-T) + (T-T) = 0` and `gcd(0,d) = d`, both coordinates of
the numerator are `div(0,G) = 0`, and the denominator is `div(d,d) = div(1+ap,
1+ap) = 1` -- four congs, `Nat.sub_self`, `Nat.div_zero`, `Nat.div_self` and
`pos_witness` for the successor spelling. Two of the endpoints in the previous
attempt were also *oriented* the wrong way (`Equal.sym` supplies `b == a` from
`a == b`, and the fill had used it where the cong needed the forward direction),
which is the orientation rule the file's gotchas already carry.

**`Rat.mul_neg` is not a congruence law, and the reason is not the arithmetic.**
The two sides' *raw* numerators do line up -- `Int.mul(xn, Int.neg(yn))` and
`Int.neg(Int.mul(xn,yn))` are the same constructor pair, and a probe in
`rat_proofs.bend` confirmed the checker reduces both of them at concrete
coordinates -- but `Rat.mul` destructures its second argument, and `Rat.neg(y)` is
`mk(Int.neg(yn), yd)` with `Int.neg(yn)` *stuck* while `yn` is a variable, so
`numof` cannot fire and the goal never reduces to the congruence shape the
block at the top of `rat.bend` uses. What makes the law cheap instead is that
negation is multiplication by -1:

    Rat.neg_eq_mul_negone:  -y = (-1)*y

an **unconditional** helper whose fill is two congs. Both sides are `Rat.mk` of
raw pairs once `y` is destructured -- `Int{ynn,yp}` over `yd` against
`Int{add(ynn,0), add(yp,0)}` over `add(yd,0)` -- and the pairs differ by one
`Nat.add_zero` per coordinate. That is a *measured* statement about how much the
checker computes: a probe def asserted `Rat.mul(Rat.neg(Rat.one()),
Rat{Int{5,3},2}) == Rat.mk(Int{add(3,0), add(5,0)}, add(2,0))` with body `{==}`,
and it checked, i.e. `Rat.neg(Rat.one())` reduces to the constructor
`Rat{Int{0,1},1}` (through `gcd` and `div`), `Nat.mul(1n, a)` reduces to
`add(a, 0n)`, and `add(0n, a)` reduces to `a`. With the helper, the law is

    x*((-1)*y) = (x*(-1))*y = ((-1)*x)*y = (-1)*(x*y)

-- `Rat.mul_assoc.arb` read backwards, one `Rat.mul_comm` under a cong,
`Rat.mul_assoc.arb` again, and the helper read backwards. Five steps, no value
law, no cross sum, no div/gcd spelling, no Int or Nat arithmetic.

**So the law's *statement* changed, and that is the honest part of the round.**
`Rat.mul_assoc.arb` is conditional at arbitrary values, so this route proves
`mul_neg` only under the positivity of `x`'s and `y`'s denominators; the
previous round had stated it unconditionally ("for *every* pair of Rats", with a
comment claiming the Int laws identify the two raw numerators, which is the
observation above that the checker cannot use). The statement now carries the
two positivity hypotheses -- the same rung-2 hypothesis pair every other
arbitrary-value law in the file carries, and the same one the QExt layer already
states about its coefficients -- and the comment says why. One junk instance was
evaluated by hand (`x = Rat{Int{1,0},0}`) and both sides agree there, so the
unconditional form is not *known* to be false; it is simply not reachable by this
route, and the value machinery that could reach it is the route the previous
round was already stuck on.

**`Rat.add_neg` was restated too, and for a harder reason: the canonical form
the previous round wrote was unusable downstream.** It was stated as
`Rat.add(Rat{Rat.num(np,nn), 1n+dp}, Rat.neg(...)) == Rat.zero()` with
`gcd(mag(np,nn), 1n+dp) = 1` as a hypothesis. But the rationalization needs this
law at `Rat.mul(xa, xb)` -- an mk-headed product, not a canonical
`Rat{Rat.num(np,nn), 1n+dp}` -- so the canonical statement cannot be instantiated
where it is needed, and coprimality of a product is not something a caller can
have. The law is now `for +x: Rat, for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{}}`,
and the coprime hypothesis turned out to be unnecessary: with the *raw*
coordinates in hand, the closing is pure Nat truncation arithmetic.

The fill is the one the previous round's comment predicted, in the order it
predicted (`Rat.mul_comm` to put the mk-headed summand in the slot the mixed
value law takes, then `Rat.mk.rep` to re-spell the raw numerator `Int{xnn,xp}` as
the truncation pair `Rat.num(xnn,xp)`), and everything after
`Rat.add.value.mixed` is the diagonal:

    C1 = (Sb*xd + Sa*0) + (xp*xd + xnn*0)
    C2 = (Sb*0 + Sa*xd) + (xp*0 + xnn*xd)          Sb = xnn - xp,  Sa = xp - xnn

Five Nat steps per coordinate (four congs -- two `mul_zero`, two `add_zero` --
around `Nat.mul_add_left` read backwards) bring both to
`mul(add(Sb,xp), xd)` and `mul(add(Sa,xnn), xd)`, and `Nat.sub_cross` at
`cmp(xnn,xp)` says the two inner sums are equal, so `Equal.cong` under `mul(.,xd)`
closes it. Then `Rat.mk.diag(C1, xd*xd, Nat.mul_pos)` is the whole denominator
side. No value equation, no cross sum, no coprimality, no case analysis.

**One call-site spelling, measured once.** `Rat.add.value.mixed`'s `pq`
hypothesis is the positivity of `Rat.denof(Rat.mk(Rat.num(np1,nn1), d))`, and
that gcd is over the *truncation pair's* coordinates:
`Rat.g(Nat.sub(np1,nn1), Nat.sub(nn1,np1), d)`, not `Rat.g(np1,nn1,d)`. Passing
the raw-pair spelling fails with the expected/observed pair naming both gcds
(`add(sub(sub(xnn,xp),sub(xp,xnn)), sub(sub(xp,xnn),sub(xnn,xp)))` against
`add(sub(xnn,xp),sub(xp,xnn))`), because `Rat.mk` destructures what it is handed
and `Rat.num` is already the difference pair. This is the same second-destructuring
fact the `den.pos` fills record, at a call site rather than in a helper.

**What the three laws are for.** `Rat.mul_neg` (at `xa,xb`), `Rat.mul_neg` again
(at `xb,xb` and at `D, mul(xb,xb)`) and `Rat.add_neg` (at `mul(xa,xb)`) are
exactly the Rat-level facts of the division-free rationalization
`x * conj(x) = a^2 - b^2 d`: the imaginary coordinate
`xa*(-xb) + xb*xa` is `-u + u = 0` at `u = xa*xb`, and the real coordinate needs
`xb*(-xb) = -(xb*xb)` and then `D*(-(xb*xb)) = -(D*(xb*xb))`. The QExt side
(`QExt.conj`, `QExt.norm` and the law itself) is the next unit; the literal
division form additionally needs a `Rat` inverse operation with its own laws,
which is still open.

## The division-free rationalization landed (measured)

`QExt.conj`, `QExt.norm` and `QExt.mul_conj` are in `qrat.bend`, filled in
`qrat_proofs.bend`. Counts: rat 208 (unchanged), qrat 215 -> 216. Six gates
green.

**The law is four Rat laws wide, and all four are from the negation block.**
With the coefficients destructured as `QExt{xa,xb}`, `QExt.mul(d, x,
QExt.conj(x))` unfolds to `QExt{xa*xa + D*(xb*(-xb)), xa*(-xb) + xb*xa}` with
`D = QExt.nat(d)` (a stuck term is enough: `QExt.mul` destructures its third
argument, which `QExt{xa, Rat.neg(xb)}` still is -- the negative is only stuck
*inside* a field). The real coordinate is then

    xa*xa + D*(xb*(-xb))  =  xa*xa + D*(-(xb*xb))     Rat.mul_neg(xb,xb)
                          =  xa*xa + (-(D*(xb*xb)))    Rat.mul_neg(D, xb*xb)
                          =  Rat.sub(xa*xa, D*(xb*xb)) {==}

and the imaginary one

    xa*(-xb) + xb*xa  =  (-(xa*xb)) + xb*xa           Rat.mul_neg(xa,xb)
                      =  (-(xa*xb)) + xa*xb           Rat.mul_comm(xb,xa)
                      =  u + (-u)                     Rat.add_comm
                      =  0                            Rat.add_neg(u)

-- i.e. no distributivity, no associativity, no value law and no cross sum
anywhere: the rationalization is exactly the two negation laws applied to the
conjugate pair. Both coordinates need a positivity fact that is not a
hypothesis, and `Rat.mul.den.pos` is what supplies it (`mul(xb,xb)` in the real
chain and the mixed law's product `mul(D, E)`, `mul(xa,xb)` for `Rat.add_neg`);
`QExt.nat(d)`'s own denominator is 1, so `{==}` discharges that slot.

**A new checker fact, measured on the first attempt.** A *def* whose body reads
the same argument twice has to declare that parameter `+`: `QExt.conj(x)` (which
calls `QExt.re(x)` and `QExt.im(x)`) and `QExt.norm(d,x)` (four reads) both
failed with `expected : x / observed : x (consumed more than once)` until the
parameter was written `+x`. Law fills inherit their linearity from the law, so
this only shows up on new helper defs -- `QExt.re`/`QExt.im` were already
`(+a, +b)` for the same reason.

**The QExt assembly is the same three-endpoint trans as every other QExt law**
(`qext.re` then `qext.im`), so the fill is two coordinate chains plus two lines
of gluing. The statement's right side is `QExt{QExt.norm(d,x), Rat.zero()}` and
the fill's is the same term with `Rat.sub` unfolded -- the def is transparent, so
the two spellings are one conversion apart.

**What is still open on this route.** `1/(a + b*sqrt d) = conj(x)/norm(d,x)`
needs a `Rat` inverse: the operation, its laws, and the `Rat` division that
consumes it. That is the field-axioms-and-inverse unit the README already names,
and nothing in this round shortens it.

## The inverse unit, round one: the operation and the two orientation rules

`Rat.inv` and `Rat.div` are in (commit `bbbef5f`), the GT branch of
`Rat.mul_inv` is stated and its arithmetic is in place -- `Rat.mul.num.coords`,
`Rat.mul.mag.coords`, `Rat.mul_inv.gt.pw`, `Rat.mul_inv.gt.divself`,
`Rat.mul_inv.gt.hT`, `Rat.mul_inv.gt.chain` all check -- and the one step still
red is `Rat.mul_inv.gt.gT`, which is `gcd(T, T) = T`. Everything below was
measured, not reasoned about; two of the statements contradict the earlier
notes in this file, so they are worth folding back into the gotchas.

**`Equal.sym(A, a, b, e)` for `e : {a == b}` gives `{a == b}`** -- it does *not*
flip. `Equal.sym(Nat, p, Nat.mul(p, 1n), N.mul_one(p))` is `{p == Nat.mul(p,1n)}`,
the same as its argument, and swapping `a` and `b` gives the other direction.
The `%`-ascription convention is likewise the reverse of what earlier rounds
recorded: `%e : {_ == a : A}` rewrites occurrences of `a` (the LHS inside the
ascription) with `b`, so a rewrite fires *left-to-right* by its own statement.

**`Equal.cong(f, a, b, e)` for `e : {a == b}` gives `f(b) == f(a)`.** Measured
twice: with `f = u => Nat.add(p, u)`, `a = p*dp`, `b = dp*p` and
`Nat.mul_comm(p,dp) : {a == b}`, the result is `add(p, dp*p) == add(p, p*dp)`.
This is the orientation the fills have to be written in, and it is why the
`cong` at a goal whose arguments are *not* abstract variables wants its evidence
oriented the other way round.

**`Nat.mul_one` in this repo is stated flipped.** `nat.bend` has
`law mul_one: {a == Nat.mul(a, 1n)}` with an explicit note that it is stated
flipped so rewrites fire left-to-right. A fill that wants `mul(a,1n) == a` has
to build it, and one that wants `a == mul(a,1n)` takes the law as it is.

**`Nat.div` and `Nat.gcd` arguments cannot be reached by a `%` rewrite at all.**
Both are defs whose bodies call `.fin`/`.go`, so a goal's occurrence shows up as
`div.fin(divmod(..))` or `gcd.go(..)` while the rewrite's pattern is the
abbreviated call -- the matcher has nothing to match on. `Nat.mul` arguments are
worse than that: they sometimes reduce and sometimes do not, depending on how
much of the surrounding context is already constructor-headed, so a proof that
leans on that reduction at one site and not another is fragile. The reliable
route is `Equal.cong` at each position, with the two orientations above, and
`Equal.trans` with the middle endpoint spelled exactly as the first half's
result rather than as something merely equal to it.

**What is left for `Rat.mul_inv.gt`.** `gT` is the only red step: with
`hT : {T == Nat.add(Nat.mul(p,1n), Nat.mul(p,dp))}`, the goal is
`gcd(T,T) = T`, and the pieces are `mul_one` to put both arguments at `T*1`,
`hT` to turn the second into `mul(p*1 + p*dp, 1)`, `Nat.mul_comm(1n+dp,p)` to
order that one as `mul(p, 1n+dp)`, the outer `gcd_scale` to factor out `p`, and
the inner `gcd(d',d') = d'` from `gcd_scale` at `k = 0`. Each of those five
steps is a three-line `Equal.trans` once the orientations above are applied;
what is red is the composition, not the arithmetic. The `T = mul(1n+dp, p)`
call site is where the two spellings of the argument (`mul(T,1n)` and
`1n + add(dp,0)`) have to be reconciled, which is the last `cong` in the chain.

**The LT branch and `Rat.div_mul_cancel` are untouched.** `Rat.mul_inv.lt` is
stated (with the hypothesis `{LT{} == Nat.cmp(np,nn)}`, the orientation
`Rat.inv` consumes) and has no fill; `rat.bend` reports 210 TODOs, i.e. the two
branch laws and nothing else.

**Gate state at the end of this round: red, by design of the checkpoint.** The
two branch laws `Rat.mul_inv.gt` and `Rat.mul_inv.lt` are *stated* in `rat.bend`
and their fills are not in `rat_proofs.bend` -- the GT fill is parked in
`wip-inv.bend`, which nothing imports, because a red fill takes every gate down
with it. So the counts are now nat 127, int 32, qext 34, **rat 210**, **qrat
218**, and the five proofs files plus `scratch.bend` fail with
`Error: 2 TODOs found.` (the two stated laws) until the fills land. The counts
before this round were rat 208 / qrat 216, and the earlier note in this file
that says "208" belongs to that state.

**What is measured and what is not.** In `wip-inv.bend`: `Rat.mul.num.coords`,
`Rat.mul.mag.coords`, `Rat.mul_inv.gt.pw`, `Rat.mul_inv.gt.divself`,
`Rat.mul_inv.gt.hT` and `Rat.mul_inv.gt.chain` all check; `Rat.mul_inv.gt.gT`
does not, and it is the only red def in the file. The LT branch has no fill at
all. To go back to a green tree without finishing the law, delete the two `law
Rat.mul_inv.*` blocks from `rat.bend`; the defs from `bbbef5f` are independent.

### The rewrite and orientation rules, measured (supersedes the earlier notes)

Four rules, each measured directly in this repo with a two-line probe rather
than read off a proof; the earlier gotchas in this file state two of them the
other way round, which cost several failed rounds.

- **`%e : P` rewrites left-to-right by `e`'s statement.** With
  `e : {a == b}`, a goal containing `a` becomes the goal with `a` replaced by
  `b`. The `_` in an ascription such as `%e : {_ == a : A}` is the *occurrence*
  side, not a wildcard for the produced type: `{_ == a}` marks the position the
  matcher searches, and the replacement is `e`'s other side. So the spelling
  `%e : {_ == Nat.div(T, T) : Nat}` is what you want when the goal's occurrence
  is `Nat.div(T,T)` and `e` says `div(T,T) == q`.
- **`Equal.sym(A, a, b, e)` returns `{a == b}`** for `e : {a == b}` -- it does
  not flip. To flip, swap the two middle arguments:
  `Equal.sym(A, b, a, e) : {b == a}`. A probe confirms both directions; the
  consequence is that a `sym` whose result is not used in the same orientation
  as its argument's statement is a no-op on the type.
- **`Equal.cong(f, a, b, e)` for `e : {a == b}` returns `f(b) == f(a)`.** With
  `f = u => Nat.add(p, u)`, `a = Nat.mul(p,dp)`, `b = Nat.mul(dp,p)` and
  `Nat.mul_comm(p,dp) : {a == b}`, the result is
  `add(p, dp*p) == add(p, p*dp)`. The `a` and `b` arguments are *the endpoints*
  -- passing them in the order you want the equation is what produces the
  reversed equation, which is where most of the failed rounds went.
- **`Nat.mul_one` is stated flipped**: `nat.bend` has
  `law mul_one: {a == Nat.mul(a, 1n)}` with a note that this is deliberate so
  rewrites fire left-to-right. A fill wanting `mul(a,1n) == a` has to flip it.

Two structural facts that decide what is even writable:

- **A `%` rewrite cannot reach an argument of a def whose body is a nested
  call.** The goal's `Nat.div(a,b)` shows up to the matcher as
  `Nat.div.fin(Nat.divmod(a,b))` and the goal's `Nat.gcd(a,b)` as
  `Nat.gcd.go(...)`, while a lemma's statement is the abbreviated call; the
  matcher has nothing to match on. Reach those positions with `Equal.cong` at
  that exact position instead. `Nat.mul` arguments are worse: they reduce or do
  not depending on how constructor-headed the rest of the context already is,
  so a fill that relies on that reduction at one site and not at another is
  fragile, and the fix is to write the lemma's own spelling out.
- **`Nat.gcd_scale` is stated at `gcd(mul(m, 1+kp), mul(d, 1+kp))`**, not at
  `gcd(m, d)` -- a caller whose gcd argument is `t` has to write `t` as
  `mul(t, 1n)` first (`Nat.mul_one` flipped), and the endpoints of that rewrite
  are the *go-form* of the gcd, so `{==}` opens the chain and the stated type is
  reachable only through the abbreviation. This is where `Rat.mul_inv.gt.gT`
  stood red until round two, where a Nat-level law replaced the in-file
  reconstruction.

## The inverse unit, round two: gcd_self as a law, and a false statement under the first red (measured)

Round one ended by saying that everything in `wip-inv.bend` except `gT` checks.
That was read off "the first error is in `gT`", and the checker reports only the
first error in file order -- so it was an inference, not a measurement. Carrying
out the `gT` recipe with a Nat-level law instead of the in-file reconstruction
removed that error, and the defs underneath it were not in the state the
inference described.

**`Nat.gcd_self` is a law now, and it is what `gT` needed.** `nat.bend` carries

    law gcd_self:
      for +a: Nat
      {Nat.gcd(a, a) == a : Nat}

filled in `nat_proofs.bend`: `match a`, `0n` is `{==}`, and the successor case is
two lines -- `%NL.add_zero(1n+ap) : {NL.Nat.gcd(_, _) == _ : Nat}` and then
`NL.gcd_scale(1n, 1n, ap)`. One `gcd_scale`, not two: `Nat.mul(1n, 1n+ap)`
reduces to `Nat.add(1n+ap, 0n)`, which is the `mul(m, 1+kp)` spelling
`gcd_scale` is stated at, and `Nat.gcd(1n, 1n)` reduces to `1n` on its own, so
that instance's statement *is* the case goal. The law's `for +a` is also what
lets the bare-name fill read `ap` twice: a linear `def g(a)` fails with
"ap (consumed more than once)".

The generality is the whole reason the law exists. At the *variable* `p` the
in-file version was stuck -- `Nat.cmp(p, p)` is stuck, so the loop cannot start
-- and a lemma stated at `1n+dp` is a different, non-convertible type. Measured
as the error it produced: `Nat.gcd(p, p) == p` expected against
`Nat.gcd.go(1n+Nat.add(p, 1n+p), 1n+p, Nat.cmp(p, p), 1n+p) == 1n+p` observed.
`Rat.mul_inv.gt.gself` is gone from `wip-inv.bend`; `gT` reaches `Nat.gcd_self(p)`
through one `Equal.cong` over `u => Nat.mul(u, 1n+dp)` and checks.

Counts after the law: nat 127 -> **128**, rat 210 -> **211**, qrat 218 -> **219**
(int 32, qext 34 unchanged), all six gates in their expected states.

**`Rat.inv`'s LT and GT branches dropped `d`, so both laws were false as
stated.** Both branches spelled the numerator out of `np`/`nn` --
`Rat{Rat.num(np, nn), Nat.sub(np, nn)}` on GT, the mirror on LT -- where the
reciprocal needs `d` in that slot: the branch's own comment says the result is
`d/(np-nn)`, "the pair `(d, |np - nn|)` is already reduced", and the header of
`wip-inv.bend` assumes exactly that shape (`Int{p*d', 0}` over `d'*p`). As
committed, `Rat.inv` returned the *value* 1 for every non-zero input. Measured
with the law's instance as a `{==}` goal: GT at np=5, nn=3, dp=0 gives
`Rat{Int{2n,0n}, 1n}` expected against `Rat{Int{1n,0n}, 1n}` observed (2 = 1);
LT at np=3, nn=5, dp=0 gives `Rat{Int{0n,2n}, 1n}` against `Rat{Int{1n,0n}, 1n}`
(-2 = 1). Fixed to `Rat{Rat.num(d, 0n), Nat.sub(np, nn)}` (GT) and
`Rat{Rat.num(0n, d), Nat.sub(nn, np)}` (LT); the same three instances then check
by `{==}` alone (np=5, nn=3 at dp=0 and dp=2; np=3, nn=5 at dp=0), including
`Rat.num(1n + 2n, 0n)` -- the `sub` terms inside `Rat.num` reduce on their own at
a successor `d`. All six gates are unchanged by the fix, and inside `src/` the
only caller is `Rat.div`.

**What the tail of `wip-inv.bend` actually is.** With `gT` green the first error
is `chain`, and it is a statement error: `Rat.mul_inv.gt.chain` states
`R.Rat{R.Rat.num(T, T), Nat.div(T, T)} == R.Rat.one()`, whose left endpoint
reduces to `R.Rat{Int{0n,0n}, Nat.div(T,T)}` -- the diagonal pair is zero, so the
goal asserts 0 = 1. `Rat.num(T, T)` is not the product's numerator at that
position; the mk-output shape is `Int{T, 0}`, with `T = d'*p` in the first slot
and the two `div(T, T)`s still to be carried to 1. `coords` fails for two further
reasons: it calls `Rat.mul.num.coords` and `Rat.mul.mag.coords`, neither of which
is defined here or in `src/` (measured: "expected: a defined name / observed:
Rat.mul.num.coords") -- the comments at the top of the file about "the two halves
of the pair gcd_divides returns" and "the two div coordinates of the GT branch"
are what is left of them; and every `%` pattern in it carries more than one `_`,
which cannot work, because `bend.ts` types the pattern under a `Lone()` binder
(the two-hole `{Nat.gcd(_, _) == 1n+dp}` of the erased `gself` was accepted
precisely because both holes are the *same* term). Its call
`%Rat.mul_inv.gt.gT(T, {==}, p, dp)` also contradicts `gT`'s telescope
`(T, p, dp, hT)`, and `{==}` cannot be that `hT` anyway: `T` is the let
`Nat.mul(1n+dp, p)` and `Nat.mul(p, 1n+dp)` is `Rat.mul_inv.gt.hT`'s job, not a
conversion.

So the state is: `pw`, `divself`, `hT`, `gT` check; `chain`'s statement has to
be restated on the product's real numerator before its body means anything; the
two coord helpers have to be written again; `coords`' rewrite steps have to be
one hole each.

*Round three supersedes that paragraph: both branches landed, and the closing
turn out not to need the coord helpers as separate defs at all.*

## The inverse unit, round three: both branches landed, and the LT half is a mirror image (measured)

`Rat.mul_inv.gt` and `Rat.mul_inv.lt` are proved. `src/rat_proofs.bend` checks
-- `All terms check.`, not a TODO count -- and so does `src/qrat_proofs.bend`,
whose 2 TODOs were exactly these two laws. All five `*_proofs.bend` files are
green, and the tree now has no unfilled law. The workbench `wip-inv.bend` is
gone: its content is the ported block, and keeping the file would have been a
second definition of `R.Rat.mul_inv.gt`.

**What round two's ending got right, and what it guessed wrong.** `chain`'s
statement *was* wrong (it asserted 0 = 1) and it *was* restated -- but not on
the clean `Int{T, 0}` the paragraph above guessed. `Rat.mul` expands to
`Int.mul(Rat.num(np, nn), Int{1n+dp, 0n})` before `Rat.mk` normalizes, and
`Int.mul` is a four-product sum, so what the checker shows is

    ca = mul(np-nn, 1n+dp) + mul(nn-np, 0n)     cb = mul(np-nn, 0n) + mul(nn-np, 1n+dp)

with mk's denominator argument `add(np-nn, mul(dp, np-nn))`. The probe that
printed it is the technique that made this round mechanical: a `{==}` at the
*law's own instance*, which forces the checker to print both endpoints in SNF.
Measured that way, `chain` is

    def Rat.mul_inv.chain(+T: Nat, +pT: {Nat.cmp(0n, T) == LT{} : Cmp})
      -> {R.Rat{I.Int{Nat.div(T, T), Nat.div(0n, T)}, Nat.div(T, T)}
          == R.Rat.one() : R.Rat}

and its body is three `Equal.cong` steps -- `divself`, then `div_zero`, then
`divself` again -- with no `Nat.divides` witness and no destructure of the pair
`gcd_divides` returns. The old route took `Pair.fst(N.gcd_divides(T, T))`
because an anonymous pair cannot be destructured by its caller; `div_self`
reaches `div(T, T) = 1` at the opaque dividend the goal has, so that witness was
never needed for this.

**The Nat algebra under the coordinates.** With `s = sub(np, nn)`,
`t = sub(nn, np)`, the two raw coordinates and their difference reduce to `T`
and `0` (`coordA`/`coordB`, then `subAB`/`subBA`), the magnitude to `mul(T, 1)`
(`magT`), and the divisor `gcd(mag, add(s, mul(dp, s)))` to `T` (`gcdT`) -- which
is `gT` at `T := mul(1n+dp, s)`, `p := s`. The coordinates are then
`div(T,T)`, `div(0,T)`, `div(T,T)`: `chain`'s goal. The branch hypothesis is
consumed exactly once, in `coordB` (`np > nn` means `nn-np` is zero, through
`sub_of_lt` at `cmp(nn, np) = LT`); by the time the coordinates are stated, it
has been spent.

**The LT branch is the GT branch with the two raw products swapped -- measured
before a line was written.** The probe on the LT law's instance printed
`A_lt = add(mul(s, 0n), mul(t, 1n+dp))`, `B_lt = add(mul(s, 1n+dp), mul(t, 0n))`
and `D_lt = add(t, mul(dp, t))`: the same terms as GT with `A`/`B` exchanged and
`s` replaced by `t` in `D`. So `lt.coordA`/`lt.coordB`/`lt.subAB`/`lt.subBA`/
`lt.magT`/`lt.gcdT` are mirror statements, `lt.pb` flips the hypothesis with
`cmp_gt_of_lt` before `sub_pos`, and `lt.coords` is `gt.coords` with the
spellings substituted. Nothing structural differs; both branches close on the
same `chain`.

**Two rules this round paid for, both about spelling at a variable.**

- The one design that failed: a branch-agnostic wrapper
  `pos_mul(a, b, pb) -> {cmp(0n, mul(a, b)) == LT{}}` calling
  `N.mul_pos(a, b, {==}, pb)` is rejected -- `expected : Nat.cmp(0n, a)` against
  `observed : LT{}` -- because `Nat.cmp(0n, a)` is stuck at a variable, so
  `{==}` can only discharge `mul_pos`'s first-factor evidence when that factor
  is *literally* a successor. This is the `Nat.gcd_self` lesson one level down:
  a law stated at a variable cannot be reached by a proof step that only runs at
  a constructor. The fix is a per-branch `pb` plus the direct
  `N.mul_pos(1n+dp, q, {==}, pb)` at the call site, where the term is a
  successor.
- The `%` patterns. Every rewrite in `coords` is written **one hole per step**,
  with the other slots spelled at the goal's own SNF terms -- that is what the
  probe is for: the second numerator slot has to be written
  `Nat.div(Nat.sub(B, A), G)`, not `Nat.div(B, G)`. Round two's claim that a
  multi-hole pattern cannot be accepted stays untested in the direction that
  matters, because this round never needed one: a *distinct-term* multi-hole
  pattern is still an open question, and the working rule is the measured one --
  one hole per rewrite, everything else spelled exactly as the checker prints
  it.

**Naming.** `pw`, `divself`, `hT`, `gT` and `chain` lost the `gt.` prefix once
LT needed them (`Rat.mul_inv.pw` and so on); the coordinate helpers keep their
`gt.`/`lt.` prefixes, because those statements are branch-specific. `gt.pT`
split into `gt.pb`/`lt.pb` plus the direct `mul_pos` call above.

**Technique that carried the round.** The deliberately-false `{==}` at a law's
own instance, run *before* writing any proof: one run pinned the GT SNF and one
pinned the LT shapes, after which the whole LT half was written by substitution
rather than by derivation. One probe per run -- the checker stops at the first
error. `probe.bend` holds the last probe; `scratch.bend` prints the fixed
`Rat.inv` triple, `(Rat{Int{7,0}, 2n}, Rat{Int{0,7}, 2n}, Rat{Int{0,0}, 0n})`
at `(5,3,7)`/`(3,5,7)`/`(3,3,7)` -- `7/2`, `-7/2`, and the `EQ` branch's zero
numerator over `sub(np, nn)`, which is 0 at that branch. That third component is
what a zero input can get: no law is stated for `np = nn`, and the two laws are
`gt` and `lt` only.

**Left on this side of the layer.** The inverse *operation* and its two laws
are in. The division laws (`Rat.div`'s value form, and the field axioms stated
over `div`) are the next unit on the Rat side, and `QExt`'s
`1/(a + b*sqrt d) = conj(x)/norm(d,x)` is now one `Rat.div` call away.

## The division laws landed: the sign goes in the spelling, and the branch-free statement is out of reach (measured)

Ten laws of `Rat.div` are stated and proved, all five `*_proofs.bend` gates are
green, and the counts are rat.bend 221 = 128 Nat + 32 Int + 61 Rat, qrat.bend
229 (it imports rat.bend, so it moved with it). The new laws are
`Rat.div.value.gt`/`.lt`/`.eq` (the value form, one per branch of `Rat.inv`'s
split), `Rat.div_self.gt`/`.lt`, `Rat.div_one`, `Rat.div_mul_cancel.gt`/`.lt`
(`(x/y)*y = x`) and `Rat.div_add.gt`/`.lt` (`(x+y)/z = x/z + y/z`).

**The design decision, and the wall behind it.** `Rat.div(a, b)` is
`Rat.mul(a, Rat.inv(bp, bnn, bd, Nat.cmp(bp, bnn), {==}))`. At a *variable*
divisor that fifth argument is stuck, and it is stuck in the worst place: inside
`Rat.inv`'s argument list, next to the `{==}` whose type mentions it. A `%` step
cannot reach it. The pattern would have to rebuild that argument list, and the
obligation it must satisfy is the type `{x == Nat.cmp(bp,bnn)}` that `Rat.inv`
puts on its evidence slot, while a pattern's own evidence binder has type
`{GT{} == x}` -- the opposite orientation, hole on the opposite side. A derived
term -- `Equal.trans(Cmp, _, GT{}, Nat.cmp(bp,bnn), Equal.sym(Cmp, GT{}, _, e), e)`
-- does typecheck *inside* the pattern, and then dies one check later: `Rwt`'s
fit compares the evidence terms (or at least refuses a trans chain against
`{==}`), so `expected` prints the goal with `{==}` where `observed` has the
chain. Three probes, one run each; the fit is the third throw in check-rwt and
its message names the `%` span, which is how the two were told apart. So a law
*stated* with a chain-spelled instance is not the answer either: a goal that
contains `Rat.div` SNFs to the `{==}` spelling, and no equation between the two
spellings can be built.

**Therefore the sign goes in the spelling.** A positive divisor is written
`Rat{Rat.num(1n+ap, 0n), 1n+dp}` (numerator coordinates `1+ap` against `0n`), a
negative one `Rat{Rat.num(0n, 1n+bp), 1n+dp}`, and the zero divisor
`Rat{Rat.num(0n, 0n), 1n+dp}`. `Nat.cmp` then computes on constructors, `Rat.inv`
matches, and all of `Rat.div` reduces to a product by the reciprocal -- with no
rewrite at all, which is why the fills are as short as they are: the three value
laws are `{==}`, `div_self.*` is one `Rat.mul_inv` call each, `div_one` is
`Rat.mul_one`, `div_add.*` is one `Rat.mul_add_left.arb`, and only the field
axiom needs a chain (associativity, then the reciprocal pair under a `cong`,
then `mul_one`). The spelling *is* the branch evidence, exactly as in
`Rat.mul_inv` -- which is also why the branches are separate laws and no law
carries a `c != EQ` side condition.

**The one trap in the mirror.** For a negative divisor the reciprocal is
`Rat{Rat.num(0n, 1n+dp), 1n+bp}`, not `Rat{Rat.num(1n+dp, 0n), 1n+bp}` -- it is
negative too. Copying the GT spelling into the LT chain (the natural error, since
only the first coordinate of `Rat.num` differs) fails with the mismatch reported
on the *first factor of the goal's product*, not on the reciprocal:
`expected : Rat.mul(Rat.mk(Int.mul(n, Int{0n, 1n+dp}), Nat.mul(d, 1n+bp)), ..)`
against the same term with `Int{1n+dp, 0n}`. The value laws had the sign right
and the mirror did not, which is the argument for probing *both* branches with a
`{==}` value form before writing either chain.

**`x / 0` is zero, but it is not the term `Rat.zero()` -- measured.**
`Rat.div.value.eq` was written last, on the guess that the EQ branch behaves like
the other two. It does -- the comparison computes and `{==}` closes it -- but
what it says is worth recording: `x / 0` reduces to
`Rat.mk(Int.mul(xn, Rat.num(0n, 0n)), Nat.mul(D, 0n))`, the value zero in the
degenerate spelling `Rat{Int{0,0}, 0n}`, whose denominator is 0. It is not
`Rat.zero()` (= `Rat{Int{0,0}, 1n}`), and no structural `x/0 = 0` law can exist:
`{Rat.div(Rat{n, 1n+dp}, Rat.zero()) == Rat.zero()}` was run as a deliberately
false def and failed with `expected : Rat.mk(Int.mul(n, Int{0,0}),
Nat.mul(dp, 0n))` against `observed : Rat{Int{0,0}, 1n}`. A caller who wants the
constructor has to go through the value laws (`Rat.mk.eqv`), not through `{==}`.

**The laws are usable, and that was checked rather than assumed.** `probe.bend`
is now a consumer file: it imports `rat.bend` and `rat_proofs.bend`, states each
of the ten laws from the caller's side, and applies them by name -- including at
literals, which is the only way to see that the implicit arguments really are
inferable, and at variables with the branch facts as hypotheses, which is the
realistic case. It also derives a fact that is not one of the ten,

    (x + y) / 1 = x + y

by `Rat.div_add.gt` at `ap = dp = 0n` followed by two `Rat.div_one` under
congruences. The first step is the interesting one: it reaches a goal stated
with `Rat.one()` only because `Rat{Rat.num(1n+0n, 0n), 1n+0n}` is convertible to
`Rat.one()`, i.e. a law stated at the spelled-out divisor does apply to a goal
stated with the constructor. Every consumer of this block depends on that.

**What is still out of reach, and the alternative that was dropped.** There is
no branch-free law at a variable divisor: `Rat.div(x, Rat{Rat.num(np,nn),
1n+dp})` does not reduce, and the evidence wall says no rewrite opens it. A
consumer with a symbolic divisor must carry the branch as a hypothesis and use
the branch law -- the discipline `Rat.mul_inv` already imposes. The alternative
considered and dropped was to delete `Rat.inv`'s `+e` parameter, so that
`Rat.div`'s body would contain no `{==}` to compare against. It is not needed
for these ten laws, and it would not buy a variable-divisor law anyway: the
`Nat.cmp(bp,bnn)` handed to `Rat.inv` as its `c` argument is still stuck at a
variable, so `Rat.inv`'s own `match c` still cannot fire. The wall is the
comparison, not the evidence.

**Two corrections to round three's record.** Its closing paragraph says "no law
is stated for `np = nn`, and the two laws are `gt` and `lt` only" -- true of the
inverse then, and no longer true of `div`, which now has `Rat.div.value.eq`. And
its "left on this side" list carries the `Rat.inv` signature edit as the route to
a variable-divisor law; the measurements above say the sign-in-the-spelling route
is the one that works and the signature is untouched.

## The QExt division payoff landed, and the norm is not positive (measured)

The unit round four pointed at was one law: for `x = a + b*sqrt d`,

    x * (conj(x) / norm(d, x)) = 1

-- the rationalization, the reason the whole division block exists. It is now
`QExt.inv.value.gt` in `src/qrat.bend`, filled by three defs in
`src/qrat_proofs.bend`.

**Two Rat laws had to come first, and both are denominator-level.** The payoff's
rearrangements carry negations of the *coefficients* through products, so they
need the positivity of a negated denominator, `Nat.cmp(0n, denof(neg x)) == LT{}`
-- the missing third member of the `mk.den.pos` / `mul.den.pos` / `add.den.pos`
family, added as `Rat.neg.den.pos`. It is a law rather than a bridge for the
reason the family is: `Rat.neg` destructures before calling `Rat.mk`, so at a
variable the term is stuck and no congruence or `mk`-headed positivity law
reaches it. And the payoffs need negation on the *left* of a product,
`(-x)*y = -(x*y)`; `Rat.mul_neg` cannot be turned around, because its negation is
in the second factor -- so `Rat.neg_mul` was added (three steps: `mul_comm`, the
inner `mul_neg`, and a `cong` under `neg` with `mul_comm` again). The payoff uses
it three times.

**One language fact, found by failing.** A `let` cannot hold a bare constructor:

    +rh = R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap}

is rejected with `expected : an annotated term (cannot infer)` and the
constructor's type in `observed` -- with no expected type, the checker cannot
infer which type the constructor builds. `let`s whose right-hand side is a *def*
call are fine, because a def has a known result type, and that asymmetry is the
whole reason `Rat.of` exists in `src/rat.bend`:

    def Rat.of(+np: Nat, +nn: Nat, +dp: Nat) -> Rat:
      Rat{Rat.num(np, nn), 1n+dp}

a plain abbreviation like `QExt.of`, nothing normalized, no match on its
arguments. With it every `let` in the fill names its divisor once.

**The law's design is round four's design.** The divisor's sign is in the
*spelling*: the norm is written as the positive raw pair `(1+ap)/(1+dp)` and a
hypothesis `hZ` says that rational *is* `QExt.norm(d,x)`. This is what buys the
fill: `Rat.div(x, spelled)` reduces by conversion to `mul(x, reciprocal)` at a
*variable* dividend -- no law, no rewrite. Measured before the fill was written,
by a `{==}` against that goal at variables; `probe.payoff.bend` keeps it as the
first of its three defs.

**The fill.** Two coordinate defs plus the composing chain.
`QExt.inv.value.gt.re` is stated in the *unfolded* shape -- the goal after the
`Rat.div`s have become products by the reciprocal -- and is a rearrangement:
associativity twice (read backwards), `mul_neg`, then a three-`Equal.trans`
chain that pulls `D*(neg BB*rh)` to `neg(PP)*rh` via `neg_mul`, `mul_neg` and an
associativity under a `neg` congruence, `mul_add_left` backwards to re-fold the
sum, `{==}` twice to cross the `sub`/`add-neg` and `norm` spellings, a `cong`
with `sym(hZ)` to re-spell the norm as the literal pair, and `Rat.mul_inv.gt` at
`(1+ap, 0n, dp)` to close. `QExt.inv.value.gt.im` is the mirror and cancels
without needing `hZ` at all (`add_comm`, `add_neg`). The composing def matches
`x` into `(xa, xb)` and then

    trans(QExt{Lr,Li}, QExt{one,Li}, QExt{one,zero})

-- the `re` step at the first coordinate only, the `im` step at the second. The
first version tried to go straight to `QExt{one,zero}` and the checker answered
with `expected : QExt{one, zero}` / `observed : QExt{one, Li}`: the intermediate
has to keep the coordinate the current step is not touching, exactly as
`QExt.mul_conj`'s fill does.

**One realization that saved a step.** After `match x`, the law's own
left-hand side -- `QExt.mul(d, x, QExt{div, div})` -- reduces to
`QExt{Lr,Li}` definitionally, so the chain starts at the matched pair with no
`{==}` bridging step.

**Where the statement stops, measured.** An earlier comment in `rat.bend` said
the norm `a^2 - b^2*d` of a non-zero extension is positive, and that the GT
branch is the branch a rationalization caller has already decided. The second
half is false in `d` itself: the norm is indefinite, so an extension like
`1 + 2*sqrt 3`, whose norm is `-11`, has no positive raw pair equal to its norm
-- no `hZ` exists, and no GT law can state that instance. What is measurable is
the product against the *positive* spelling `11`, and it is not 1: deliberately
false `{==}` on the closed product prints

    expected : QExt{Int{0,1}/1, 0}      (i.e. -1 over 1)
    observed : QExt{Int{1,0}/1, 0}      (QExt.one())

so the same product built with `11` multiplies out to **-1**. That is the
boundary of the law, not a presentational choice, and it is why an LT twin of
`QExt.inv.value.gt` is the next unit. Both files' comments were corrected to say
this instead.

**What checks, and the counts.** All five `src/*_proofs.bend` print
`All terms check.`, as do `probe.bend` and the new `probe.payoff.bend`
(which states the conversion, the law from a caller's side at a *variable* `x`,
and the literal `1/(2 + sqrt 2) = (2 - sqrt 2)/2`). Two honest notes about that
probe: at literals the whole product *also* reduces on its own -- measured,
`{==}` closes the instance goal -- so the variable def is what really exercises
the law; and the instance still earns its place as the arithmetic check.
Laws-only counts: nat.bend 128, int.bend 32, qext.bend 34, rat.bend **223**
(128 + 32 + 63 Rat: the two new laws), qrat.bend **232** (rat's 223 + 9 QExt).

## The LT twin of the payoff, and the mirror cost one substitution table (measured)

Round five ended with a measurement and an open unit: the norm of an extension is
*indefinite* in `d`, so `1 + 2*sqrt 3` (norm -11) has no positive raw pair equal
to its norm, no `hZ` exists for the GT law, and forcing the positive spelling 11
makes the same product multiply out to -1. The unit that closes that hole is
`QExt.inv.value.lt`, the payoff stated at round four's *negative* divisor
spelling, and it is now in `src/qrat.bend` with three fills in
`src/qrat_proofs.bend`.

        x^-1 = conj(x)/norm(d,x),     norm(d,x) = a^2 - b^2*d < 0

**The statement.** Same shape as the GT law, with `ap` replaced by `bp` and the
divisor written `Rat{Rat.num(0n, 1n+bp), 1n+dp}` -- the negative spelling, i.e.
`-(1+bp)/(1+dp)` -- and `hZ` saying the norm *is* that rational. `Nat.cmp(0n, 1n+bp)`
computes to `LT{}` on constructors, so `Rat.div` against it reduces by
conversion, exactly as on the GT side. The reciprocal is the thing worth
re-reading round four for: `Rat.inv`'s LT branch is
`Rat{Rat.num(0n, d), Nat.sub(nn, np)}`, so with `np = 0n`, `nn = 1n+bp`,
`d = 1n+dp` the reciprocal is `Rat{Rat.num(0n, 1n+dp), 1n+bp}` -- the *negative*
raw shape, **not** the GT reciprocal `Rat{Rat.num(1n+dp, 0n), 1n+ap}` with a
coordinate flipped. The fill's closing law is `Rat.mul_inv.lt(0n, 1n+bp, dp, {==})`
and it only closes because of that.

**The fills are the GT fills, and the check that they are is the checker.**
Nothing in either coordinate chain is about the sign of the norm: the same
`Rat.neg_mul`, the same backwards `Rat.mul_add_left.arb`, the same congruence
against `hZ`, the same `{==}` denominator witnesses (they only need `rh`'s
denominator to be a successor, and `1n+bp` is one just as `1n+ap` is). So the LT
block was produced from the GT block by a substitution table of eleven literal
strings -- three def names, the `+ap: Nat` parameter, the two `hZ` types, the two
`rh` spellings in the goals, the two `R.Rat.of` lets, and the closing
`Rat.mul_inv.gt(1n+ap, 0n, dp, {==})` -- applied in a script, with an assertion
that every pattern occurred and a scan showing no `ap` left in the block. The GT
half of that script then had to be run *backwards*: the first attempt wrote
`head + header + transformed_block` over the file, which replaced the GT block
instead of following it, and the checker said so immediately -- `Error: 1 TODO
found`, one law short of the 233 in the laws file. Inverting the table restored
the GT block byte-for-byte, and the check that it is byte-for-byte is that the
restored file prints `All terms check.`: a rewrite chain with one wrong
identifier in it does not close. Worth recording as a technique: a mirror that is
*claimed* to be a relabelling can be produced by relabelling, and the checker is
the proof that the claim was right -- but only if the original is kept until it
checks.

**What the pair of laws covers, and what it does not.** Together they cover every
extension whose norm is non-zero, one law per sign. Norm = 0 stays uncovered, and
that is correct rather than an omission: `a^2 = b^2*d` is satisfiable for non-zero
`x` whenever `d` is a square (`x = 2 + sqrt 4 = 4` has norm 0), and an extension
whose norm is zero is a zero divisor -- there is no inverse to state. The
*branch-free* form is still out of reach for the reason round four measured: at a
variable divisor the `Nat.cmp` is stuck inside `Rat.inv`'s argument list next to
the `{==}` whose type mentions it.

**The consumer probe grew both ways.** `probe.payoff.bend` now records the
negative conversion too -- `Rat.div(a, Rat{Rat.num(0n,1n+bp),1n+dp})` unfolds by
conversion to `mul(a, Rat{Rat.num(0n,1n+dp),1n+bp})` at a variable dividend, which
is the fact the `rh` spelling rests on, stated from the caller's side -- plus
`probe.payoff.lt` (the law at a variable `x`, body a call to the published name)
and `probe.payoff.instance.lt`, the literal

    1/(1 + 2*sqrt 3) = (1 - 2*sqrt 3)/(-11)

with every hypothesis `{==}`: the norm computes to -11, which is the spelling at
`bp = 10`, `dp = 0`. That instance is the one the GT law cannot state at all, so
it is also the honest demonstration that the LT twin was needed. As with the GT
instance, at literals the product reduces on its own (`{==}` closes the goal);
what the call adds is that the published name is callable with every implicit
argument inferred.

**Counts.** Laws-only: nat.bend 128, int.bend 32, qext.bend 34, rat.bend 223,
qrat.bend **233** (rat's 223 + 10 QExt -- the LT law is the tenth). All five
`src/*_proofs.bend` print `All terms check.`, as do `probe.bend` and
`probe.payoff.bend`, and `scratch.bend` prints the same `Rat.inv` triple it has
since round three.

## The operations QExt.inv and QExt.div, and the field axiom measured false at non-canonical spellings (measured)

Round six closed the payoff as a *relation*: `x * (conj(x)/norm(d,x)) = 1`, one
law per sign of the norm, with the norm spelled as a raw rational pair of that
sign plus `hZ` saying the norm *is* that rational. Nothing in the tree named an
inverse or a quotient as a `QExt` operation, though, so the pair had no
consumer that could write `1/x` -- it could only write the product the laws are
stated over. This round adds the operations and the two law pairs stated over
them, and measures the boundary of the field axiom.

**The defs** (in `src/qrat.bend`, right after `QExt.norm`):

    QExt.inv(x, q)      = QExt{QExt.re(x)/q, (-QExt.im(x))/q}
    QExt.div(d, x, y, q) = QExt.mul(d, x, QExt.inv(y, q))

`q` is a *parameter*, not `QExt.norm(d,x)` computed in the body. That is forced
by round four's wall, one layer up: `Rat.div` needs a constructor-headed divisor
for the `Nat.cmp` inside `Rat.inv`'s argument list to compute, and
`QExt.norm(d,x)` is an operation's output, so a computed `q` would put the stuck
comparison back where no rewrite reaches it. The caller hands over the norm as a
spelled rational (`R.Rat.of(1n+ap, 0n, dp)` or `R.Rat.of(0n, 1n+bp, dp)`), and
the laws' `hZ` is what says that rational *is* the norm. `QExt.div`'s `q` is
*y's* norm spelling -- round five's note that `QExt.inv`'s body is verbatim the
divisor expression the value laws are stated over now pays off: the operations
apply those laws by conversion alone, with no bridge.

**The linearity lesson, second instance.** The first attempt was
`def QExt.inv(x: QExt, q: R.Rat)` and it died with `expected : q / observed : q
(consumed more than once)`: `q` appears twice in the body, and `x` twice through
`re`/`im`. `+x, +q` is the fix -- the same shape as `Nat.gcd_self`'s `+a`
(round two) and `QExt.neg_neg`'s coefficient hypotheses. Worth stating as a rule
for defs rather than laws: *a parameter used twice in a body must be declared
implicit*, and an operation whose body destructures its argument twice is
automatically in that case.

**`QExt.mul_inv.gt`/`.lt`, and why there is no third law.** Each states
`QExt.mul(d, x, QExt.inv(x, spelled_norm)) = QExt.one()`, with the same `gx`/`hx`
positivity hypotheses as the value laws and the same `hZ`, and each fill is
*one call* to `QExt.inv.value.gt`/`.lt`: `QExt.inv(x, q)` unfolds to the
divisor expression those laws are stated over and `R.Rat.of` unfolds to the
spelled constructor. The pair exists so the operation and the spelled relation
cannot drift apart; if a value law is ever restated, these two are what fails.
The fill's comment says so.

`x/x = 1` is deliberately **not** a law here, and the reason is a measurement
rather than a preference: `QExt.div(d, x, x, q)` unfolds to
`QExt.mul(d, x, QExt.inv(x, q))` verbatim, which is exactly the product
`QExt.mul_inv` concludes, so a caller writes the quotient they want and cites
that law. `Rat.div_self.gt` is a real Rat law only because Rat's divisor there
is a raw coordinate spelling; at the operation level the statement collapses
into the one already present. `probe.payoff.bend` records the collapse from the
caller's side: `probe.op.div.self.gt`/`.lt` are each one call, at a variable `x`.

**`QExt.div_add.gt`/`.lt`.** `(x+y)/z = x/z + y/z`, six positivity hypotheses
(the same list `QExt.mul_distrib` takes) and -- unlike `mul_inv` -- **no `hZ`**:
the law is about dividing by the spelled rational, and what connects a spelling
to a norm is the caller's business. What makes the fill short is the asymmetry
with `QExt.mul_distrib`, which needs the *reciprocal's* coordinate positivity as
hypotheses: here it is not a hypothesis but a derivation, because the reciprocal
of a spelled rational is a constructor whose denominator is `1n+ap` (positive by
`{==}`) and `Rat.mul.den.pos` lifts the divisor's positivity to the quotient's.
So the fill is four steps: `+rp = R.Rat.of(1n+dp, 0n, ap)` (the reciprocal's raw
pair, the one `probe.unfold.div.pos` records), two `R.Rat.mul.den.pos` calls --
the second under `R.Rat.neg`, so it is fed `R.Rat.neg.den.pos(zb, hz)` -- and
then `qext.mul_add_left` at the reciprocal. The LT twin is the same with
`of(0n, 1n+bp, dp)` / `of(0n, 1n+dp, bp)`, all witnesses still `{==}`.

`qext.mul_add_left` is a bare *helper*, not a law: `QExt.mul_distrib` is stated
on the left (`(y+z)*x`), the mirror is `QExt.mul_comm` + that law + two
`QExt.mul_comm`s under a cong, and both `div_add` branches share it. The Rat
layer keeps the same mirror as a *law* (`Rat.mul_add_left.arb`) because there it
is a fact about multiplication that consumers may want; here its only consumer
is the fill, and the layer's habit is to keep bare helpers bare (as
`qext.re`/`qext.im` are).

**The `+rp` let, and a gotcha that reappeared in a new position.** The first
version wrote `+rp = R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap}` and died with
`expected : an annotated term (cannot infer) / observed : rat.Rat{int.Int{1n+dp,
0n}, 1n+ap}` -- the long-recorded rule that a constructor literal cannot head a
`let`, which is the whole reason `Rat.of` exists. `R.Rat.of(1n+dp, 0n, ap)` is
the fix, in both branches.

**The field axiom `(x/y)*y = x` is out of reach, and the probes say why.** Three
measurements, in this order, each one run before any proof was attempted:

1. At a variable `x`, `QExt.mul(d, x, QExt.one()) = x` filled with `{==}` fails:
   `expected : QExt.mul(...) / observed : x`. Not definitional -- `QExt.mul`
   destructures its arguments and its coordinates are sums of products, so there
   is real work here, and `QExt.mul_one` is the law that would do it.
2. At a canonical literal instance (`x = y = 2 + sqrt 2`, `d = 2`, norm 2,
   divisor `R.Rat.of(1n+1n, 0n, 0n)`), the axiom closes with `{==}`: `All terms
   check.` So the equation is *true* -- what is missing is a proof at a variable,
   not a counterexample.
3. At a **non-canonical** dividend it is *false*: with real coordinate
   `Rat{Int{2n,0n}, 2n}` (the value 1, spelled unreduced), `x * QExt.one()`
   fails with `expected : Rat{Int{1n,0n},1n} / observed : Rat{Int{2n,0n},2n}`
   -- the product comes back normalized while `x` keeps the unreduced spelling --
   and the axiom at that dividend with `y = QExt.one()` fails the same way.

So no law can state the field axiom at arbitrary values: `==` on `Rat` is
structural and `QExt.one()`'s own coordinates are canonical, so the conclusion is
canonical whether or not the dividend is. The variable form has to be presented
over canonical spellings (canonicality hypotheses, exactly the shape
`Rat.mul_one(n, d, fx)` uses, where `fx : Rat.mk(n,d) == Rat{n,d}` is the
bridge), and it therefore waits on a presentation-level `QExt.mul_one` rather
than on any positivity fact. That is the next unit. The route is stated as a
route, not as a result: measurement 1 is what says `mul_one` is needed at all,
and the canonicality restriction is a restriction on the *proof*, since
measurement 2 shows the equation itself holds.

**The consumer probe grew the operation surface.** `probe.payoff.bend` gains
six defs (twelve in the file now, from the six of round six): `probe.op.unfold.inv` (that `QExt.inv` is its own body by conversion,
at a variable value and a variable rational), `probe.op.div.self.gt`/`.lt` (the
collapse above, one call each), `probe.op.div_add.gt`/`.lt` (the new pair at
variables), and `probe.op.instance`
(`(2 + sqrt 2)/(2 + sqrt 2) = 1` at literals -- `{==}`, as the rest of the
literal instances are). The defs are written against the published names at
their own telescopes, so an implicit argument that stops being inferable fails
here first.

**Counts, measured.** Laws-only: nat.bend 128, int.bend 32, qext.bend 34,
rat.bend 223, qrat.bend **237** (rat's 223 + 14 QExt: the ten of round six, the
two `mul_inv` operation laws, the two `div_add` operation laws). All five
`src/*_proofs.bend` print `All terms check.`, as do `probe.bend` and
`probe.payoff.bend`; `scratch.bend` prints the same triple it has since round
three. The defs themselves do not move the count -- laws-only was still 233
after `QExt.inv` and `QExt.div` were added, and `qrat_proofs.bend` checked
immediately.

## QExt.mul_one and the field axiom on both signs: the canonical presentation is part of the statement (measured)

Round seven measured the field axiom `(x/y)*y = x` out of reach and named the
reason: every route passes through `x * 1 = x`, which is false at non-canonical
dividends, so the axiom waits on a presentation-level `QExt.mul_one`. This round
adds that law and then the axiom itself, one law per sign of the norm.

**`QExt.mul_one` is stated over bridges, not over coprimality.**

    law QExt.mul_one:
      for +d, np, nn, dp, mq, mn, dq
      for +f1: {Rat.mk(Rat.num(np,nn), 1n+dp) = Rat{Rat.num(np,nn), 1n+dp}}
      for +f2: {Rat.mk(Rat.num(mq,mn), 1n+dq) = Rat{Rat.num(mq,mn), 1n+dq}}
      {QExt.mul(d, QExt.of(np,nn,dp,mq,mn,dq), QExt.one()) = QExt.of(np,nn,dp,mq,mn,dq)}

The two bridges are exactly `Rat.mul_one`'s own hypothesis, so the law passes
them straight through instead of re-deriving them; a bridge is strictly weaker
than coprimality, and a `neg_neg`-style caller who *has* coprimality reaches
these with one `Rat.mk.fixed` call per coordinate and nothing new to prove
(`probe.mul_one.fixed` is that caller, written out). The `QExt.of` spelling is
the same canonical presentation `QExt.neg_neg` and `QExt.add_assoc` use.

**The real coordinate is where the work is, and it is the radicand's fault.**
`QExt.nat(d) = Rat{Rat.num(d,0n), 1n}` has base denominator `1n`, while
`Rat.mul_zero` is stated at `Rat{n, 1n+dp}` -- there is no way to feed the
radicand's coefficient to it. So the file gains one bare helper,
`qext.nat.mul_zero`, the same move `qext.re`/`qext.im` make: a fact about a
narrow spelling that only a fill consumes stays a helper. With it, the real
coordinate is four steps (`mul_zero` on the imaginary product, `qext.nat.mul_zero`
on the radicand term, `Rat.mul_one` on the surviving product, `Rat.add_zero` at
the end) and the imaginary coordinate is three (`mul_zero`, `Rat.mul_one`,
`Rat.zero_add`); the composing fill is two `qext.re`/`qext.im` trans steps. The
law's own left-hand side reduces to `QExt{Lr, Li}` after `match x`, so no
bridging step is needed at the top -- the same fact the payoff laws rest on.

**Four probes ran before any of it was written**, on the pattern that has worked
since round two -- one file per question, each a deliberately-false `{==}` whose
error prints both endpoints in full SNF:

- the real coordinate of `QExt.mul(d, x, QExt.one())` at a canonical
  `x = QExt{Rat{n1,1n+p1}, Rat{n2,1n+p2}}` is
  `Rat.add(Rat.mk(Int.mul(n1, Int{1n,0n}), 1n+Nat.mul(p1,1n)),
   Rat.mul(QExt.nat(d), Rat.mk(Int.mul(n2, Int{0n,0n}), 1n+Nat.mul(p2,1n))))`
  -- the first summand already `mk`-headed, the second still `mul`-headed with
  the radicand factor *unfolded*. Writing the intermediates in this spelling,
  rather than in the `Rat.mul(XA, one())` spelling one would expect, is what made
  the fill short.
- `Rat.add(Rat{n,1n+p}, zero)` reduces to
  `mk(Int.add(Int.mul(n, Int{1n,0n}), Int{0n,0n}), 1n+Nat.mul(p,1n))` -- exactly
  `Rat.add_zero`'s `fx` input, so that law applies with `{==}` for its bridge.
- `Rat.mul(Rat{n,1n+p}, zero)` and `Rat.mul(Rat{n,1n+p}, one)` likewise reduce to
  exactly `Rat.mul_zero`'s and `Rat.mul_one`'s inputs.
- `Rat.mk(Int.zero(), 1n)` is `Rat.zero()` by conversion, and `Nat.mul(1n,1n)` is
  `1n` -- the base cases the fills lean on.

**One failure with no location line, diagnosed by bisection rather than by
reading.** The first version of the fill failed with an error whose text was
65537 bytes of one unfolded `Rat.mk` normalization -- `Nat.divmod`/`gcd` towers
over `Nat.sub(np,nn)`, `Nat.sub(mq,mn)`, `Nat.sub(0n,d)`, `Nat.mul(1n+dq,1n)`.
`grep -c 'Location'` over the capture returned **0**: a giant-term error has no
location line at all, so "read the head of the error" is not available and
`head -30` lands mid-term (lines are enormous). What worked was a three-way
bisection written as a script: back the file up, extract the new block, and
rebuild the file keeping any subset of the three pieces -- `.re` alone, `.im`
alone, the composing fill alone -- running the gate on each. `im` alone checked
(`Error: 1 TODO found.`, the unfilled law); the fill alone failed with
`expected : a defined name / observed : QExt.mul_one.re` (it calls a def that
isn't there); `re` alone produced the giant term. That named the culprit in three
runs without reading a byte of the 64 KB. A botched python edit in the middle of
this produced a parse error at lines 979-981 and was fixed by restoring the
backup wholesale -- **full restore, then patch**, never incremental repair of a
mangled edit.

**Two bugs in the real coordinate, both about the endpoint a rewrite meets.**

1. `+e1` was the *sub-term* equality `mul(D, mul(XB, zero)) = mul(D, zero)` fed
   to a `Equal.trans` whose endpoints were the whole sums. Fix: wrap it, i.e.
   make e1 an outer `Equal.cong` over `u => Rat.add(Rat.mul(XA, one()), u)` whose
   evidence is that inner `cong`. (The checker's first complaint, after the
   wrapping, moved up a level -- which is itself the signal that the level was
   wrong.)
2. In the composing fill, `Equal.trans`'s middle term was `QExt{A1, B1}` -- the
   chain's internal intermediate name -- but the first leg concludes at
   `QExt{XA, B1}`, the rewritten coordinate. `trans`'s `b` is the term both legs
   must *meet* at; it is not a name of convenience. This is the second time this
   exact mistake appeared (round three, `QExt{A1,B1}` → `QExt{XA,B1}` in the
   payoff's compose), so it is worth a rule: **write `trans`'s middle term as the
   exact endpoint of the first leg, copying it out of the first leg's evidence,
   not out of the chain's list of names.**

**The field axiom, `QExt.div_mul_cancel.gt`/`.lt`.** `(x/y)*y = x` with a
canonical dividend, one law per sign of the norm's spelling. Three deliberate
choices, each measured rather than preferred:

- `x` is canonical (the `QExt.of` spelling plus `mul_one`'s two bridges). Nothing
  branch-free can exist: `==` on `QExt` is structural and the product comes back
  normalized, which is round seven's measurement 3 and the reason `QExt.mul_one`
  had to be stated this way in the first place.
- `x`'s positivity is **not** a hypothesis, though `mul_assoc` needs it: the
  spelled `x` has successor denominators, so `Nat.cmp(0n, 1n+dp)` computes and the
  fill passes `{==}` -- the same derivation-not-hypothesis move `div_add`'s fill
  makes.
- `y` is arbitrary, so both of its coordinates' positivity and the spelled norm
  with `hZ` are hypotheses -- exactly what `QExt.mul_inv` asks for, because the
  fill ends by calling it.

The fill is the composition the design was waiting for: `QExt.div` unfolds to
`mul(d, x, inv(y,q))` by definition; `mul_assoc` regroups it to
`mul(d, x, mul(d, inv(y,q), y))`; one `cong` with `mul_comm` inside moves the
reciprocal to the right; one `cong` with `QExt.mul_inv.gt` (which states
`y * inv(y) = one()`, hence the `mul_comm` *first* -- assoc leaves `inv(y) * y`)
collapses the pair; and `QExt.mul_one` finishes. Five lets, three derived
positivity facts, no new helper. The three bugs hit while writing it, in order:

1. `+Y = Q.QExt{ya, yb}` -- the constructor-cannot-head-a-`let` rule, fourth
   instance in this project. The fix here was not `QExt.of` but deletion: the
   `match y` binder already exists, so use `y` itself.
2. `gi`/`hi` were built from `x`'s coordinates with `{==}`. They are the
   *reciprocal's* positivity, so they must come from `y`:
   `Rat.mul.den.pos(ya, rp, gy, {==})` and
   `Rat.mul.den.pos(Rat.neg(yb), rp, Rat.neg.den.pos(yb, hy), {==})`. The error
   printed the type it wanted, `{Nat.cmp(0n, denof(mul(ya, rp))) == LT{}}`, which
   named the operand.
3. The giant mismatch (expected and observed both 2614 characters, first
   difference at character 1530, pure `mul`-grouping with no spelling
   difference): the outer `Equal.trans`'s middle term was `L2`, but its legs
   prove `{L1 = L3}` and `{L3 = X}` -- it had to be `L1, L3, X`. Same rule as
   above, one level out.

**Localizing a 2614-character term diff, and reading `base.bend` instead of
guessing.** Two cheap techniques carried bug 3: (a) a token-level `difflib`
diff, tokenizing on `mul(|add(|neg(|{,|},|,` plus words, so the opcodes say
whether the difference is grouping or spelling -- here every opcode was
`mul`-grouping, which ruled out the whole class of spelling bugs in one step;
(b) replacing a single evidence term with `{==}` so the checker prints the type
it *demands* at that position (that is how bug 2's wanted type was read, and how
the `mul(mul(ya,q),ya)` vs `mul(ya,mul(ya,q))` orientation was settled). And
`base.bend:355-396` gives the three `Equal` fills exactly: `cong(A,B,f,a,b,e)`
fills `%e : {f(a) = f(_)}` with `{==}`, `sym(A,a,b,e)` fills `%e : {_ = a}` with
`{==}`, and `trans(A,a,b,c,ab,bc)` fills `%bc : {a = _}` with `ab` -- so `b` is
the shared middle term and nothing else.

**The LT twin was generated, not written.** Five substitutions on the GT def text
(`.gt(` → `.lt(`, the parameter list, the two `R.Rat.of(...)` spellings, the
closing `QExt.mul_inv` call), each applied with an assertion and a printed count
(all ×1), followed by a scan for leftovers (`1n+ap`, `, ap,`, `mul_inv.gt`),
then appended as `gt_text + "\n" + lt_text`. It checked on the first run. Round
six's lesson repeats: a mirror *claimed* to be a relabelling can be produced by
relabelling, and the checker is the proof the claim was right -- which held here
only because the GT text was still in the file. (In round six the first script
overwrote the original instead of following it, and the checker caught it as a
missing TODO.)

**Counts, measured.** Laws-only: nat 128, int 32, qext 34, rat 223, qrat.bend
**240** = 128 Nat + 32 Int + 63 Rat + **17 QExt** (the ten of round six, the four
operation laws of round seven, `QExt.mul_one`, and the two `div_mul_cancel`
laws). All five `src/*_proofs.bend` print `All terms check.`, as do
`probe.bend` and `probe.payoff.bend`; `scratch.bend` prints the same triple it
has since round three. `probe.payoff.bend` grew from the twelve defs of the last
commit to eighteen -- three for `QExt.mul_one`, then `probe.div_mul_cancel.gt`/`.lt` from the caller's side at a variable `y`, and
`probe.div_mul_cancel.instance`, `1/(2 + sqrt 2) * (2 + sqrt 2) = 1` at literals,
where every hypothesis is `{==}` and -- as with `probe.mul_one.instance` -- the
product also reduces on its own, so the instance is the arithmetic check and the
variable defs are what exercise the law.

**Temp probes, deleted.** The five scratch probe files this round needed
(`probe.field.a.bend` through `probe.field.d.bend`, `probe.mulone.bend`) were
removed before the commit; their measurements are the four bullets above.

## The additive identity and inverse: the last three laws, and the shortest fills in the layer (measured)

Round eight closed the multiplicative side of the operation surface. What was
left was the additive group: `QExt.add_comm`, `add_assoc`, `sub_eq_add_neg` and
`neg_neg` were in, but nothing said `x + 0 = x` or `x + (-x) = 0` -- and the Rat
layer has all of them (`Rat.add_zero`, `Rat.zero_add`, `Rat.add_neg`). This round
adds the three, and they are the cheapest laws in the layer.

**The additive identity is false at an unreduced coordinate, measured before the
comment was written.** The probe is round seven's, one operation over: at the
real coordinate `Rat{Int{2,0}, 2}`,

    QExt.add(QExt{Rat{Int{2,0},2}, Rat.zero()}, QExt.zero())

comes back `QExt{Rat{Int{1,0},1}, Rat{Int{0,0},1}}` -- the expected/observed pair
the checker printed, with a location line this time (the term is small). So
`QExt.add_zero`/`zero_add` are stated at the canonical presentation with
`QExt.mul_one`'s two bridges, for `QExt.mul_one`'s reason: `==` on `QExt` is
structural, and a non-canonical `x` does not survive the sum.

**What makes them short, and what they do not need.** `QExt.add` is
componentwise, so after the coordinates are read each coordinate goal *is* the Rat
law's statement -- `Rat.add(Rat{n, 1n+dp}, Rat.zero())` against
`Rat{n, 1n+dp}` -- with nothing in between and no intermediate term to name:
one `R.Rat.add_zero(n, 1n+dp, fx)` call per coordinate, and a composing fill that
is just the two `qext.re`/`qext.im` witnesses. In particular there is no radicand
coefficient anywhere, so no helper is needed: `qext.nat.mul_zero` exists only
because `QExt.mul`'s real coordinate multiplies by `QExt.nat(d)`, whose
denominator is base 1 and therefore unreachable by `Rat.mul_zero`. That is also
why these two laws take no `d` parameter: the radicand is `QExt.mul`'s parameter,
not `QExt.add`'s.

**`QExt.add_neg` is stated at an arbitrary value, and that is a contrast worth
recording.** `Rat.add_neg` needs only a coefficient and its denominator's
positivity, and its conclusion is `Rat.zero()` on the nose -- unlike `Rat.neg_neg`
and `Rat.mul_one`, which compare an `mk` against a constructor and therefore need
coprimality or a bridge. Negation is componentwise and produces no `mk` of its
own, so the two sides of the coordinate equation are both compositions and `==`
compares them directly. The fill is one `R.Rat.add_neg` per coordinate, at a
variable `x`, inside a `match`; the law's positivity hypotheses arrive intact
because `QExt.re(QExt{xa,xb})` reduces to `xa` after the match.

**There is deliberately no `QExt.neg_add`, and the reason is a naming fact
rather than a mathematical one.** In this tree `Rat.neg_add` (rat.bend:1206) is
the *distribution* law `-(x + y) = (-x) + (-y)`, not the flipped inverse. A QExt
law called `neg_add` stating `(-x) + x = 0` would therefore mean something
different from its Rat namesake, and the flipped inverse is two steps any caller
can take -- `QExt.add_comm` then `QExt.add_neg` -- so nothing in the tree states
it. (`Rat` itself has no flipped form either. The two layers now agree on
`add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg`, `neg_neg` and
`sub_eq_add_neg`; what `QExt` still lacks on the additive side is `Rat.neg_add`
itself -- negation distributing over a sum -- and on the multiplicative side the
pair `Rat.mul_neg`/`Rat.neg_mul`. Those three are laws about how `neg` interacts
with the operations rather than about the identity elements, and they are the
natural next unit on this side if the structure is to be mirrored exactly.)

**Counts, measured.** Laws-only: nat 128, int 32, qext 34, rat 223, qrat.bend
**243** = 128 Nat + 32 Int + 63 Rat + **20 QExt** (the seventeen of rounds six to
eight plus these three). All five `src/*_proofs.bend` print `All terms check.`,
as do `probe.bend` and `probe.payoff.bend`; `scratch.bend` prints the same triple
it has since round three. `probe.payoff.bend` grew from eighteen defs to
twenty-three: `probe.add_zero`, `probe.zero_add` and `probe.add_neg` from the
caller's side at variables, `probe.add_neg.sub_self` (`x - x = 0` written with
`QExt.sub`, which the law reaches by conversion -- the shape a caller writing a
difference actually has), and `probe.add_zero.instance` (`(2 + sqrt 2) + 0`,
`{==}`, as with the other literal instances).

**All three fills checked on the first run**, which is worth noting against the
record of the last two rounds: every step here was a law applied at a spelling the
goal already carried, with no intermediate term, no congruence to place and no
`trans` middle to match up. The two rounds before this one each cost several
iterations on exactly those three things.

## The negation and conjugation block: a rung-2 Rat law was the missing rung, and one law is out of reach (measured)

Round nine closed the operation surface and named the next unit itself: what the
`QExt` layer still lacked was "`Rat.neg_add` itself -- negation distributing over a
sum -- and on the multiplicative side the pair `Rat.mul_neg`/`Rat.neg_mul`". This
round adds those, plus the two conjugation laws that finish the additive half of
`conj`, and the round needed a *new Rat law* to do it. It also found that one of
the round-nine sentences about a law name was about the wrong law, and that one
member of the block -- `conj(x*y) = conj(x)*conj(y)` -- cannot be stated here at
all.

**The canonical `Rat.neg_add` cannot reach an operation output, so the rung-2 form
had to be written.** `Rat.neg_add` (rat.bend:1206) spells its summands
`Rat{num(np,nn), 1n+dp}`; `QExt.neg_add`'s summands are coordinates of an arbitrary
`QExt`, which after `QExt.add` are `Int.add`-headed sums of scaled difference
pairs, and no congruence turns one into the other. This is the fourth time the same
pattern has forced a rung-2 law (`Rat.add_assoc.arb`, `Rat.mul_assoc.arb`,
`Rat.mul_distrib.arb`, now `Rat.neg_add.arb`): the *canonical* Rat laws are what the
`Rat` layer is stated over, and the *arbitrary-value* forms are what a composing
layer can call. `Rat.neg_add.arb` (rat.bend:1360) is

    -(x + y) = (-x) + (-y)      for arbitrary x, y, with only px and py

-- the −1 factor written as `Rat.neg(Rat.one())`, which is `neg_eq_mul_negone`'s own
spelling of it, so its positivity is `{==}` at a literal and no hypothesis is
needed for it. The route is `Rat.neg_eq_mul_negone` (negation is multiplication by
−1), `Rat.mul_distrib.arb`, and then the same law again at each summand under a
congruence. No destructuring, no value law, no cross product. The fill
(rat_proofs.bend:4559) is a three-deep `Equal.trans` whose middle terms are the
scaled summands; it mirrors `Rat.neg_mul`'s three-step fill one operation over.

**The one error in that fill is a rule about `Equal.sym` worth stating.** The first
leg is `Rat.neg_eq_mul_negone(s)` and the goal's left endpoint is already
`neg(s)`, so the law applies in the direction the `trans` needs and must be cited
*naked*. Wrapping it in `Equal.sym` produced the flip the checker printed --
`expected {neg(s) == mul(A,s)}` against `observed {mul(A,s) == neg(s)}`. `sym`
belongs on the *small congruence witnesses* inside the last leg (which need the
opposite orientation from what `neg_eq_mul_negone` states), not on the leg that
already matches. Both are visible in the fill as two `Equal.sym`s on the inner
witnesses and none on the leg.

**`QExt.neg_add`'s hypothesis set was wrong in the first draft, and reading the
definition is what fixed it.** The draft took only the *imaginary* coefficients'
positivity, on the assumption that `QExt.neg` negates the imaginary coordinate
alone. It does not:

    QExt.neg(x) = QExt{Rat.neg(xa), Rat.neg(xb)}

-- componentwise. Negating the imaginary coefficient alone is `QExt.conj`. So both
coordinates are negated sums needing both summands' positivity, and the law
(qrat.bend:484) takes `gx, gy, hx, hy`. The fill (qrat_proofs.bend:1109) is then
two `Rat.neg_add.arb` calls -- one per coordinate, via `qext.re`/`qext.im` -- and
nothing else, with no congruence anywhere, because both sides of each coordinate
equation are compositions `==` compares directly. The general lesson: the
hypothesis list of a composing law is what the *fill's* Rat laws need, so deriving
it from the fill (or from the operation's definition) before writing the statement
costs less than a rewrite after.

**The multiplicative twins, and what they cost.** `QExt.mul_neg` and
`QExt.neg_mul` (`mul(d,x,-y) = -(mul(d,x,y))` and `mul(d,-x,y) = -(mul(d,x,y))`,
qrat.bend:503 and :513) are not symmetric in price. `mul_neg` is per coordinate and
needs a helper level: a coordinate of a product is a sum of two products, so the
negation has to travel one factor at a time (`Rat.mul_neg` at each product of
`xa`/`ya`, and on the real coordinate if the radicand term is involved,
`Rat.mul.den.pos(xb, yb, hx, hy)` as the positivity prototype for the coefficient
`d` pulled inside the negation under a congruence), and then the two negations
merge with `Equal.sym(Rat.neg_add.arb(P, Q, ...))` -- the law above it, read
backwards. `QExt.neg_mul` is then *three steps and no coordinates of its own*:
`QExt.mul_comm` moves the negation into the second slot, `QExt.mul_neg` does the
work, and one `Equal.cong` of `QExt.neg` over `QExt.mul_comm` swaps the factor
back. Two laws for the price of one because the commuting law was already in the
file.

**`conj_add` is one call, `conj_conj` is one call plus a hypothesis, and together
they say `conj` is an additive automorphism.** `QExt.conj_add` (qrat.bend:341)
needs a single `Rat.neg_add.arb` on the imaginary coordinate and no congruence at
all: the real coordinate is the *same term* on both sides, and addition is
componentwise. `QExt.conj_conj` (qrat.bend:373) is `neg(neg(im x)) = im x`, so it
needs `Rat.neg_neg`, which is false unconditionally (rat.bend records the witness
`np = 4, nn = 0, dp = 1`) and therefore carries the canonical spelling plus
coprimality -- on the imaginary coordinate *only*, because the real coordinate
never enters it. Its fill (qrat_proofs.bend:1267) is the `Q.QExt.neg_neg` call
shape one operation over. One error here, and it is the constructor-in-a-`let`
rule again: `+RE = R.Rat{R.Rat.num(np,nn), 1n+dp}` is rejected with "an annotated
term (cannot infer)", and `R.Rat.of(np, nn, dp)` is the fix -- a bare constructor
cannot be the right-hand side of a `let` in this checker.

**`conj(x*y) = conj(x)*conj(y)` is out of reach here, and not for a presentation
reason.** Its real coordinate is `mul(xa,ya) + d*mul(neg xb, neg yb)` against
`mul(xa,ya) + d*mul(xb,yb)`, so the law needs

    mul(neg xb, neg yb) = mul(xb, yb)     at variables

and nothing in rat.bend reaches that. The only route to it is double negation at a
product's own output, `neg(neg(mul(xb,yb))) = mul(xb,yb)`, and `Rat.neg_neg` is
stated over the canonical spelling, which a product is not -- its conclusion is a
constructor-headed `Rat{...}` and applications of `Rat.mul` are def-headed terms.
Measured this round, both halves of that:

    {==} at variables:  expected  neg(neg(mul(a,b)))
                        observed  mul(a,b)              (fails)
    {==} at literals:   neg(neg(mul(Rat{Int{2,0},3}, Rat{Int{5,0},7})))
                          = mul(Rat{Int{2,0},3}, Rat{Int{5,0},7})   (closes)

-- the identity is *true* and every literal instance is `{==}`, while at variables
the checker cannot even compare the two sides. What would unblock it is a Rat law
about `mk`'s own output being reduced: the coprimality of the numerator and
denominator that `mk` produces, which is Nat-level gcd work rather than a
rearrangement. Until then the law is deliberately absent, and the exclusion, this
route and both measurements are recorded in `QExt.conj_conj`'s comment where a
reader looking for the missing law will actually be.

**Counts, measured.** Laws-only: nat 128, int 32, qext 34, rat **224**, qrat.bend
**249** = 128 Nat + 32 Int + **64 Rat** + **25 QExt** (the twenty of rounds six to
nine plus `neg_add`, `mul_neg`, `neg_mul`, `conj_add`, `conj_conj`). All five
`src/*_proofs.bend` print `All terms check.`, as do `probe.bend` (restored verbatim
from HEAD and re-checked after a stray experiment was found in it) and
`probe.payoff.bend`; `scratch.bend` prints the same triple it has since round
three. `probe.payoff.bend` grew from twenty-three defs to **thirty**: the five laws
from the caller's side at variables, `probe.neg_add.out` (the same law through
`Equal.sym`, because the orientation a caller with a sum of negations needs is not
baked into the statement), and `probe.conj_conj.instance` at literals.

**The fills reported green after one real error** (the constructor in a `let`
above) and one editing miss, which is the cheapest this layer has been since round
nine -- and the block landed in the order round nine predicted for the Rat-facing
part, with the addition round nine did not predict: that the Rat-facing part needed
`Rat.neg_add.arb` before `QExt.neg_add` could exist at all.
