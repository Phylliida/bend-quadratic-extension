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
  never computed values. Pass `Nat.cmp(xm, ym)` to a helper and match on
  the helper's parameter. This is why `Int.add.opp` takes `c: Cmp` as its
  first argument — and it makes the op *proof-friendly* for free (proofs
  can then call the helper with a literal `Cmp`).
- **No `if`**: a branch is a `match` on `True{}`/`False{}`, and there is
  no `Bool` short-circuit sugar in proofs.
- **Termination is structural, left-to-right by argument**: the recursive
  call's arguments must pass unchanged until one is a strict subterm. Put
  the decreasing argument first and keep the others literally unchanged
  (`add_assoc(ap, b, c)`, not `add_assoc(ap, c, b)` reordered by
  rewriting).
- **Parsing**: `1n+x` is sugar for `Succ{x}` and chains (`1n+1n+x`).
  `-`/`+` glued to a name starts a binder, not an operator; space your
  operators.

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
- Unary `Nat` is O(value) at runtime. Proofs don't care; CAD-sized
  coordinates will. A binary-nat layer is the right next investment.

## The Rat route: remaining plan

State at handoff: `Int` is `Int{pos, neg}` = `pos - neg` with all 19 ring laws
proved; `Int.canon` (+ `canon.pos`, `canon.neg`, `canon.idem`) is in; the Nat
scaling groundwork (`cmp_add_left`, `cmp_mul_right`, `mul_sub_add`,
`sub_of_add`, `mul_sub`, `mul_one`) is in. Everything below is still open.

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
   **Scaling done** (`gcd.go.scale`, `gcd.go.fuel`, `gcd_scale`); the
   "divides both" half is open, see the section below.
3. `Int.canon.scale`, and `Int.canon.eqv` (the quotient lemma,
   `canon x == canon y` iff `xp + yn == yp + xn`) if it fits.
4. `Rat`: the type, `Rat.mk`, canonicality by the scaling route, then the
   field axioms.
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

### Why "gcd divides both arguments" is still open

The per-step arithmetic is done and proved: `Nat.divides` /
`Nat.divides_both` (a witness pair), `divides_add` (a multiple plus a multiple
is a multiple, quotients added), `Nat.succ_add_ne_zero` (the fuel hypothesis
at `s = 0` is contradictory), and the branch assembly for both LT and GT.
What does not close is the loop-level induction, and the obstacle is the
checker's affinity rules rather than arithmetic:

- The induction hypothesis returns a *pair* of divisibility witnesses, and the
  step needs the quotients from both halves plus the original pair back. But
  `match` only scrutinizes a parameter or a pattern-bound field ("a match
  cannot scrutinize a computed value"), so the returned pair cannot be taken
  apart in place -- the step has to run inside a helper `def` whose binder is
  the pair.
- Inside that helper the two quotients are each needed twice (once in the
  rebuilt witness, once in `divides_add`). Fields of a `Sigma` are linear --
  `Sigma<&2, &2, ..>` does *not* make them copyable, the *field* quantities
  are what count, and `Tuple{fst, snd}` defaults them to `&1` -- so each needs
  a `+q = q` re-bind first. Those re-binds typecheck on their own (a minimal
  `def` with a nested destructure, a `+` re-bind and a rebuilt pair passes),
  but inside the real fill the checker rejects the whole def with
  `expected : an annotated term (cannot infer) / observed : q => {a ==
  Nat.mul(g, q) : Nat}` -- i.e. it wants the existential's family annotated at
  a point where the source has no lambda at all. That is a checker behaviour
  worth understanding before another attempt; the arithmetic is not the
  problem.
- A `+` re-bind of the *pair* itself is not available either: `Nat.divides_both`
  is a `Sigma<&1,&1,..>`, whose kind is `Type`, and `+` forms only at `Data`.
  The plausible repair -- give the witnesses a `Data` pair type of your own --
  is untried.

Do not weaken the statement to dodge this (`Ex`, `Nat.div`-shaped or
"divides one argument"): the Rat step below consumes the *witness* of
`g | n.pos + n.neg`.

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
