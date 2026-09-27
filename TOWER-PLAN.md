# TOWER-PLAN — a tower of quadratic extensions in bend, for 30-deep chains

**This is a plan, not a measurement.** Every number quoted as *measured* comes from
`PROVING.md` rounds four through seventeen or from `README.md`. Everything about the
tower itself is design, and Step 0 exists to falsify parts of it cheaply before any
of it is built.

The general design this plan ports is `../tactus-quadratic-extension/DESIGN.md`
(referred to below as **DESIGN**). The older Verus implementation of a subset is
`../verus-quadratic-extension` (`src/dyn_tower.rs`, `src/dyn_tower_lemmas.rs`), and
the constraint/solver layer it feeds is `../verus-2d-constraint-satisfaction`.

---

## 1. The target, and why it forces the design

The use case is a *construction chain*: a circle drawn on a circle drawn on a circle,
thirty times, where each step places a point by intersecting two loci built from the
previous steps. In the worst case thirty such steps is a degree-2³⁰ algebraic number
— about 10⁹ for the flattened degree — and DESIGN §2 is right that this is intrinsic:
it is the field extension degree, not an artifact of a lazy representation. So:

- **Flattening is not an option.** 2³⁰ basis coefficients is not a slow computation,
  it is an impossible one, at any depth worth having.
- **What is compact is the nested expression**, one level per step. That is the whole
  design idea, and it is what this plan builds.

Two consequences to accept up front rather than discover later:

- **There is no canonical flattened form for a deep element.** Its minimal polynomial
  has degree 2³⁰, so it cannot be produced, and there is no global canonical
  comparison. Local questions are cheap; global ones are not.
- **Therefore a sketch lives in one tower.** Comparing values from two independently
  built towers needs a compositum — the exponential thing DESIGN §9.1 rejects route
  (γ) for. A certificate is a single tower, so this costs nothing in practice; it is
  the reason not to design a "merge two sketches" operation.

What "exact value" means here: a nested radical, evaluable to any precision, with
per-step exactness certificates. Not a normal form that can be hashed or simplified.

## 2. Where this lane stands

Measured on `main` at round twenty-one (Step 0.2 committed as `3ec7043`, Step 1 landed),
transitive over imports: **nat 129, int 32, qext 34, rat 229, qrat 265, tower 233** laws
-- the last being rat.bend's 229 plus the tower's own four. All six `src/*_proofs.bend`
check, as do `probe.bend` and `probe.payoff.bend`; `scratch.bend` prints its triple. The
tower gate runs in 1.60 s, against 0.34–3.35 s for the five library gates. Both probes and
`probe.payoff.bend` (4.32 s) were re-measured here, against upstream rather than the parked
branch.

What that buys, at depth 1:

- `Rat` is a field: ring laws, `Rat.mk` normalization, `Rat.mk.eqv` deciding equality
  on canonical values, inverse and division laws stated per sign of the divisor's
  spelling, `Rat.mul_eq_zero` and `Rat.zero_mul` (src/rat.bend).
- `QExt` — one quadratic level, radicand as an operation *parameter* — has the ring
  laws, `conj` as a ring homomorphism, `norm.mul`, the inverse/division payoff, the
  norm's own identities, and the zero-divisor boundary (src/qrat.bend).

The constraints this lane has measured, which the plan below is built around:

- `==` is structural, and every law carries its presentation hypotheses. Laws stated
  over spelled coordinates cost seconds and occasionally gigabytes (PROVING rounds
  twelve to fourteen); laws stated at stuck terms — variables — cost nothing. Round
  seventeen measured one law at +6.7 s spelled and ~0.1 s restated.
- A fill's type must be the goal's *written* form, not its normal form (round fifteen).
- A def whose name is qualified by the import alias (`R.Rat.foo`) takes bare
  parameters only; typed parameters need a helper in the file's own namespace
  (round fifteen).
- Literal *storage* is no longer a problem (Bend 2.0.24 made a nat literal one
  `Lit` node; 10^7 checks in 0.17 s, round eighteen), but literal *arithmetic* still
  is: `Nat.mul`/`div`/`gcd` recurse over the tower and overflow the stack at about
  10^3, and a nat literal is capped at 4294967295n.

## 3. Two things bend gives us for free

### 3.1 Equality of representatives is structural, so D5's correctness half disappears

A level is the quadratic quotient `T[√d]` with representatives of degree < 2. The
constructor *is* the normal form, so `==` on it is already the right equality, and
deciding whether a representative is zero is a structural question about its two
coordinates — recursively.

DESIGN §5 needs D5 — squarefree-not-irreducible levels, gcd with Bézout data, splitting
the level when the gcd is nonconstant — because it has to make zero-tests and
inverses work where equality of representatives is *not* free. In bend that half is
not needed for correctness. What remains is the **unit test**: an element is
invertible exactly when its norm is non-zero, and a level whose radicand is a square
in the level below has norm-zero elements and is not a field. That is the division
and zero-divisors unit this repo already finished at depth 1 (`QExt.inv`,
`QExt.mul_inv.gt/.lt`, `QExt.mul_eq_zero`, `QExt.zero_divisor.d4`).

So **D5 shrinks to a performance lever** here: tower shrinking is something the
untrusted side can do by handing over a shorter certificate, and the checker verifies
the shorter one. It is not on the critical path for correctness.

### 3.2 Types can be indexed by values, so the "relative-ring crux" may not exist

`bend2/base.bend` declares `law Word: for n: Nat; Data` with `type Word.Con<-p: Nat>`,
i.e. a type family indexed by a *value*. If that generalizes to a tower-valued index,
an element type can carry its tower (or at least its depth) *in the type* rather than
in runtime data — which is exactly what DESIGN §9.1 identifies as the hard part: the
trait ladder's operations are absolute while the tower is certificate data, so there
is no honest type to instantiate `T: OrderedField` with, and the design's chosen route
(η) is a mechanically derived *relative* copy of the constraint layer.

In bend, "relative" is already the house style at depth 1: `QExt.mul(+d, x, y)` takes
the radicand as a parameter and every law about it is stated with that parameter
explicit. Generalizing means taking the *tower* as the parameter, which is route (η)
written natively. If the type index can carry it, the crux may not exist at all.

**Measured, round twenty: it generalizes.** A family indexed by a tower value checks,
with the `Word` idiom generalized from a `Nat` index to a tower: indexed constructor types
`Elem.Base<-v: Nat>` and `Elem.Ext<-t: Tower>`, a type-level `def Elem(t: Tower) -> Data:`
that `match`es on the tower, and then

```
def Elem.zero(+t: Tower, x: Elem(t)) -> Elem(t):
  match t:
    case TBase{v}:
      x
    case TExt{re, im, d}:
      x
```

for which the checker reduces `Elem(t)` per branch, so `x` typechecks in both. A law may
quantify `for +t: Tower for +x: Elem(t)`. An element type can therefore carry its tower
*in the type* -- route (η) written natively -- and the crux DESIGN §9.1 names may not exist
on this side at all: Step 2's operations can be typed `Elem(t) -> Elem(t)` rather than
carrying a tower argument through every law. The depth-index-plus-`wf` fallback stays in
the plan for the case where the laws turn out to want it.

## 4. Two things bend makes harder

### 4.1 Sharing

The nested representation is compact only if sub-terms are *reused* rather than
duplicated. A geometric step uses the previous point three or four times, so a naive
encoding — one giant nested term — is 3³⁰ nodes even though the mathematical object is
linear in the depth. Bend terms are trees; whether the checker shares a `let`-bound or
`def`-named value, or substitutes it textually, decides the encoding. §6.1 measured it in round nineteen: the checker shares.

### 4.2 Big numbers: what is fixed, and what is not

Measured in round eighteen, against Bend 2.0.27:

| | status |
|---|---|
| Writing a literal (`1000000n`) | **Fixed.** One `Lit` node since 2.0.24; 10^7 checks in 0.17 s, and the 10^4 that used to overflow the stack is gone. |
| Comparing, matching, checking a literal | **Fixed.** The node unfolds one constructor at a time. |
| Arithmetic *on* literals (`Nat.mul`, `div`, `gcd`) | **Broken.** Still recursive over the tower; stack overflow at ~10^3. |
| Magnitude | **Capped at 4294967295n** (`bend.ts:2352`). No bignum literals. |

So the sequencing consequence changes shape. It is no longer "avoid literals"; it is:

- **Arithmetic on concrete numbers belongs in the compiled lane.** Proof-land
  reasoning stays generic, over variables, where bend is cheapest — and that is the
  same discipline the plan needed anyway (§5).
- **A reducer fast path is the cheap fix for arithmetic**: when both operands of a
  `Nat` operation are literals, compute natively the way the compiled lanes already
  do and box the result as a literal. That is a checker change of the same kind as
  the `Lit` node, not a proof project.
- **A bignum type is a separate, later question**, and its shape should be decided by
  measured coordinate sizes rather than assumed: `Word(n)`'s bit vectors in
  `base.bend` are the obvious substrate, and a proved bignum would need the same
  refinement discipline as anything else here — keep the unary `Nat` laws as the
  spec and prove the binary operations against them.

`bend.ts` is human-written and marked do-not-edit in its own `AGENTS.md`, so the
fast path is a proposal for its owner, not a patch this repo carries.

## 5. The invariant

Everything below rests on one discipline. It belongs in the code as a rule, not a hope:

> **No goal ever contains a deep element's expansion.**

Each step's residual is a question at its own level, reaching lower levels only
through named definitions and law applications, so every goal stays small. Deep
elements are *evaluated* — for drawing, for sign queries, for hundred-digit
coordinates — through the interval path (§9, Step 4), never through exact arithmetic
on an expanded term.

The bend analogue of DESIGN's "never flatten" is therefore not just a representation
choice but a *goal-size* invariant, and Step 0 decides how strictly it has to be
enforced.

## 6. Step 0 — two probes that decide the encoding

Do these first. Both are small, both are in the untrusted/experimental register (no
laws, no gate impact), and each outcome pins down a choice the rest of the plan
depends on.

### 6.1 Does the checker share terms?

Build the same chain at depths 5, 10, 15, 20, 25, 30 in three encodings:

1. **One nested term** — the whole chain written out as a single expression.
2. **One `def` per level**, each referencing the previous by name.
3. **A chain of law applications**, where each step's *goal* is small and the deep
   value appears only as an argument.

Time each. Read the curves:

| Outcome | Consequence |
|---|---|
| 2 or 3 linear, 1 exponential | Encode chains as a sequence of named definitions; the certificate is a list of steps. Plan proceeds as written. |
| All three exponential | The checker substitutes and duplicates. Every goal must then be built one level at a time by law application, and the certificate format is a chain of *small* goals from day one. Step 5 changes shape. |
| All three linear or near-linear | The checker shares substantively. The plan is unconstrained; keep the invariant anyway for the checker's own sanity. |

**Measured, round nineteen** (Bend 2.0.27, the box's nix-store Bun; each row is one
probe file and the times include the ~0.17 s startup these runs sit on):

| encoding | depths | source size | time |
|---|---|---|---|
| 1, written out as one expression | 5, 10, 20, 30, 50, 100 nested `Nat.add` | under 2 KB at 100 | 0.16-0.18 s, flat |
| 2, one `def` per level, each naming the previous twice | 5, 10, 15, 20, 25, 30 | 1 KB at 30 | 0.17-0.18 s, flat |
| 2 again, but with the goal *forcing* the value | 13, 15, 17, 19, 21, 23, 25, 30 | 1 KB | 0.17-0.18 s, flat |

Encoding 2 is the answer, and it is stronger than the plan required. The level-30 value
is a tree of 2^30 nodes if it is ever materialized, and a goal that forces it --
`{P.fst(A30()) == 1n}`, which has to peel thirty levels before it can compare -- checks
in 0.18 s, the same as depth 5. So the checker neither substitutes a named definition
into the caller's term nor builds the tree: reduction is lazy and the value stays
shared. The plan proceeds as written, and Step 5's certificate is a list of named steps.

Encoding 3 could not be built as §6.1 sketches it, for a structural reason rather than
a surprising one: *"expected : a filled definition (an unfilled law is a dead claim:
live code cannot use it)"*. A `law` in `src/*.bend` is a statement awaiting its fill in
`src/*_proofs.bend`, and until that fill exists nothing may call it. A chain of law
applications therefore has to be written where the fills are -- which is where Step 5's
certificate work happens anyway -- so that probe belongs there, not here. What decided
the representation is measured, and it decided for encoding 2.

Two syntax facts the probes paid for, worth having before Step 1: a type is
`type P is Data:` with its constructor on the following line; and a projector is a
plain `def` with a destructuring body (`P{+f, +s} = p`, then `f`), not a derived field
access, so `def P.fst(p: P) -> Nat:` works but its name must not collide with a field.

### 6.2 Does induction over a user-defined recursive type work in fills?

**Measured, round twenty: yes to both**, and the pair below is the working recipe. A
recursive user type, two functions over it, and a statement at variables that no unfolding
settles:

```
type TL is Data:
  TNil{}
  TCon{head: Nat, tail: TL}

def TL.append(a: TL, b: TL) -> TL:
  match a:
    case TNil{}: b
    case TCon{h, t}: TCon{h, TL.append(t, b)}

def TL.sum(l: TL) -> Nat:
  match l:
    case TNil{}: 0n
    case TCon{h, t}: Nat.add(h, TL.sum(t))

law TL.sum.append:
  for +a: TL
  for +b: TL
  {TL.sum(TL.append(a, b)) == Nat.add(TL.sum(a), TL.sum(b)) : Nat}
```

The fill lives in another module, and calls *itself* on the tail: structural induction
written as recursion, which the checker accepts.

```
def L.TL.sum.append(a, b):
  match a:
    case L.TNil{}:
      {==}
    case L.TCon{h, t}:
      %Equal.sym(Nat, L.TL.sum(L.TL.append(t, b)), Nat.add(L.TL.sum(t), L.TL.sum(b)),
          L.TL.sum.append(t, b))
        : {Nat.add(h, _) == Nat.add(Nat.add(h, L.TL.sum(t)), L.TL.sum(b)) : Nat}
      %N.add_assoc_rev(h, L.TL.sum(t), L.TL.sum(b))
        : {Nat.add(h, Nat.add(L.TL.sum(t), L.TL.sum(b))) == _ : Nat}
      {==}
```

Three things it settled. The `match` refines the law's statement to the branch, and the
`Nil` branch closes definitionally (`Nat.add(0n, x)` reduces to `x`). A fill may call
itself on a structurally smaller argument and the *type* follows the argument, so the
induction hypothesis arrives at the smaller tower already stated. And the rewrite
orientation is exact: `%e` replaces the goal's occurrence of `e`'s **right** endpoint with
its left, so a law must be stated in the direction its rewrites need -- `N.add_assoc`
failed here and its flipped twin `N.add_assoc_rev` closed the proof in one step, the same
reason `nat.bend`'s `add_succ` is documented "stated flipped so rewrites fire
left-to-right". The ascription is the goal with the rewritten occurrence written as `_`
and every other slot spelled exactly as the checker prints it.

Two namespace facts the probe paid for: constructor names are **global** (`Nil` and `Con`
are already taken by `base.bend`, hence `TNil`/`TCon`), so `Base`/`Ext` in Step 1's sketch
are fine; and a cross-module *pattern* names the constructor under the module alias with no
type in the path (`case L.TNil{}:`), while construction across modules was not exercised.

The tower-index half of this probe is §3.2's answer; both probe files are deleted, with the
recipes here.

## 7. Steps 1–5

Each step lands with all seven gates green, in the house style: laws in `src/*.bend`
with their fills in `src/*_proofs.bend`, counters as the gate output, PROVING round
written when it lands.

### Step 1 — `Tower`, depth, wf, lift

**Deliverable.** The element type and the structural machinery.

```
type Tower is Data:
  Base{value: Rat}
  Ext{re: Tower, im: Tower, d: Tower}
```

plus `depth`, a well-formedness predicate (each level's radicand positive, levels
reduced), and `lift`, which carries a level-k element into a deeper tower as
`Ext(re, 0, d)` recursively. Lifting is linear and cheap, and it is why shallow
elements stay cheap at depth 40.

**Done when.** `lift` is proved to distribute over the level operations, so every
later law can work at a common depth, and the depth/`wf` predicates are usable as
hypotheses in the style the existing laws use for positivity.

**Risk.** The shape of `wf` is the one real design decision here: too weak and Step 2
carries side conditions everywhere, too strong and `lift` cannot be stated.

**Landed, round twenty-one.** `src/tower.bend` and `src/tower_proofs.bend`: the type as
sketched, `depth`, `zero`, `lift`, and four laws -- `zero.base`, `depth.lift` and
`lift.zero` definitional, `depth.zero` a structural induction in the fill. `lift(t, d)` is
`Ext{t, Tower.zero(t), d}`, one constructor, so lifting is constant-time rather than
merely linear; that is also why `depth.lift` and `lift.zero` are definitional.

`wf` answered the risk as a *sequencing* fact rather than a shaping one. Its arithmetic
half cannot be stated yet -- "a radicand positive, levels reduced" needs the ordering that
Step 2 brings -- and its structural half is automatic, because `Ext{re, im, d}` requires
three towers and an element's shape *is* its level, so no value can violate it. So `wf` is
a family `Tower.wf(t) -> Data` with a trivial leaf and an `Ext` case carrying the three
sub-evidences, and what it demonstrates now is *transport*: `Tower.wf.zero` and
`Tower.wf.lift` are structural inductions in an indexed type, and the second consumes the
first to build the evidence a lift needs. Those are the shapes Step 2's positivity
evidence will take, which is the part of the risk that mattered.

Three exactness facts the type-level work produced, all now load-bearing:

- Evidence at an indexed type does not survive as an equation. `Tower.wf(Tower.zero(t))`
  and `Tower.wf(t)` have different indices (`Tower.Wf.Ext<zero re, zero im, d>` against
  `Tower.Wf.Ext<re, im, d>`) and no equation between them is true, so `Tower.wf.zero` is a
  def that transports evidence, never a law that equates types.
- A type family must be declared *above* the def it references. base's `Word.Con` sits
  above `Word` for the same reason; with the family below, the reference inside the def
  resolves too early and the import fails with a doubled module path.
- Laws and defs share one namespace (`Tower.wf.lift` could not be both), and a def
  parameter used twice needs `+`, exactly like a law's.

The done-when is met for `zero` -- `Tower.lift.zero` is a level operation surviving the
embedding, and zero is the identity of the level's addition -- while the `add` and `mul`
cases land in Step 2, where those operations are defined.

### Step 2 — one level's arithmetic, generically

**Deliverable.** `add`, `neg`, `mul` (reducing with `√d·√d = d`), `zero`, `one`, and
the ring laws for elements of a common level.

**Why this is cheaper than it looks.** The existing `QExt` proofs *are* the induction
step. They are already stated with the radicand as a parameter, and already proved
coordinatewise from `Rat` laws — which is route (η) relativization in its native form,
at depth 1. Generalizing means proving the same body once as the step case of an
induction over the tower, with the laws threading positivity hypotheses through
levels the same way they thread them through coordinates today.

**Done when.** `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `mul_distrib` hold for
tower elements, and the reduction `Ext(0,1,d)·Ext(0,1,d) = Ext(d,0,·)` is available as
an unfolding.

**Risk.** Hypothesis threading: each level's positivity conditions become the next
level's hypotheses, and the bend checker's strict comparison (round fifteen) means
those hypotheses must be stated in the caller's spelling. Expect this to be tedious
rather than hard, and expect it to be where the one-second rule gets tested.

### Step 3 — the unit test

**Deliverable.** A recursive `norm` (an element of the level below), the unit test
"norm non-zero ⇒ invertible", the inverse, and the level-local zero-divisor boundary.

**Why.** This is bend's replacement for D5's correctness half (§3.1), and it is the
generalization of the depth-1 unit that already exists: `QExt.norm`,
`QExt.mul_inv.gt/.lt`, `QExt.mul_eq_zero`, `QExt.zero_divisor.d4`. Division in a
construction step needs it; a degenerate step is exactly a norm-zero element.

**Done when.** Inverse and zero-divisor laws hold at an arbitrary level, stated at
whatever presentation the checker accepts — measured, as those laws were at depth 1.

### Step 4 — the interval fast path

**Deliverable.** Recursive rational evaluation of a tower element with an error bound,
and the one-sided theorem: *if the evaluated interval excludes zero, the sign is as
computed*. Plus realness of each level: a level with a positive radicand has a chosen
positive root.

**Why.** This is what makes branch selection and non-degeneracy work at depth 30
without any exact ordering theory, and it is what lets you draw the chain and read off
coordinates to any precision. DESIGN §7 keeps this soundness-only and notes that
separation bounds are deliberately not verified; bend should follow, and skip Sturm
entirely at first.

**Done when.** A depth-30 chain evaluates to a sign, with the proof obligation being
just interval arithmetic at the base.

### Step 5 — the chain certificate, and the 30-circle demo

**Deliverable.** A certificate as a list of steps, each carrying the local identity it
imposes; a checker that verifies step by step; the global theorem by induction over
the list; and the demo — thirty circles on circles, built and checked, with node count
and check time printed.

**Why this shape.** The global statement "every constraint is satisfied" is a fold
over steps, each of which is a level-local identity, which is the same structural
induction idiom this repo already uses for its `Nat` laws. It is also the bend
counterpart of DESIGN §8, minus the tower-wf certificate work that §3.1 makes
unnecessary for correctness.

**Done when.** The thirty-step chain checks, the timing is reported, and the per-step
cost is visibly not exponential in the step index.

## 8. Deliberately out of scope for now

- **D5 as a correctness mechanism.** Not needed here (§3.1). Tower shrinking is a
  performance lever for the untrusted side.
- **Exact ordering, Sturm–Tarski, separation bounds.** Step 4's interval path covers
  the practical queries; DESIGN §6 keeps the exact route as the fallback and §7 keeps
  the fast path soundness-only.
- **Bignum literals and a literal-arithmetic fast path.** Both are checker-side
  (§4.2). The first is what a sketch with 20-digit coordinates would need; the second
  is what makes proofs about *moderately* sized concrete numbers possible at all.
  Neither is needed for the generic algorithm, and neither is needed to *write*
  numbers any more.
- **Minimal-polynomial recognition (LLL/PSLQ).** An untrusted optimization; DESIGN §8
  explicitly allows the untrusted side to hand over pre-collapsed towers.
- **Cross-tower comparison.** Needs a compositum; see §1.

## 9. References

- General design: `../tactus-quadratic-extension/DESIGN.md` — §2 blowup, §4 towers,
  §5 D5, §6 ordering, §7 fast path, §8 certificate, §9.1 the relative-ring crux,
  §10 milestones, §11 asset map.
- Prior implementation: `../verus-quadratic-extension/src/dyn_tower.rs` (recursive
  `DynTowerSpec<T>`, `Equivalence` and `AdditiveGroup` proved; `Ring`/`Field`/
  `OrderedField` removed pending the `WellFormedDTS` wrapper) and
  `src/dyn_tower_lemmas.rs`; the solver side is `../verus-2d-constraint-satisfaction`
  (19 constraint types, loci, construction-plan soundness, `constraint_satisfied_dts`).
- This repo's own depth-1 laws: `src/qrat.bend` — `QExt.mul` at 123 (the radicand as a
  parameter: relativization in miniature), `QExt.conj` 133, `QExt.norm` 142,
  `QExt.inv` 174, `QExt.norm.mul` 515, `QExt.zero_divisor.d4` 568, `QExt.mul_eq_zero`
  721, `QExt.mul_inv.gt` 956; `src/rat.bend` — `Rat.mk.eqv` 415, `Rat.zero_mul` 319,
  `Rat.mul_eq_zero` 1703.
- Measured constraints: `PROVING.md` rounds twelve to seventeen (conversion cost of
  spelled presentations; the written-form rule; the qualified-name grammar; the
  zero-divisor statement), and `README.md` items 1–3.

## 10. What is measured, and what is not

**Measured** (this repo, this session): law counts and gate timings in §2; the
presentation costs in §2's third bullet; the existence of recursive datatypes and
value-indexed type families in `bend2/base.bend` (§3.2, §6.2); that `QExt` is already
parameterized by its radicand.

**Measured since (round nineteen):** the checker shares terms, and a 30-deep chain of
named definitions costs the same as a 5-deep one, even when the goal forces the value
(§6.1).

**Measured since (round twenty):** fills induct structurally over a user-defined
recursive type, and a value-indexed family carries a tower index -- both Step 0 questions
answered yes (§3.2, §6.2).

**Measured since (round twenty-one):** Step 1 is landed and its gate is green -- the tower
type, `depth`, `zero`, `lift`, and the `wf` evidence family with two transport inductions
(§7 Step 1). `wf`'s shape is settled as far as it can be before ordering exists.

**Not measured, and load-bearing:** the cost of a chain written as law applications, which
can only be measured where laws are filled (§6.1); the arithmetic half of `wf`, which needs
Step 2's ordering; the `Elem(t)`-indexed route §3.2 measured as feasible but which Step 2
would have to adopt wholesale; and every step of §7 from Step 2 on.
