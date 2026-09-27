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
transitive over imports: **nat 129, int 32, qext 34, rat 229, qrat 265, tower 240** laws
-- the last being rat.bend's 229 plus the tower's own eleven. All six `src/*_proofs.bend`
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

**Partially landed, round twenty-two.** The operations and their spellings are in:
`Tower.add(+d, x, y)`, `Tower.neg(x)`, `Tower.mul(+f, +d, x, y)`, `Tower.one(t)`, with
seven laws at spelled constructor forms -- `add.base`, `add.ext`, `neg.ext`, `mul.base`,
`mul.ext` (the `sqrt(d) * sqrt(d) = d` unfolding the done-when asks for), `one.base`,
`one.ext` -- all filled definitionally, and the tower gate green at 240 = rat.bend's 229
plus its own eleven. The five ring laws (`add_comm`, `add_assoc`, `mul_comm`,
`mul_assoc`, `mul_distrib`) are *not* proved yet: they are inductions over the tower and
they are the rest of this step, along with the route B probe and the fuel-sufficiency
law.

The radicand is an operation *parameter*, as planned, and that is what keeps the laws
free of shape-agreement hypotheses: `add(d, x, y)` and `add(d, y, x)` mention one
radicand. Operands at different levels are not a value of the theory, so the mismatched
arms return the level's zero and no law reaches them.

**`mul` has to be fuel-driven, and that is a checker constraint, not a style choice.**
bend checks that every self-call decreases -- *"arguments are read left to right: each
passed unchanged until one shrinks"* -- and the `sqrt(d)*sqrt(d) = d` term needs the
im*im product multiplied by `d`, which nests one self-call inside another's argument.
Measured: two operands shrinking together is *fine* (`add` passes with
`add(d, rx, ry)`), a let-bound intermediate does not help (still rejected), and
descending on a `Nat` fuel does -- which is the same shape `base.bend`'s own `Nat.gcd`
takes, so there is precedent. Callers pass a fuel of at least the operands' depth; a law
that enough fuel never runs out is part of the rest of this step. Every `mul` law is
therefore spelled at a successor fuel, `Tower.mul(1n+g, d, ...)`.

**Three exactness facts the spellings cost**, all load-bearing for the ring laws:

- **Pattern binders are linear.** A constructor field used more than once in a body
  needs `+` in the pattern, exactly as a parameter does (`case Ext{+rx, +ix, +dx}:`),
  or the checker reports *"expected : iy"* -- which reads like a missing variable and is
  not.
- **A law's statement may only name its `for` parameters.** Pattern binders inside a
  statement are not implicitly quantified: `Ext{rx, ix, dx}` with no `for dx` reports
  *"expected : a defined name / observed : dx"*, so every tower value mentioned in a
  statement is declared.
- **A fill's parameter list mirrors its law's `for` list exactly, in order.** The
  checker prints what it expected (`@iy -> @dy -> ...`), which is the fastest way to get
  the order right.

**Route B probed, round twenty-three: the statements are cleaner, the fills are not.**
A bounded probe built the indexed route: `Elem.Base<-v: Rat>` and `Elem.Ext<-t: Tower>` as
the indexed constructors, `def Elem(t: Tower) -> Data` matching on the tower (a rational at
`Base`, a pair over `Elem(d)` at `Ext{re, im, d}`), and

```
def Elem.add(+t: Tower, x: Elem(t), y: Elem(t)) -> Elem(t):
```

which checks, with each branch destructuring its operands because the checker reduces
`Elem(t)` once `t` is a constructor. The ring law then states *with no shape hypothesis at
all*:

```
law Elem.add.comm:
  for +t: Tower
  for +x: Elem(t)
  for +y: Elem(t)
  {Elem.add(t, x, y) == Elem.add(t, y, x) : Elem(t)}
```

and that is route B's real advantage: a mismatched-radicand call cannot be written, so
nothing has to be hypothesised away. The file checks at 231 TODOs = rat.bend's 229 plus the
two laws, exactly as predicted.

The fill is where the index bites. The `Base` branch closes in one step -- `Equal.sym`
around `R.Rat.add_comm`, with the goal's type written as `Elem(Base{v})` -- and the `Ext`
branch does not: rewriting inside the constructor needs `Equal.cong`, and its lambda cannot
infer the indexed constructor's index at a *variable* context. Measured three ways with the
same result:

*expected : Elem(d) / observed : Elem.Ext<d>*

The checker wants the lambda's **domain** type where the codomain belongs, so
`u => EExt{u, ...}` is rejected no matter how the ascription's type is spelled (reduced
`Elem.Ext<d>` or unreduced `Elem(LB.Ext{re, im, d})` both fail identically). The untested
candidate fix is the house helper pattern -- a typed def `Elem.Ext.at(+d, u, xi) ->
Elem.Ext<d>` so the lambda returns a *declared* type instead of an inferred constructor
index -- but that would need one such helper per congruence per constructor, which is the
shape of cost to weigh.

**Verdict, revised in round twenty-four: route B is viable.** The round-twenty-three
verdict -- continue on route A -- rested on the wall above. That wall is measured
differently now, and the *index inference* was never the problem:

- The helper pattern works. A typed def
  `Elem.Ext.at(+d: Tower, u: Elem(d), w: Elem(d)) -> Elem.Ext<d>` makes `Equal.cong` with
  an indexed codomain check **as a direct term**
  (`Equal.cong(Elem(d), Elem.Ext<d>, u => Elem.Ext.at(d, u, w), a, b, e)`), which is the
  signature `(domain, codomain, f, a, b, e)` confirmed against the checker.
- What fails is a **`%`-script step whose ascription type is indexed**: five spellings
  measured, one message (*expected : Elem(d) / observed : Elem.Ext<d>*), and the ascription
  cannot be dropped at all (the checker reports *expected : ':' / observed : '%'*).
- Build the fill out of direct terms instead and the indexed law goes through:
  *All terms check.* The probe uses three small congruence defs (`Elem.at.cong`,
  `Elem.at.cong.r`, and `Elem.pair.cong` composing them with `Equal.trans`) and the `Ext`
  branch of the law's fill is then a single term application. The `Base` branch keeps its
  `%` step, which works -- its ascription type `Elem(Base{v})` has a *plain* slot type
  (`Rat`), while the `Ext` branch's hole sits in a slot of indexed type `Elem(d)`.

So route B's cost is a small family of typed congruence defs per constructor -- three in the
probe, about twelve lines -- plus `Equal.trans` to compose them, and the payoff is that a
mismatched-radicand call **cannot be written at all**. That is the difference the "no errors
can happen" requirement turns on: route A's mismatch arms return `zero(d)`, which `depth`
cannot distinguish from a correct element of the same level, so A's safety is a convention
enforced by review; B's safety is a type. The cost is per operation, not per checker fix.

Not yet measured for B: `mul` (whether the `sqrt(d) * sqrt(d) = d` term needs the same Nat
fuel under an indexed signature), the remaining ring laws, and the target-file timings.

Both probe files are deleted; the recipes are here and in PROVING round twenty-three.

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


### Route B's operations, measured (round twenty-five)

`add` was proved under route B in round twenty-four. `mul` is where the
`sqrt(d)*sqrt(d) = d` term forces the radicand into the term itself, and the
measurements below settle its shape.

**The radicand cannot be used as an element (measured).** A def whose body passes the
radicand tower where a coefficient is expected:

    def LB.Elem.crux(+d: LB.Tower, u: LB.Elem(d)) -> LB.Elem(d):
      LB.Elem.add(d, u, d)

fails with `expected : probe.tower.rb.Elem(d) / observed : probe.tower.rb.Tower`. So
route A's spelling `mul(d, mul(d, ix, iy), d)` has no route B counterpart: `d` is a
tower, not an element of the coefficient ring.

**The embedding is blocked too (measured).** `def Elem.of(+t: Tower) -> Elem(t)` with
the Ext case `EExt{Elem.of(re), Elem.of(im)}` fails with
`expected : probe.tower.rb.Elem(d) / observed : probe.tower.rb.Elem(re)` -- a
coefficient carries the index `re`, the field demands `Elem(d)`. This is the
relative-ring crux, in bend, with a checker message.

**A type index is legal (measured).** `type ElemT.Ext<-K: Data> is Data: TExt{re: K, im: K}`
plus `def ElemT(t: Tower) -> Data` returning `ElemT.Ext<ElemT(d)>` checks. So the Ext
case may be indexed by the coefficient ring itself.

**So the shape that works is a carrying one**, and it checks:

    type ElemC.Ext<-K: Data> is Data:
      CExt{re: K, im: K, dr: K}      # dr = the radicand, as an element of the coefficient ring

    def ElemC(t: LB.Tower) -> Data:
      match t: Base{v} -> ElemC.Base<v>; Ext{re, im, d} -> ElemC.Ext<ElemC(d)>

**And route B's `mul` needs no fuel (measured, twice).** The nested term
`ElemC.mul(d, ElemC.mul(d, xi, yi), xdr)` checks both with a Nat fuel and at
`ElemC.mul(+t, x, y)` with no fuel at all: 229 either way. The contrast with route A is
the point -- route A's `mul` descends on a plain tower parameter and had to carry fuel
precisely because nothing shrinks; route B recurses with the level index `d`, which is a
subterm of `Ext{re, im, d}`, so the structural descent is real and the fuel-sufficiency
law disappears from the plan.

**But the carrying field does not verify radicand agreement -- and the checker proves
it (measured).** With `law ElemC.add.comm` stated for all `x, y : ElemC(t)`, unfolding
both sides gives

    expected : ... == CExt{add(d,yr,xr), add(d,yi,xi), ydr} : ElemC.Ext<ElemC(d)>
    observed : ... == CExt{add(d,yr,xr), add(d,yi,xi), xdr} : ElemC.Ext<ElemC(d)>

The third field is the left operand's carried radicand on one side and the right
operand's on the other, so the law is simply false unless the two agree. That is the
improvement route A could not deliver: in route A a mismatched call returns `zero(d)`,
indistinguishable by `depth` from a correct element, and every law holds vacuously. Here
a mismatched call is *unprovable*. It is still not *untypeable*, which is what
safety-by-construction would need.

**The obstruction to the clean statement, named.** A hypothesis-free law wants the
radicand as an *index* (`Elem.Ext<-K, dr: K>`), so that operands must share it by
construction; the operations want the radicand as *data*, because `mul` has to multiply
by it. As measured, the level family cannot supply that index -- it dispatches on the
tower `t`, and no `dr` is determined by `t` (the embedding that would determine it is
itself blocked above). The untested design that could reconcile them is an
operations *record* passed per level, so that a radicand-indexed `Ext` type has the
coefficient ring's `add`/`mul` in hand; that is the next probe, and it is unmeasured.


### The operations record is not expressible, and why that settles the design (round twenty-six)

Round twenty-five left one reconciliation untested: index the element type by the
radicand, and hand the operations in per level. Three measurements close it.

**A `Data` type cannot hold a function field.** `type Ops<-K: Data> is Data:
OpsRec{add: K -> K -> K, mul: K -> K -> K}` fails with
`expected : Data / observed : Type` at the field. Function types have kind `Type`, and a
`Data` declaration wants fields of kind `Data`. (The parenthesised spelling is worse --
`(K, K) -> K` parses as a `Sigma`: `expected : Type / observed : Sigma`. Function types
are written with bare arrows.)

**A def cannot take a type or a function parameter.** Three variants, one message:

    def EB.k(+K: Type, +dr: K, x: EB.Ext<K, dr>, y: EB.Ext<K, dr>) -> EB.Ext<K, dr>
    def EB.k(+K: Data, +dr: K, x: EB.Ext<K, dr>, y: EB.Ext<K, dr>) -> EB.Ext<K, dr>
    def Ops.add(+K: Type, f: K -> K -> K, x: K, y: K) -> K

all fail with `expected : Data / observed : Type`, located at the def. Def parameters
must be data values, so bend has no type parameters and no function parameters: no
dictionaries, no type classes. Dependent parameter types are fine (`u: LB.Elem(d)` checks
in round twenty-five's P1 -- the error there was in the body), so it is specifically the
*type-valued* and *function-valued* parameters that are impossible.

**What that settles.** Operations have to be dispatched on a *value*, which is what
route B's level family does. The radicand can therefore be a type index or a value, never
both, and the carrying design (round twenty-five) is not a preference but the only
expressible shape: the radicand rides in the data, and the family supplies the operations
for the level below. Its one accepted cost stands -- two elements claiming different
radicands are *unprovable*, not *untypeable*.

Worth stating precisely, because it bounds the search: elements at *different levels* are
already untypeable under route B, since the Ext case is indexed by the radicand tower
(`Elem.Ext<d>`). The residual hole is narrower than it sounds -- two different elements
representing the *same* radicand, at the same index. Pinning the carried field to its
index is exactly the embedding, which fails at the cross-radicand step
(`expected : Elem(d) / observed : Elem(re)`, P2). Indexing the element by the radicand
*element* instead would need a def generic in that element's type -- measured impossible
above. So the residual hole is structural in bend as it stands, not an oversight in the
design. Closing it needs either an upstream bend feature or a working embedding; the
embedding fails only in the Ext case, and for a *base* radicand it is trivially
available (`Base{v} -> EBase{v}`), which is why a nested-radicand chain is the case that
needs it.


**And the safety claim holds, at concrete indices (measured).** A dependent index is
legal -- `type EC.Ext<-K: Data, -dr: K>` -- and two elements claiming different radicands
of the same coefficient ring cannot be passed to one operation:

    def EC.op(x: EC.Ext<EC.Base<0n>, ECBase{0n}>, y: EC.Ext<EC.Base<0n>, ECBase{0n}>)

    Error:
    - expected : EC.Ext<EC.Base<0n>, ECBase{0n}>
    - observed : EC.Ext<EC.Base<0n>, ECBase{1n}>

with the control (agreeing radicands) printing `All terms check.` So radicand-as-index
does deliver untypeability. The catch is that it cannot be stated for all levels: a def
generic in the coefficient type is impossible (P3/P4 above), which means the design
covers one concrete ring at a time and cannot cover a tower of unbounded depth. That is
why the carrying design stands, and the residual hole is the price of covering the tower
at all.


### The embedding and typed arithmetic are mutually exclusive (round twenty-seven)

Round twenty-five's P2 showed the embedding `Elem.of(t) : Elem(t)` failing with
`expected : Elem(d) / observed : Elem(re)`. That failure turns out to depend entirely on
which index keys the Ext fields, and the two choices give the two horns of a dilemma.

**Key the fields by the tower's own coordinates and the embedding works.** With

    type ET.Ext<-A: Data, -B: Data, -D: Data> is Data:
      EExt{u: A, w: B}

    def ET(t: T.Tower) -> Data:
      match t:
        case T.Base{v}: ET.Base<v>
        case T.Ext{re, im, d}: ET.Ext<ET(re), ET(im), ET(d)>

the embedding, `add`, and a hypothesis-free ring statement all check in one file:

    def ET.of(+t: T.Tower) -> ET(t):
      match t:
        case T.Base{v}: EBase{v}
        case T.Ext{re, im, d}: EExt{ET.of(re), ET.of(im)}

    law ET.add.comm:
      for +t: T.Tower
      for +x: ET(t)
      for +y: ET(t)
      {ET.add(t, x, y) == ET.add(t, y, x) : ET(t)}

`def ET.add` recurses on the coordinate towers with no radicand parameter at all. The
file reports `241 TODOs` = the 240 of `src/tower.bend` plus the one unfilled law, so
every definition typechecks and the statement is legal -- the first place in bend where a
ring law at a *variable* tower level needs no agreement hypothesis, which is exactly what
round twenty-five's carrying design could not do (`add.comm` is false there, P5).

**Key them by the radicand and the embedding fails, precisely as before.** The variant
with `EExt{u: D, w: D}` -- both coordinates in the ring at the radicand's level, which is
what arithmetic needs -- fails at the embedding:

    Error:
    - expected : ET2(d)
    - observed : ET2(re)
    Location: ET2.of

**And the first variant cannot multiply.** `mul` on it dies on the cross-coordinate term,
not on the radicand at all:

    Error:
    - expected : probe.tower.e1.ET(re)
    - observed : probe.tower.e1.ET(im)
    Context:
    - u1 : probe.tower.e1.ET(re)
    - w1 : probe.tower.e1.ET(im)

`w1 * w2` is at index `ET(im)` while its target is `ET(re)`. Typed arithmetic needs both
coordinates keyed by the *same* type -- the coefficient ring -- and that is exactly the
indexing that makes the embedding unprovable.

**Why the dilemma is structural.** In a tower `Ext{re, im, d}` the three fields are three
separate towers at the same level, with no shared index and no way to state that they are
at the same level: `Tower.depth` is a function, not a type index, and bend has no
equality on types to transport along. So the checker can never see `ET(re) = ET(d)`, and
the typed route must give up either the embedding or the arithmetic. Route A's untyped
tower is what makes the arithmetic work -- everything is one type -- and that is why
typing it buys no safety here. The level and radicand discipline has to be carried by
*proofs* (Step 1's `Tower.wf` evidence, which is already an indexed type over dependent
tower indices: `Tower.Wf.Ext<-re, -im, -d>`), not by types.

The constructive finding worth keeping: the `ET` family, indexed by the whole triple, is
a sound base for the parts of the ring that never touch the radicand -- `add`, `neg`, and
their laws are stateable at a variable level with no hypothesis, and the statement above
is the first one measured in bend. `mul` is the operation that needs the radicand to
cross between levels, and that is the operation the typed route cannot have.


### The typed base carries provable laws (round twenty-eight)

Round twenty-seven left one question: the three-index `ET` family makes a hypothesis-free
ring law *stateable* at a variable tower level, but can it be *proved*? It can, with the
`Rat.add_comm` recipe and nothing else -- one `Equal.cong` per coordinate composed by
`Equal.trans` with the middle endpoint spelled out:

    def ET.add.comm(t, x, y):
      match t:
        case T.Base{v}:
          EBase{+a} = x
          EBase{+b} = y
          Equal.cong(R.Rat, ET.Base<v>, u => EBase{u},
            R.Rat.add(a, b), R.Rat.add(b, a), R.Rat.add_comm(a, b))
        case T.Ext{re, im, d}:
          EExt{+u1, +w1} = x
          EExt{+u2, +w2} = y
          Equal.trans(ET.Ext<ET(re), ET(im), ET(d)>,
            EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)},
            EExt{ET.add(re, u2, u1), ET.add(im, w1, w2)},
            EExt{ET.add(re, u2, u1), ET.add(im, w2, w1)},
            Equal.cong(ET(re), ET.Ext<ET(re), ET(im), ET(d)>,
              u => EExt{u, ET.add(im, w1, w2)},
              ET.add(re, u1, u2), ET.add(re, u2, u1), ET.add.comm(re, u1, u2)),
            Equal.cong(ET(im), ET.Ext<ET(re), ET(im), ET(d)>,
              u => EExt{ET.add(re, u2, u1), u},
              ET.add(im, w1, w2), ET.add(im, w2, w1), ET.add.comm(im, w1, w2)))

**The count is the evidence.** With the fill the file reports `Error: 11 TODOs found.` --
exactly `src/tower.bend`'s own eleven laws, because importing
`./src/rat_proofs.bend as RP` fills rat's 229 and the definition above fills mine. The
unfilled version of the same file read 241 (round twenty-seven); an unattached fill here
would read 12.

**Negative control.** Returning the first `Equal.cong` alone, without the `Equal.trans`
wrapper, is rejected as a type error rather than a syntax error, so the checker is really
checking this fill instead of accepting it vacuously:

    Error:    - expected : {EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)} == EExt{ET.add(re, u2, u1), ET.add(im, w2, w1)} : ET.Ext<ET(re), ET(im), ET(d)>}    - observed : {EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)} == EExt{ET.add(re, u2, u1), ET.add(im, w1, w2)} : ET.Ext<ET(re), ET(im), ET(d)>}    Context:    - re : src/tower.Tower    - im : src/tower.Tower    - d  : src/tower.Tower    - u1 : ET(re)

**The direct form suffices.** A variant routing the injected element through a
declared-return-type helper (`def ET.Ext.at(+re, +im, +d: T.Tower, u: ET(re), w: ET(im))
-> ET.Ext<ET(re), ET(im), ET(d)>`) and spelling all three `trans` endpoints through it
also gives 11, so both spellings pass. That matches round twenty-four: on indexed types the
`%`-ascriptions are what fail, and direct terms avoid the wall.

**What it means.** The radicand-free half of the ring is fully available in the typed
setting -- `add` has a law at a variable tower level with no agreement hypothesis, stated
and proved, and `neg` follows the same recipe (`EExt{ET.neg(u), ET.neg(w)}` never touches
the radicand). `mul` remains the operation that needs the radicand to cross a level, and
it remains impossible (round twenty-seven P3). The plan stands: route A for the
arithmetic, `Tower.wf` evidence for the level and radicand discipline, with the `ET` base
as a real asset if a hybrid development is ever wanted.


### The witnessed route A has no teething: evidence is inert and the mismatch value is indistinguishable (round twenty-nine)

Round twenty-seven concluded that the level and radicand discipline would have to be
carried by proofs, and Step 1's `Tower.wf` evidence looked like the machinery for it.
Measured, it is not -- for three independent reasons.

**The evidence cannot be eliminated inside an operation.** Matching the evidence first,
then the tower it is evidence about:

    def T.Tower.head(+x: T.Tower, wx: T.Tower.wf(x)) -> T.Tower:
      match wx:
        case T.WfExt{wfre, wfim, wfd}:
          match x:
            case T.Ext{re, im, d}:
              re

    Error:
    - message  : a match on a parameter or field (this name is a def or a consumed binder:
                 give the value its own def)

and the natural ordering fares no better -- matching the tower first, so that the evidence
*should* reduce, then the evidence:

    case T.Base{a} T.Base{b}:
      match wx wy:
        case T.TowerOk{} T.TowerOk{}:
          T.Base{R.Rat.add(a, b)}

    Error:
    - message  : a match on a parameter or field (this name is a def or a consumed binder:
                 give the value its own def)

The mechanism is the stuck-term wall this project keeps meeting: the scrutinee's type
`Tower.wf(x)` never reduces for a variable `x`, so the evidence is inert. It can be taken
as a parameter, and a *law* may quantify it -- `law ... for +x: T.Tower; for +wx:
T.Tower.wf(x)` reports 241 TODOs = `tower.bend`'s 240 plus the one law, so the statement is
legal -- but it can never drive a dispatch. Evidence is for statements, not for operations.

**Well-formedness is orthogonal to level agreement anyway.** Two towers can both be
perfectly well-formed and still be at different levels, so the evidence could not exclude
the mismatch even if it could be eliminated. The property that would matter is "x is at
`d`'s level", which is a *proof obligation* about depth, not a data witness.

**And the mismatch value is indistinguishable from a correct one.** The mixed arms return
`Tower.zero(d)`, which by the landed `depth.zero` law has depth `1 + depth(d)` -- exactly
the depth a correct sum at that level has. It is a legitimate element of the claimed ring,
so no theorem phrased about *values* can call it wrong. Depth does not separate them, and
nothing else does either.

**What that leaves.** The only mechanism in bend that removes the silent-wrong-answer
hazard is failing loudly: a distinguished marker returned by the mixed arms, which every
consumer must handle explicitly because matching on `Tower` becomes non-exhaustive until
it does. The measured cost is bounded -- 31 match/case sites in `src/tower.bend` and 3 in
`src/tower_proofs.bend`, and no other file in the repo matches on `Base`/`Ext` (the
interval fast path of Step 4 would be the next consumer). What it buys is that a
wrong-level call cannot flow silently into a coordinate: reading a coordinate requires
matching, and the marker forces a branch there.

A theorem should ride with it -- well-formed, same-level inputs never produce the marker --
and the absurdity machinery for that is in the library: `law lt_ne_eq: for e: {LT{} == EQ{} :
Cmp}; Empty`, `gt_ne_eq`, `lt_ne_gt`, `Empty.absurd(-A: Type, e: Empty) -> A`, with
`Nat.cmp` computing on literal zeros. **Proved.** The bridging lemma is real, with no laws of its own in the file:
`All terms check.` So the absurdity machinery is available end to end:
`Empty.absurd`, `lt_ne_eq`, `gt_ne_eq`, `Equal.sym`, `Equal.cong`, and `Nat.cmp`
computing on literal zeros.

The recommended change, which alters the landed public API and so is the user's call: add
the marker constructor, return it from the four mixed arms, define `depth` and `wf` on it,
and prove the unreachability theorem. The weaker alternative, if the API should stay put,
is to keep the convention and rely on `depth` invariants at the consumer boundary.


### Failing loudly is cheap, and it catches a second silent zero (round thirty)

The marker design was probed by generating a copy of `src/tower.bend` with the change
applied textually -- the real type, operations, helpers and laws -- so what is measured is
the actual code plus the change.

**Two markers, because there are two failure modes.** `Bad{}` from the four mixed-shape
arms (two in `add`, two in `mul`), and `Fuel{}` from `mul`'s `case 0n:` arm. That second
site is a finding about landed code: `mul` is fuel-driven, and an exhausted fuel returned
`Tower.zero(d)` -- a plausible zero, silently, decided by a caller-supplied Nat. The plan
listed "a law proving that enough fuel never runs out" as Step 2's business, but not that
running out of fuel was silent. Two markers keep the diagnoses apart, and the
fuel-sufficiency law becomes the unreachability statement for `Fuel`.

**Every match on Tower must grow, and wildcards bound the growth.** The checker reports
`expected : cases for Bad, Fuel` one definition at a time. Eight sites needed arms:
`depth`, `zero`, `add`, `neg`, `mul`, `one`, `wf`, and the proof helper `Tower.wf.zero` --
which is a `wf` helper, so its arms return evidence (`TowerOk{}`, since `wf(Bad{})` is
`Tower.Ok`) rather than the marker. `Tower.wf.lift` needed nothing. A binary match would
otherwise need sixteen constructor combinations, but bend has wildcards -- a minimal probe
with `case _ _:` prints `All terms check.` -- so `add` keeps its two matching arms plus
`case _ _: Bad{}`, and `mul` uses `Fuel{} _`, `_ Fuel{}`, `_ _` to propagate the diagnosis
instead of flattening it. Net cost: about nine arm edits in `src/tower.bend`.

**The statements survive.** The generated file checks -- its only output is a TODO count,
no error -- so every definition, both helper proofs, and all eleven copied law *statements*
remain legal under the marker. The count is 111 with this import set, and it is exactly explained: nat contributes
129 laws and nat_proofs fills every one of them, so a control probe importing nat,
nat_proofs and rat with no laws of its own reports 100 -- rat's 229 minus nat's 129 --
and the probe's eleven copied laws bring it to 111. src/tower.bend alone reports
240 = rat's 229 plus its own eleven. So the number tracks unfilled laws in the import
graph and nothing about the change. Note what this does *not* measure: the fills live in
`src/tower_proofs.bend` and were not copied, so this is the statements' legality and the
operations' typechecking, not a re-proof that the laws still hold.

**The unreachability machinery works end to end.** A discriminator `Tower.tag` (`Base`/`Ext`
to `0n`, `Bad` to `1n`, `Fuel` to `2n`) plus round twenty-nine's absurdity lemma proves one
case:

    def Tower.bb.not.bad(+d: Tower, +v: R.Rat, +w: R.Rat,
        e: {Tower.add(d, Base{v}, Base{w}) == Bad{} : Tower}) -> Empty

The full theorem is four such cases. It carries a hypothesis -- the operands have equal
depth -- which is what makes the mixed cases absurd. So it certifies "same-level inputs
never see the marker", while the discipline of *passing* same-level operands remains a
caller obligation rather than something the type system enforces.


### The safety theorems land: clean in, clean out (round thirty-two)

The two laws that turn the markers from a loud failure into a proved-never-happens for
correct callers are on `main` and filled.

**The predicate.** `Tower.clean(t) -> Data` is marker-free evidence: `Tower.Clean` at a
Base, `Tower.Clean.Ext<re, im, d>` at an Ext, and `Empty` at `Bad` or `Fuel`. Because the
Ext case demands evidence for its parts recursively, evidence for a computation *is* a
proof that no marker appears anywhere inside it, not merely that none is at the top.

**The laws.**

    law Tower.add.depth:   ... {Tower.depth(Tower.add(d, x, y)) == Tower.depth(x) : Nat}
    law Tower.add.clean:   ... Tower.clean(Tower.add(d, x, y))

both under `for hd: Tower.clean(d)`, `hx: Tower.clean(x)`, `hy: Tower.clean(y)` and
`h: {Tower.depth(x) == Tower.depth(y) : Nat}`.

**What the fills forced, all measured.**

- The predicate had to carry `hri: {depth(re) == depth(im)}`. The first attempt was
  unprovable for a plain reason: `depth` reads only the re slot, so an Ext/Ext call's im
  coordinates have no depth relation to induct with. That is round twenty-nine's conclusion
  -- the level discipline has to live in the evidence -- made concrete.
- A field relating the coordinates to the *radicand* is deliberately absent. Nothing in a
  tower relates an operand's own radicand to the caller's `d`, and `add` never recurses
  into `d`, so such a field is neither derivable nor needed. Tying `d` to the operands'
  level stays the caller's obligation.
- `succ_add_ne`'s instantiated parameter type does not match the natural spelling up to the
  checker's comparison, so the mixed-shape arms use round twenty-nine's route instead:
  `Nat.cmp` for discrimination plus `eq_ne_gt` / `gt_ne_eq`.
- The mixed arm's goal type is `{0n == 1n+depth(rx)}`, not the reverse: the result there is
  `Bad`, whose depth is `0n`.
- Linearity: `hd` is used five times in the clean fill's Ext/Ext branch, so it is marked
  `+hd` on the *law's* `for` list; a fill inherits those marks positionally.

**Shape of each fill**: eight arms. Four shape arms -- Base/Base is definitional; Ext/Ext is
the induction, with the re relation recovered by `succ_inj` and the im relation assembled
from the evidence's `hri` fields; the two mixed arms are absurdity from the equal-depth
hypothesis. Four marker arms hand the marker's own evidence to `Empty.absurd`, naming their
goal type because `add(d, Bad{}, y)` does not reduce when `y` is still a variable.

**The fuel obligation, stated but not landed.** With strictly more fuel than the operands'
depth, `mul` does not run out:

    law ... Tower.clean(Tower.mul(f, d, x, y))
      for hf: {Nat.cmp(Tower.depth(x), f) == LT{} : Cmp}

Its statement checks (243 = tower's 242 plus one, measured in a throwaway file, since an
unfilled law would leave the proofs gate red). Its fill is a nat-inequality induction -- the
recursive calls need `depth(rx) < g` from `1+depth(rx) < 1+g`, which is what the library's
`cmp_lt_succ_r`-family laws are for -- and that is the next unit. `neg` and `one` were left
alone under the goal's "if cheap": `neg`'s Ext case needs `{depth(neg(rx)) == depth(neg(ix))}`,
i.e. a depth law for `neg` first.

**Gates after the change.** All six proof files print `All terms check.`; counts are nat 129,
int 32, qext 34, rat 229, qrat 265, tower 242 (240 plus the two safety laws -- the predicate
and its evidence types add no laws); `probe.bend` and `probe.payoff.bend` check and
`scratch.bend` still prints its inversion triple.

**What this does and does not buy.** It proves that a caller who supplies clean operands at
equal depth cannot receive a marker at any depth -- so no silent zero can enter the pipeline
from a level mismatch or an exhausted fuel. The hypotheses themselves are obligations bend
cannot express as types, so the guarantee is about *correct* callers; a caller who passes
operands of unequal depth gets `Bad` and is forced to say what it does with it.


### The fuel obligation splits, and its extension case surfaces the radicand question (round thirty-three)

**The base shape is landed and proved.** Two rational elements need no structure to
multiply, so one step of fuel always suffices and the radicand is never touched:

    law Tower.mul.fuel.base:
      for +g: Nat
      for +d: Tower
      for a: R.Rat
      for b: R.Rat
      Tower.clean(Tower.mul(1n+g, d, Base{a}, Base{b}))

The fill is `T.CleanOk{}` -- `mul`'s successor arm takes the Base/Base branch and returns
`Base{Rat.mul(a, b)}`, which is clean by definition.

**The extension shape is blocked, and the reason is not fuel arithmetic.** Stating the law
the way `add.clean` is stated -- clean operands at equal depth, the operand one level above
the radicand (`hrd: {depth(x) == 1n + depth(d)}`), strictly more fuel than `depth(x)` -- puts
the recursion in a corner. `mul`'s Ext/Ext arm calls `mul(g, d, rx, ry)`, whose operands sit
at the level *below* x. The caller's `hrd` says `1n + depth(rx) == 1n + depth(d)`, so `rx` and
`d` are at the *same* depth -- siblings, not parent and child -- and the sub-level call
therefore needs a hypothesis about `rx`'s own radicand, one level further down, which the
statement does not supply. Measured, as a small lemma asking for exactly that:

    def T.Tower.hrd.down(+d, +rx, +ix, +dx: T.Tower,
        hrd: {T.depth(T.Ext{rx, ix, dx}) == Nat.add(1n, T.depth(d)) : Nat})
      -> {T.depth(rx) == Nat.add(1n, T.depth(d)) : Nat}:
      N.succ_inj(T.depth(rx), T.depth(d), hrd)

    Error:
    - expected : {src/tower.Tower.depth(rx) == 1n+src/tower.Tower.depth(d) : Nat}
    - observed : {src/tower.Tower.depth(rx) == src/tower.Tower.depth(d) : Nat}
    - hrd : {1n+src/tower.Tower.depth(rx) == 1n+src/tower.Tower.depth(d) : Nat}

Three things follow, and they are not the same thing:

1. *Measured*: the hypothesis the recursion needs is not derivable from the caller's.
2. *Reasoned, not measured*: the radicand of a sub-level multiplication is the sub-level's
   own, which is not `d`. `mul` threads `d` unchanged through every recursive call, so at
   depth two or more the `sqrt(d) * sqrt(d) = d` term multiplies coefficients by the
   *caller's* radicand rather than the level's. That is the same radicand-chain wall rounds
   twenty-six and twenty-seven hit in the typed designs, showing up here in the untyped one.
3. *Untested*: whether `mul`'s values are actually wrong for nested towers. A proof
   obstruction is not a semantics proof -- the statement I chose may simply be the wrong
   shape -- and that is what the next unit tests: multiply two depth-2 towers with rational
   coefficients whose product is known by hand and compare the printed value, the way
   `scratch.bend` checks the inversion triple.

Until that test runs, `mul` should be treated as verified for depth-1 towers only. If it
needs its radicand threading changed, `mul.ext`'s statement and the fuel obligation both
restate with it.


### Depth-2 multiplication was broken, and the markers made it visible (round thirty-four)

The numeric test the fuel obstruction pointed at: level 1 lives in Q(sqrt 5), a level-1 tower
being `Ext{p, q, Base{5}}` for `p + q*sqrt(5)`; level 2 extends that by `sqrt(D)` where D is
the level-1 element 2, so a level-2 element is `Ext{R, I, D}` for `R + I*sqrt(2)`. The control
multiplies `sqrt(5)` by itself at level 1. The test multiplies `sqrt(5) + sqrt(2)` by itself.
`main` returns all three values -- control, product, hand-computed expectation -- so the runner
prints them side by side.

**Before the fix**: control `Ext{Base{5}, Base{0}, Base{5}}` = 5, correct. Product
`Ext{Ext{Bad{}, Bad{}, D}, Ext{Bad{}, Base{2}, D}, D}` -- `Bad` where the answer should be.
Expectation `Ext{Base{7}, Ext{Base{0}, Base{2}, Base{5}}, D}`, i.e. `7 + (2*sqrt(5))*sqrt(2)`.

So `mul` could not multiply depth-2 elements at all, and the markers are what made that
visible: before round thirty-one the same call returned `Tower.zero(D)`, a perfectly plausible
ring element, and nothing downstream would have noticed.

**Diagnosis.** `mul`'s Ext/Ext arm handed the *level-k* radicand to level-(k-1)
multiplications -- both as the parameter the recursion threads and, through it, as the
radicand the coordinates' own recursions would use. At depth 2 those coordinates are rationals
and the level-1 radicand is a rational too, but the value passed was D, a level-1 tower, so the
operands of the coordinate multiplication sat at different depths and the mixed-shape arm
fired.

**Fix** (`mul-radicand-threading`):

- `Tower.rad(t)` reads a level's radicand off an operand: `d` for `Ext{re, im, d}`, and `t`
  itself for a Base, a dummy that is never read because a Base/Base multiplication takes no
  radicand. It is a function of the operand, so the recursion descends without a caller
  having to thread a chain of radicands -- the thing rounds twenty-six and twenty-seven
  could not do in the typed designs.
- The recursive calls in `mul`'s and `add`'s Ext/Ext arms pass `Tower.rad(...)` in the
  radicand *slot*. The `sqrt(d)*sqrt(d) = d` term's second operand stays the caller's `d`,
  which is correct: it is the level's own radicand, and the caller supplies it. The result's
  third field stays `d` too.
- `add`'s parameters become `(x, y, +d)`. The termination check wants each argument unchanged
  until one shrinks, and `add(Tower.rad(rx), rx, ry)` changed the first argument before the
  second shrank; with the operands first, `add(rx, ry, Tower.rad(rx))` is accepted.
- `add.ext` and `mul.ext` restate to the new unfoldings, and `add.base`, `add.depth`,
  `add.clean` reorder their `for` lists to match.

One mistake worth recording: the first attempt also replaced the `sqrt(d)*sqrt(d) = d` term's
operand with `Tower.rad(rx)`. The control caught it -- `sqrt(5)*sqrt(5)` came out as
`Ext{0, 0, 5}`, i.e. zero -- because at level 1 that operand is the rational 5 while
`rad(Base{0})` is 0. Reverted.

**After the fix**, printed values: control `Ext{5, 0, 5}`; product `Ext{Ext{7, 0, 5},
Ext{0, 2, 5}, Ext{2, 0, 5}}`; expectation identical to the product. Depth-2 arithmetic is
correct.

**Still open on the branch.** `src/tower_proofs.bend` is red until its fills follow the new
signatures: the parameter orders are mechanical, but `add.clean`'s Ext/Ext arm now needs clean
evidence for `Tower.rad(rx)`, which is a function of a variable operand and therefore needs the
fill to match on the coordinates' shape as well. `main` is untouched and the law statements
themselves are unchanged apart from the reordering.

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
