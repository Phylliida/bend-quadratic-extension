import Base
import ./rat.bend as R
import ./rat_helpers.bend as RH

# The tower
# =========
#
# Step 1 of TOWER-PLAN: the element type and the structural machinery every later
# step stands on. An element is a value of the tower itself -- Base{value} is a
# rational, and Ext{re, im, d} is re + im*sqrt(d) with re, im and d all elements
# of the level below -- so an element's shape *is* its level.
#
# depth is an element's level. zero is the additive identity at that level, built
# recursively and keeping its radicand slot, which makes it linear in the
# radicand's depth. lift embeds a level-k element into level k+1: the element
# keeps its value and sits in the re slot, because that slot holds level-k
# elements. That one move is what lets every later law work at a common depth.
#
# wf is the structural half of well-formedness: at every Ext the three parts are
# themselves well formed. The arithmetic half -- a radicand positive, levels
# reduced -- is carried as hypotheses by the laws that need it, the way the
# depth-1 QExt laws carry positivity evidence, because ordering does not exist
# until the level operations land in Step 2. The choice is deliberate and is the
# risk TOWER-PLAN flags: too weak and Step 2 carries side conditions everywhere,
# too strong and lift cannot be stated.

type Tower is Data:
  Base{value: R.Rat}
  Ext{re: Tower, im: Tower, d: Tower}
  # The two failure markers. Bad is a call whose operands sit at different
  # levels -- there is no ring holding both, so no ring element describes the
  # result. Fuel is a call whose fuel ran out before the structure did. Neither
  # is a ring element: both propagate through the operations unchanged, depth
  # gives them 0n because they have no level, and wf accepts them structurally.
  # Making them constructors rather than a plausible zero is the point: reading
  # a coordinate out of a tower requires matching on it, so every consumer has
  # to say what it does with a failure instead of silently receiving a number.
  Bad{}
  Fuel{}

def Tower.depth(t: Tower) -> Nat:
  match t:
    case Base{v}:
      0n
    case Ext{re, im, d}:
      1n+Tower.depth(re)
    case Bad{}:
      0n
    case Fuel{}:
      0n

def Tower.zero(t: Tower) -> Tower:
  match t:
    case Base{v}:
      Base{R.Rat.zero()}
    case Ext{re, im, d}:
      Ext{Tower.zero(re), Tower.zero(im), d}
    case Bad{}:
      Bad{}
    case Fuel{}:
      Fuel{}

def Tower.lift(+t: Tower, d: Tower) -> Tower:
  Ext{t, Tower.zero(t), d}

# The radicand of the level an operand sits at
# ============================================
#
# A multiplication at level k needs the level's own radicand. For an operand
# Ext{re, im, d} at level k that is d, and the *coordinate* level below k has a
# different one -- the radicand stored inside the coordinates -- which is what the
# depth-2 test of round thirty-four caught: the recursion was handing the level-k
# radicand to a level-(k-1) multiplication, whose operands then sat at different
# depths and came back as Bad. Each operation therefore reads the radicand off the
# operand it is descending into (dx, the first operand's own third field), so the
# recursion descends without the caller threading a chain of radicands.

# One level's arithmetic, generically
# ===================================
#
# The radicand is *intrinsic*: it is what the result's third field records, and
# every operation takes it from its first operand rather than from a parameter.
# Round thirty-nine landed that -- the explicit-parameter design of round
# twenty-two needed a side condition at every call, and retiring it let add and mul
# share one evidence type -- and what it costs is recorded here.
#
# A call that mixes a Base with an Ext returns Bad, not a plausible zero: two
# operands of different *shapes* are not a value of the theory. Radicand
# disagreement is a different matter and this definition does not detect it: add
# and mul compare shapes, not radicands, so two Ext operands that agree in shape
# but not in level combine silently, and the result takes its radicand from the
# first. Round forty-six measured exactly that (the swap of two depth-1 values with
# radicands 2 and 3 differs in the third field alone), and the consequence is that
# the level discipline is not the definition's to enforce but the *laws'*: a law
# that states an operation on two operands needs evidence that they sit at one
# level, and a caller who cannot state it never builds the value.
#
# The marker arms are last, after the matching ones, so they cannot swallow a
# legitimate call; a marker operand propagates its own marker. No law reaches any
# of them.
#
# mul reduces with sqrt(d) * sqrt(d) = d: the im*im term is multiplied by d, an
# element of the level below, exactly as the depth-1 QExt.mul does.

def Tower.add(x: Tower, y: Tower) -> Tower:
  match x y:
    case Base{a} Base{b}:
      Base{R.Rat.add(a, b)}
    case Ext{rx, ix, dx} Ext{ry, iy, dy}:
      Ext{Tower.add(rx, ry), Tower.add(ix, iy), dx}
    case Fuel{} _:
      Fuel{}
    case _ Fuel{}:
      Fuel{}
    case _ _:
      Bad{}

def Tower.neg(x: Tower) -> Tower:
  match x:
    case Base{a}:
      Base{R.Rat.neg(a)}
    case Ext{rx, ix, dx}:
      Ext{Tower.neg(rx), Tower.neg(ix), dx}
    case Bad{}:
      Bad{}
    case Fuel{}:
      Fuel{}

# Tower.sub: x - y = x + (-y). The definition, exactly as Rat.sub is, so its twin
# below is a definitional equality rather than an arithmetic fact.
def Tower.sub(x: Tower, y: Tower) -> Tower:
  Tower.add(x, Tower.neg(y))

# mul is fuel-driven, and it has to be. bend checks that a self-call decreases --
# "arguments are read left to right: each passed unchanged until one shrinks" --
# and the sqrt(d)*sqrt(d) = d term needs im*im multiplied by d, which nests one
# self-call inside another's argument. Neither a let-bound intermediate nor the
# operand order fixes that (both measured: rejected); descending on a Nat fuel
# does, which is the same shape base's own Nat.gcd takes. Callers pass a fuel of
# at least the operands' depth; a law proving that enough fuel never runs out is
# Step 2's business, not the definition's. Running out returns Fuel, a separate
# diagnosis from Bad: it says the caller's fuel was too small, not that the
# operands disagreed about their level.

def Tower.mul(+f: Nat, x: Tower, y: Tower) -> Tower:
  match f:
    case 0n:
      Fuel{}
    case 1n+g:
      match x y:
        case Base{a} Base{b}:
          Base{R.Rat.mul(a, b)}
        case Ext{+rx, +ix, +dx} Ext{+ry, +iy, +dy}:
          Ext{Tower.add(Tower.mul(g, rx, ry), Tower.mul(g, Tower.mul(g, ix, iy), dx)),
              Tower.add(Tower.mul(g, rx, iy), Tower.mul(g, ix, ry)),
              dx}
        case Fuel{} _:
          Fuel{}
        case _ Fuel{}:
          Fuel{}
        case _ _:
          Bad{}

def Tower.one(t: Tower) -> Tower:
  match t:
    case Base{v}:
      Base{R.Rat.one()}
    case Ext{re, im, d}:
      Ext{Tower.one(re), Tower.zero(im), d}
    case Bad{}:
      Bad{}
    case Fuel{}:
      Fuel{}

# the type of well-formedness evidence at one tower, with the evidence for the
# parts as its fields, so a law can take `for h: Tower.wf(t)` as a hypothesis
type Tower.Ok is Data:
  TowerOk{}

type Tower.Wf.Ext<-re: Tower, -im: Tower, -d: Tower> is Data:
  WfExt{wfre: Tower.wf(re), wfim: Tower.wf(im), wfd: Tower.wf(d)}

def Tower.wf(t: Tower) -> Data:
  match t:
    case Base{v}:
      Tower.Ok
    case Ext{re, im, d}:
      Tower.Wf.Ext<re, im, d>
    case Bad{}:
      Tower.Ok
    case Fuel{}:
      Tower.Ok

# Well-formedness evidence is an *indexed* type, so it does not survive a
# rewrite as an equation: Tower.wf(Tower.zero(t)) and Tower.wf(t) have different
# indices -- Tower.Wf.Ext<zero re, zero im, d> against Tower.Wf.Ext<re, im, d> --
# and no equation between them is true. What is true, and is what later laws
# actually need, is that the evidence *transports*: from evidence at t, evidence
# at zero(t). Both of the following are structural inductions in a type, which is
# the Step 0.2 recipe doing real work.
def Tower.wf.zero(t: Tower, h: Tower.wf(t)) -> Tower.wf(Tower.zero(t)):
  match t:
    case Base{v}:
      h
    case Ext{re, im, d}:
      WfExt{+wfre, +wfim, +wfd} = h
      WfExt{Tower.wf.zero(re, wfre), Tower.wf.zero(im, wfim), wfd}
    case Bad{}:
      TowerOk{}
    case Fuel{}:
      TowerOk{}

# at a lift, the evidence for the level-k element is the re slot, the zero
# transport fills the im slot, and the radicand arrives from the caller
def Tower.wf.lift(+t: Tower, d: Tower, +h: Tower.wf(t), hd: Tower.wf(d)) ->
  Tower.wf(Tower.lift(t, d)):
  WfExt{h, Tower.wf.zero(t, h), hd}

# The marker-free predicate
# ========================
#
# wf is structural: it asks that the parts are well formed, and the markers count
# as well formed. What the safety theorems need is stronger -- that a tower
# contains no marker anywhere -- and that is what clean is. Its evidence is Empty
# at a marker, so Tower.clean(t) is uninhabited exactly when t fails somewhere
# inside; a law that returns Tower.clean(add(d, x, y)) is therefore a proof that
# the computation produced no failure at all, not merely that it did not fail at
# the top.

type Tower.Clean is Data:
  CleanOk{}

# The Ext evidence carries marker-free evidence for each part plus one level
# relation. depth reads only the re slot, so without hri an induction has nothing
# to say about the im coordinates -- measured, not guessed: the first attempt at
# the safety law was unprovable for exactly that reason. hri says the two
# coordinates sit at one level.
#
# A relation between the coordinates and the radicand d belongs here too on
# paper, and it is deliberately absent: nothing in a tower relates an operand's
# own radicand to the caller's d, and add never recurses into d, so such a field
# is neither derivable nor needed. Tying d to the operands' level is the caller's
# obligation, which is the conclusion round twenty-nine reached about the level
# discipline generally.
type Tower.Clean.Ext<-re: Tower, -im: Tower, -d: Tower> is Data:
  CleanExt{cre: Tower.clean(re), cim: Tower.clean(im), cd: Tower.clean(d),
           hri: {Tower.depth(re) == Tower.depth(im) : Nat},
           hrd: {Tower.depth(re) == Tower.depth(d) : Nat}}

def Tower.clean(t: Tower) -> Data:
  match t:
    case Base{v}:
      Tower.Clean
    case Ext{re, im, d}:
      Tower.Clean.Ext<re, im, d>
    case Bad{}:
      Empty
    case Fuel{}:
      Empty

# The level-discipline witness: what two operands have to agree about before an
# operation that reads its radicand from the first operand may be commuted.
#
# Round forty-six measured why this is not a per-value fact. Tower.clean recurses
# on one operand and says nothing about a second one, and the swap of two depth-1
# values whose radicands are 2 and 3 is simply false -- the results differ in the
# third field alone. So the witness is a relation between two operands, in the
# shape route two of that round's fork measured: a *computed family* in the style
# of Tower.clean -- one type per pair of shapes, each with a single constructor,
# so a consume site destructures without a case split and the pairs that cannot
# agree get Empty.
#
# The Base case carries nothing: at the leaves the operands are Rats and the Rat
# laws are unconditional there. The Ext fields are indexed by the operands' own
# parts -- the family is applied to them directly, so no projection defs are
# needed, exactly as CleanExt's cre is typed by Tower.clean(re).
type Tower.Same.Base is Data:
  SameBase{}

type Tower.Same.Ext<-rx: Tower, -ix: Tower, -dx: Tower,
                     -ry: Tower, -iy: Tower, -dy: Tower> is Data:
  SameExt{sre: Tower.same(rx, ry),
          sim: Tower.same(ix, iy),
          sd: {dx == dy : Tower}}

# A wildcard operand does not do: the family is stuck on a variable, so every arm
# whose shapes disagree spells both of them out and reports Empty. Those arms
# close at the call site with Empty.absurd, the idiom the fills already use for
# the Bad and Fuel arms.
#
# A marker agrees with itself, which is why the two marker pairs take the trivial
# witness too. That is not an aesthetic choice: the operations are *total* even
# where they cannot do their job -- add of two Ext values whose levels disagree is
# Bad, mul below its fuel is Fuel -- so a closure law like "same(x, y) and
# same(u, v) gives same(add(x, u), add(y, v))" has to say something about the
# pairs where one side is a marker. Without these two arms the family is Empty
# there, and composition is unprovable at exactly the arms its induction needs.
def Tower.same(x: Tower, y: Tower) -> Data:
  match x y:
    case Base{a} Base{b}:
      Tower.Same.Base
    case Ext{rx, ix, dx} Ext{ry, iy, dy}:
      Tower.Same.Ext<rx, ix, dx, ry, iy, dy>
    case Bad{} Bad{}:
      Tower.Same.Base
    case Fuel{} Fuel{}:
      Tower.Same.Base
    case _ _:
      Empty

# Tower.Level<x, y>: x and y sit at the same level -- same shape, the same depth, and
# the same radicand at every step of the chain. It is deliberately weaker than
# Tower.same, which also relates a value's coordinates to each other (a cross pair).
# Level relates aligned pairs only, which is what makes it *reflexive*: its Ext arm is
# exactly the two recursive instances plus the radicand equation. Round fifty-three
# measured why that matters -- adding cross fields to Tower.same makes same(x, x)
# unprovable (probe.crossrefl.bend refused `expected : Probe.s4(rx, ix) / observed :
# Probe.s4(rx, rx)`), and same.of_eq, whose Ext arm ends at exactly that goal, dies
# with it.
#
# The Base case carries nothing, exactly as in Tower.same: two base values sit at the
# same level whatever Rat values they hold, because the Rat laws are unconditional at
# the leaves (Rat.add_comm, Rat.mul_comm).
type Tower.Level.Base is Data:
  LevelBase{}

type Tower.Level.Ext<-rx: Tower, -ix: Tower, -dx: Tower,
                      -ry: Tower, -iy: Tower, -dy: Tower> is Data:
  LevelExt{lre: Tower.level(rx, ry),
           lim: Tower.level(ix, iy),
           ld: {dx == dy : Tower}}

def Tower.level(x: Tower, y: Tower) -> Data:
  match x y:
    case Base{a} Base{b}:
      Tower.Level.Base
    case Ext{rx, ix, dx} Ext{ry, iy, dy}:
      Tower.Level.Ext<rx, ix, dx, ry, iy, dy>
    case Bad{} Bad{}:
      Tower.Level.Base
    case Fuel{} Fuel{}:
      Tower.Level.Base
    case _ _:
      Empty

# Safety: a clean call is a clean result
# ======================================
#
# Bad exists because two operands at different levels have no common ring, and
# Fuel because mul can be handed too little of it. This law is what makes those
# markers unreachable for a correct caller: given clean operands at equal depth
# the sum is clean, meaning no marker anywhere inside it, not merely absent from
# the top. The equal-depth hypothesis is what rules out the mixed-shape arms, and
# it is the caller's obligation -- bend cannot express "x is at d's level" as a
# type, which is why the hypothesis is a proposition rather than a signature.
# add preserves the level, and that is what lets the clean law build the level
# relations for its own result: the three fields of an Ext result get their
# relations from the depth of the coordinates that produced them.
# Depth needs no cleanliness. The marker arms of this law's fill used to take
# their Empty witness from clean hypotheses; spelling all sixteen arms out instead
# makes twelve of them definitional ({0n == 0n}) and leaves four that read the
# equal-depth hypothesis. That matters for mul: its depth proof calls this law on
# products of coordinates, whose cleanliness would otherwise require a whole
# separate safety law for mul.
law Tower.add.depth:
  for +x: Tower
  for +y: Tower
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  {Tower.depth(Tower.add(x, y)) == Tower.depth(x) : Nat}
law Tower.add.clean:
  for +x: Tower
  for +y: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  Tower.clean(Tower.add(x, y))

# The same two facts for a product
# ================================
#
# Stated as two laws because that is how a caller reaches for them, but they are
# one induction, and neither can be stated without the operand's cleanliness:
# mul recurses into a coordinate product times the radicand, so its recursive
# calls need clean evidence for a product, and its arms need the depths of the
# sub-products. The pair is proved together in Tower.mul.safe
# (tower_helpers.bend), where the cycle, the fuel sufficiency equation and the
# reason it is needed are all written out; these two laws are its projections.
#
# The fuel is `1n+Tower.depth(x)`: one level per operand, which is the fuel a
# caller has when x and y sit at the same level. At a smaller fuel the product
# is Ext{Fuel{}, Fuel{}, dx} and both of these are false, so the fuel is part of
# the statement rather than a parameter a caller may pick.
law Tower.mul.depth:
  for +x: Tower
  for +y: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  {Tower.depth(Tower.mul(1n+Tower.depth(x), x, y)) == Tower.depth(x) : Nat}
law Tower.mul.clean:
  for +x: Tower
  for +y: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  Tower.clean(Tower.mul(1n+Tower.depth(x), x, y))

# Fuel sufficiency at the bottom shape
# ===================================
#
# Two rational elements need no structure to multiply, so one step of fuel is
# always enough and the radicand is never touched. This is the base case of the
# obligation; the extension case is where the recursion has to descend a level,
# and that is a separate question (see TOWER-PLAN section 7, round thirty-three).
# zero at the bottom level is a zero
law Tower.zero.base:
  for v: R.Rat
  {Tower.zero(Base{v}) == Base{R.Rat.zero()} : Tower}
# zero does not change the level
law Tower.depth.zero:
  for +t: Tower
  {Tower.depth(Tower.zero(t)) == Tower.depth(t) : Nat}
# lift raises the level by exactly one
law Tower.depth.lift:
  for +t: Tower
  for +d: Tower
  {Tower.depth(Tower.lift(t, d)) == 1n+Tower.depth(t) : Nat}
# lift distributes over zero: the level operation zero survives the embedding
law Tower.lift.zero:
  for +t: Tower
  for +d: Tower
  {Tower.lift(Tower.zero(t), d) == Tower.zero(Tower.lift(t, d)) : Tower}

# Laws and defs share one namespace, so the shape well-formedness takes at a lift
# is stated by Tower.wf.lift's return type above rather than by a law naming it.

# The level operations at spelled forms. Each of these is the definition's own
# unfolding, stated so that later laws -- and callers -- can rewrite with it
# without re-deriving it; the ring laws that follow in Step 2 work by induction on
# top of exactly these.
law Tower.add.base:
  for a: R.Rat
  for b: R.Rat
  {Tower.add(Base{a}, Base{b}) == Base{R.Rat.add(a, b)} : Tower}
law Tower.add.ext:
  for rx: Tower
  for ix: Tower
  for dx: Tower
  for ry: Tower
  for iy: Tower
  for dy: Tower
  {Tower.add(Ext{rx, ix, dx}, Ext{ry, iy, dy})
   == Ext{Tower.add(rx, ry), Tower.add(ix, iy), dx} : Tower}
law Tower.neg.ext:
  for rx: Tower
  for ix: Tower
  for dx: Tower
  {Tower.neg(Ext{rx, ix, dx}) == Ext{Tower.neg(rx), Tower.neg(ix), dx} : Tower}
# Tower.sub_eq_add_neg: x - y = x + (-y) -- true by definition here, the same way
# Rat.sub_eq_add_neg is. It is the one law of the identity block that needs nothing
# of its operands: no evidence, no coefficient fact, no induction.
law Tower.sub_eq_add_neg:
  for +x: Tower
  for +y: Tower
  {Tower.sub(x, y) == Tower.add(x, Tower.neg(y)) : Tower}
law Tower.mul.base:
  for +g: Nat
  for a: R.Rat
  for b: R.Rat
  {Tower.mul(1n+g, Base{a}, Base{b}) == Base{R.Rat.mul(a, b)} : Tower}
# the sqrt(d) * sqrt(d) = d reduction, as the unfolding the plan asks for. Spelled
# at a successor fuel, since the definition matches on the fuel.
law Tower.mul.ext:
  for +g: Nat
  for +rx: Tower
  for +ix: Tower
  for dx: Tower
  for +ry: Tower
  for +iy: Tower
  for dy: Tower
  {Tower.mul(1n+g, Ext{rx, ix, dx}, Ext{ry, iy, dy})
   == Ext{Tower.add(Tower.mul(g, rx, ry), Tower.mul(g, Tower.mul(g, ix, iy), dx)),
          Tower.add(Tower.mul(g, rx, iy), Tower.mul(g, ix, ry)),
          dx} : Tower}
law Tower.one.base:
  for v: R.Rat
  {Tower.one(Base{v}) == Base{R.Rat.one()} : Tower}
law Tower.one.ext:
  for re: Tower
  for im: Tower
  for d: Tower
  {Tower.one(Ext{re, im, d}) == Ext{Tower.one(re), Tower.zero(im), d} : Tower}

# The commutativity laws need hs because add keeps the first operand's radicand:
# add(x, y) is Ext{add(rx, ry), add(ix, iy), dx}, so swapping is a claim about the
# radicand slot as well as the coordinates. mul_comm is deliberately not here
# yet: its Ext arm's third recursive call takes a *product* as an argument, so it
# needs a witness for values the law has not been given one for -- a composition
# law for this witness, which is the level discipline's preservation theorem.
# Tower.Pos: every Rat leaf of the value has a positive denominator.
#
# The coefficient half of the carrier. Round fifty-six measured that it cannot be
# derived: Rat.add_assoc.arb asks {Nat.cmp(0n, Rat.denof(a)) == LT{}} of each
# coordinate, Rat.denof(Rat{p, d}) is the field d, and Nat.cmp(0n, d) is stuck at a
# variable -- the general statement is false outright (Rat{Int{0n,0n}, 0n}). Positivity
# is a property of the *spelling* (Nat.cmp(0n, 1n+dp) is LT{} by {==}), and a law stated
# at variable coordinates has to be handed it.
#
# Hence a per-value family, like Tower.clean and unlike the pairwise Tower.Same:
# reflexivity is what a witness family needs to be usable, and the leaf facts
# propagate through the operations by Rat laws that already exist (Rat.add.den.pos,
# Rat.mul.den.pos, Rat.neg.den.pos, landed for the QExt rationalization).
#
# The marker arms are Pos.Marker rather than Empty, for round fifty-one's reason: the
# operations are total even where they cannot do their job, so a closure law's shape
# induction reaches Bad and Fuel results and has to say something there.
type Tower.Pos.Marker is Data:
  PosOk{}

type Tower.Pos.Base<-a: R.Rat> is Data:
  PosBase{pden: {Nat.cmp(0n, R.Rat.denof(a)) == LT{} : Cmp}}

type Tower.Pos.Ext<-re: Tower, -im: Tower, -d: Tower> is Data:
  PosExt{pre: Tower.pos(re), pim: Tower.pos(im), prad: Tower.pos(d)}

def Tower.pos(t: Tower) -> Data:
  match t:
    case Base{a}:
      Tower.Pos.Base<a>
    case Ext{re, im, d}:
      Tower.Pos.Ext<re, im, d>
    case Bad{}:
      Tower.Pos.Marker
    case Fuel{}:
      Tower.Pos.Marker

# Tower.Canon: every Rat leaf of the value is its own normal form.
#
# The coefficient carrier's other half. Rat.add_zero, Rat.zero_add, Rat.mul_one and
# Rat.one_mul are stated at Rat{n, d} with fx: {Rat.mk(n, d) == Rat{n, d}}, and no
# .arb version can exist: at a non-canonical value the equation is false outright --
# adding zero to Rat{Int{2n,0n}, 2n} normalizes to 1/1, which is not that value.
# Canonicality is a property of the spelling, exactly as positivity is, so the
# identity laws are handed it rather than deriving it.
#
# The leaf field is not the law's fx verbatim, because the family cannot destructure
# its own index: a pattern variable is not matchable ("give the value its own def").
# So the two things the fill cannot obtain any other way are what it carries -- the
# equation saying the value *is* its projection spelling, and fx at that spelling.
# Round sixty-four measured that this is enough: the fill rewrites the value to its
# spelling and hands fx to the Rat law.
#
# Round seventy-one gave the leaf a third field of the same kind. Rat.neg is not an
# involution at arbitrary values: it is mk(neg xn, xd), and mk normalizes, so at a
# non-canonical Rat the double negation lands on the canonical form rather than on the
# value. Rat.neg_neg is stated at a spelled, reduced Rat{Rat.num(np, nn), 1n+dp} with
# that spelling's coprimality as a hypothesis, and it has no .arb form, so the leaf
# fact is handed in with the other two -- neg(neg(a)) == a, which is exactly what
# Tower.neg_neg's Base arm needs.
#
# Marker arms are inhabited, like Pos's and for the same reason: the operations are
# total there and a closure law's shape induction reaches them.
type Tower.Canon.Marker is Data:
  CanonOk{}

type Tower.Canon.Base<-a: R.Rat> is Data:
  CanonBase{ce: {a == R.Rat{R.Rat.numof(a), R.Rat.denof(a)} : R.Rat},
            cfx: {R.Rat.mk(R.Rat.numof(a), R.Rat.denof(a)) == a : R.Rat},
            cneg: {R.Rat.neg(R.Rat.neg(a)) == a : R.Rat}}

# The Ext variant carries two more things: the level relation between the value's two
# coordinates, and the one between its first coordinate and the radicand. Those are the
# sibling facts the zero laws need -- `mul`'s second coordinate comes back as
# add(mul(g, rx, zero(iy)), mul(g, ix, zero(ry))) and add keeps its *first* operand's
# radicand, so the result carries rx's while the target zero(x) carries ix's. With
# level(rx, ix) the two agree. Round sixty-six measured the failure without it: the two
# sides differ in exactly one field.
#
# They live here rather than in Tower.Clean because Clean is *produced* -- add.clean,
# mul.clean and mul.safe must hand back a witness for a product -- and a product's
# radicand-slot obligation, level(mul(f, ix, iy), dx), is the wall round sixty measured.
# A carrier that no producer can fill is worse than a hypothesis the caller already has
# in hand. Canon is produced by nobody: it is handed in, like Pos.
type Tower.Canon.Ext<-re: Tower, -im: Tower, -d: Tower> is Data:
  CanonExt{cre: Tower.canon(re), cim: Tower.canon(im), cd: Tower.canon(d),
           lri: Tower.level(re, im),
           lrd: Tower.level(re, d)}

def Tower.canon(t: Tower) -> Data:
  match t:
    case Base{a}:
      Tower.Canon.Base<a>
    case Ext{re, im, d}:
      Tower.Canon.Ext<re, im, d>
    case Bad{}:
      Tower.Canon.Marker
    case Fuel{}:
      Tower.Canon.Marker

law Tower.add_comm:
  for +x: Tower
  for +y: Tower
  for hs: Tower.same(x, y)
  {Tower.add(x, y) == Tower.add(y, x) : Tower}

# The associativity of add, and the two carriers its coordinates need. The clean
# witness supplies the depth equations the induction consumes -- a per-value clean
# carries level(re, im), so depth(ix) == depth(iy) is in hand from x's and y's own
# witnesses plus the operand-level equation -- and the pos witness supplies the
# positivity of the Rat leaves that Rat.add_assoc.arb asks for. Both sides keep dx
# (add returns its *first* operand's radicand, and x is first on both sides), so
# unlike add_comm this law needs no level hypothesis at all.

law Tower.add_assoc:
  for +x: Tower
  for +y: Tower
  for +z: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for hz: Tower.clean(z)
  for px: Tower.pos(x)
  for py: Tower.pos(y)
  for pz: Tower.pos(z)
  for hxy: {Tower.depth(x) == Tower.depth(y) : Nat}
  for hyz: {Tower.depth(y) == Tower.depth(z) : Nat}
  {Tower.add(Tower.add(x, y), z) == Tower.add(x, Tower.add(y, z)) : Tower}

# x + (-x) = 0. Negation is coordinatewise and leaves the radicand alone, and
# Tower.zero keeps the radicand too, so the two sides agree structurally: the
# leaf is Rat.add_neg, which asks only for the leaf's denominator positivity --
# the same shape the pos carrier stores. clean is carried because the recursion
# hands each coordinate's own witness down.

law Tower.add_neg:
  for +x: Tower
  for hx: Tower.clean(x)
  for px: Tower.pos(x)
  {Tower.add(x, Tower.neg(x)) == Tower.zero(x) : Tower}

# -(x + y) = (-x) + (-y). The distribution law, named as Rat.neg_add is (Rat's
# flipped inverse is Rat.add_neg above). One level of recursion per coordinate,
# and the operand-level equation is what lets the recursion run: it is passed on
# as the coordinates' own equation after succ_inj.

law Tower.neg_add:
  for +x: Tower
  for +y: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for px: Tower.pos(x)
  for py: Tower.pos(y)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  {Tower.neg(Tower.add(x, y)) == Tower.add(Tower.neg(x), Tower.neg(y)) : Tower}

# mul_neg: x * (-y) = -(x * y), and neg_mul: (-x) * y = -(x * y). Both are
# projections of Tower.neg_pair (tower_helpers.bend), which is where the
# induction lives: the radicand coordinate of either conclusion needs the other
# half -- mul(f, x, neg y)'s is mul(g, mul(g, ix, neg iy), dx), and reaching
# neg(mul(g, mul(g, ix, iy), dx)) from it goes through the negation on the first
# argument, which is neg_mul at the pair (mul(g, ix, iy), dx). Neither half is
# provable on its own, exactly as with mul.depth and mul.clean.
#
# The hypotheses are what the induction consumes at every coordinate --
# cleanliness and positivity of both operands, and the operand-level depth
# equation -- plus the exact fuel mul.depth/mul.clean use, because each
# sub-product's cleanliness is only available at that fuel.

law Tower.mul_neg:
  for +f: Nat
  for +x: Tower
  for +y: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for px: Tower.pos(x)
  for py: Tower.pos(y)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  for hf: {f == Nat.add(1n, Tower.depth(x)) : Nat}
  {Tower.mul(f, x, Tower.neg(y)) == Tower.neg(Tower.mul(f, x, y)) : Tower}

law Tower.neg_mul:
  for +f: Nat
  for +x: Tower
  for +y: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for px: Tower.pos(x)
  for py: Tower.pos(y)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  for hf: {f == Nat.add(1n, Tower.depth(x)) : Nat}
  {Tower.mul(f, Tower.neg(x), y) == Tower.neg(Tower.mul(f, x, y)) : Tower}

# neg_neg: -(-x) = x, the one law of the negation block that needs a leaf fact.
#
# neg is coordinatewise and keeps the radicand, so the Ext arm is two recursive calls
# and two congruences; the markers are definitional, since neg is the identity on them.
# What is not structural is the Base leaf: Rat.neg_neg is stated at a spelled, reduced
# value (the double negation normalizes, so at a non-canonical Rat it is false), which
# is why the leaf's involution travels in the canon witness beside the spelling
# equations. One hypothesis, like the rest of the block.
law Tower.neg_neg:
  for +x: Tower
  for cx: Tower.canon(x)
  {Tower.neg(Tower.neg(x)) == x : Tower}

# add_zero: x + 0 = x, the first of the block that needs canonicality.
#
# Its Base arm is Rat.add_zero at the leaf, and the goal there is
# Base{Rat.add(a, Rat.zero())} = Base{a}: the left side is Mk's output, so the
# equation holds only if a is its own normal form -- which is what the canon
# witness supplies. The Ext arm is two recursive calls and two congruences. add
# keeps its first operand's radicand, so the third field is dx on both sides and no
# level hypothesis is needed; the markers are definitional, since add propagates
# them and zero is the identity on them.
law Tower.add_zero:
  for +x: Tower
  for cx: Tower.canon(x)
  {Tower.add(x, Tower.zero(x)) == x : Tower}

# zero_add: 0 + x = x, the mirror of add_zero and the same carrier.
#
# Base is Rat.zero_add at the leaf. The rewriting the fill does is not only about
# the Rat law's spelling: Rat.add destructures *both* operands, so at a variable a
# the goal's Rat.add(_, a) is stuck and only unfolds once every operand is spelled.
# That is why each fill here rewrites every occurrence of the value -- both sides in
# add_zero, and both inside and outside the Rat.add in zero_add. The Ext arm is two
# recursive calls with dx in the third slot on both sides (add keeps its first
# operand's radicand, and zero(x) carries dx too), and the markers are definitional.
law Tower.zero_add:
  for +x: Tower
  for cx: Tower.canon(x)
  {Tower.add(Tower.zero(x), x) == x : Tower}

# mul_one: x * 1 = x at the value's own level, and one_mul for 1 * x.
#
# Both are self-stated -- mul(f, u, one(u)) == u and mul(f, one(u), u) == u -- so neither
# needs a level hypothesis: every level fact the fills use is a sibling fact out of the
# canon witness (lri for re against im, lrd for re against d), exactly as add_zero and
# zero_add are stated. The pos witness is along because the fills reach the zero block,
# whose laws take one. one(u) is one at u's level: Base takes Rat.one(), and Ext keeps its
# real part's one, replaces im by zero, and keeps d -- so one(u) is canonical wherever u
# is, which is what the Base leaf needs from Rat.mul_one/Rat.one_mul (both stated at a
# spelled Rat{n, d} with mk(n, d) == Rat{n, d}, and the Canon carrier hands over exactly
# that equation).
law Tower.mul_one:
  for +f: Nat
  for +u: Tower
  for cu: Tower.canon(u)
  for pu: Tower.pos(u)
  for hf: {f == Nat.add(1n, Tower.depth(u)) : Nat}
  {Tower.mul(f, u, Tower.one(u)) == u : Tower}

law Tower.one_mul:
  for +f: Nat
  for +u: Tower
  for cu: Tower.canon(u)
  for pu: Tower.pos(u)
  for hf: {f == Nat.add(1n, Tower.depth(u)) : Nat}
  {Tower.mul(f, Tower.one(u), u) == u : Tower}
