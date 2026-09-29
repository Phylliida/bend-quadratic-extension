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
law Tower.add_comm:
  for +x: Tower
  for +y: Tower
  for hs: Tower.same(x, y)
  {Tower.add(x, y) == Tower.add(y, x) : Tower}
