import Base
import ./rat.bend as R

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
# Ext{re, im, d} at level k that is d, which the caller supplies; but the
# *coordinate* level below k has a different radicand -- the one stored inside the
# coordinates -- and that is what the depth-2 test of round thirty-four caught:
# the recursion was handing the level-k radicand to a level-(k-1) multiplication,
# whose operands then sat at different depths and came back as Bad. rad reads the
# right one off the operand, so the recursion descends without the caller having to
# thread a chain of radicands.

def Tower.rad(t: Tower) -> Tower:
  match t:
    case Base{v}:
      t
    case Ext{re, im, d}:
      d
    case Bad{}:
      Bad{}
    case Fuel{}:
      Fuel{}

# One level's arithmetic, generically
# ===================================
#
# The radicand is an operation *parameter* for the level being combined: it is
# what the result's third field records, and callers pass the level's own. What
# the recursion needs is *not* that value but the radicand one level down, which
# is a function of the operands rather than something a caller can thread --
# Tower.rad reads it off them. Round thirty-four measured why: handing the level's
# radicand to a coordinate-level multiplication put its operands at different
# depths and the result came back as Bad.
#
# Two operands at *different* levels are not a value of the theory -- there is no
# ring holding both -- and a call that mixes them returns Bad, not a plausible
# zero. The marker arms are last, after the matching ones, so they cannot
# swallow a legitimate call; a marker operand propagates its own marker. No law
# reaches any of them.
#
# mul reduces with sqrt(d) * sqrt(d) = d: the im*im term is multiplied by d, an
# element of the level below, exactly as the depth-1 QExt.mul does.

def Tower.add(x: Tower, y: Tower, +d: Tower) -> Tower:
  match x y:
    case Base{a} Base{b}:
      Base{R.Rat.add(a, b)}
    case Ext{+rx, +ix, dx} Ext{ry, iy, dy}:
      Ext{Tower.add(rx, ry, Tower.rad(rx)), Tower.add(ix, iy, Tower.rad(rx)), d}
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

def Tower.mul(+f: Nat, +d: Tower, x: Tower, y: Tower) -> Tower:
  match f:
    case 0n:
      Fuel{}
    case 1n+g:
      match x y:
        case Base{a} Base{b}:
          Base{R.Rat.mul(a, b)}
        case Ext{+rx, +ix, +dx} Ext{+ry, +iy, +dy}:
          Ext{Tower.add(Tower.mul(g, Tower.rad(rx), rx, ry),
                        Tower.mul(g, Tower.rad(rx),
                          Tower.mul(g, Tower.rad(rx), ix, iy), d),
                        Tower.rad(rx)),
              Tower.add(Tower.mul(g, Tower.rad(rx), rx, iy),
                        Tower.mul(g, Tower.rad(rx), ix, ry), Tower.rad(rx)),
              d}
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
           hri: {Tower.depth(re) == Tower.depth(im) : Nat}}

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
law Tower.add.depth:
  for +x: Tower
  for +y: Tower
  for +d: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for +hd: Tower.clean(d)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  {Tower.depth(Tower.add(x, y, d)) == Tower.depth(x) : Nat}

law Tower.add.clean:
  for +x: Tower
  for +y: Tower
  for +d: Tower
  for hx: Tower.clean(x)
  for hy: Tower.clean(y)
  for +hd: Tower.clean(d)
  for h: {Tower.depth(x) == Tower.depth(y) : Nat}
  Tower.clean(Tower.add(x, y, d))

# Fuel sufficiency at the bottom shape
# ===================================
#
# Two rational elements need no structure to multiply, so one step of fuel is
# always enough and the radicand is never touched. This is the base case of the
# obligation; the extension case is where the recursion has to descend a level,
# and that is a separate question (see TOWER-PLAN section 7, round thirty-three).

law Tower.mul.fuel.base:
  for +g: Nat
  for +d: Tower
  for a: R.Rat
  for b: R.Rat
  Tower.clean(Tower.mul(1n+g, d, Base{a}, Base{b}))

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
  for +d: Tower
  {Tower.add(Base{a}, Base{b}, d) == Base{R.Rat.add(a, b)} : Tower}

law Tower.add.ext:
  for +rx: Tower
  for +ix: Tower
  for dx: Tower
  for +ry: Tower
  for +iy: Tower
  for dy: Tower
  for +d: Tower
  {Tower.add(Ext{rx, ix, dx}, Ext{ry, iy, dy}, d)
   == Ext{Tower.add(rx, ry, Tower.rad(rx)), Tower.add(ix, iy, Tower.rad(rx)), d} : Tower}

law Tower.neg.ext:
  for rx: Tower
  for ix: Tower
  for dx: Tower
  {Tower.neg(Ext{rx, ix, dx}) == Ext{Tower.neg(rx), Tower.neg(ix), dx} : Tower}

law Tower.mul.base:
  for +g: Nat
  for +d: Tower
  for a: R.Rat
  for b: R.Rat
  {Tower.mul(1n+g, d, Base{a}, Base{b}) == Base{R.Rat.mul(a, b)} : Tower}

# the sqrt(d) * sqrt(d) = d reduction, as the unfolding the plan asks for. Spelled
# at a successor fuel, since the definition matches on the fuel.
law Tower.mul.ext:
  for +g: Nat
  for +d: Tower
  for +rx: Tower
  for +ix: Tower
  for dx: Tower
  for +ry: Tower
  for +iy: Tower
  for dy: Tower
  {Tower.mul(1n+g, d, Ext{rx, ix, dx}, Ext{ry, iy, dy})
   == Ext{Tower.add(Tower.mul(g, Tower.rad(rx), rx, ry),
                    Tower.mul(g, Tower.rad(rx),
                      Tower.mul(g, Tower.rad(rx), ix, iy), d),
                    Tower.rad(rx)),
          Tower.add(Tower.mul(g, Tower.rad(rx), rx, iy),
                    Tower.mul(g, Tower.rad(rx), ix, ry), Tower.rad(rx)),
          d} : Tower}

law Tower.one.base:
  for v: R.Rat
  {Tower.one(Base{v}) == Base{R.Rat.one()} : Tower}

law Tower.one.ext:
  for re: Tower
  for im: Tower
  for d: Tower
  {Tower.one(Ext{re, im, d}) == Ext{Tower.one(re), Tower.zero(im), d} : Tower}
