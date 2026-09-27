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

# One level's arithmetic, generically
# ===================================
#
# The radicand is an operation *parameter*, not something read out of the
# operands. That is the depth-1 house style (`QExt.mul(+d, x, y)`) lifted one
# level, and it is what makes the ring laws statable: `add(d, x, y)` and
# `add(d, y, x)` mention one radicand, so no law needs a shape-agreement
# hypothesis. The discipline is that callers pass the level's own radicand.
#
# Two operands at *different* levels are not a value of the theory -- there is no
# ring holding both -- and a call that mixes them returns Bad, not a plausible
# zero. The marker arms are last, after the matching ones, so they cannot
# swallow a legitimate call; a marker operand propagates its own marker. No law
# reaches any of them.
#
# mul reduces with sqrt(d) * sqrt(d) = d: the im*im term is multiplied by d, an
# element of the level below, exactly as the depth-1 QExt.mul does.

def Tower.add(+d: Tower, x: Tower, y: Tower) -> Tower:
  match x y:
    case Base{a} Base{b}:
      Base{R.Rat.add(a, b)}
    case Ext{rx, ix, dx} Ext{ry, iy, dy}:
      Ext{Tower.add(d, rx, ry), Tower.add(d, ix, iy), d}
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
          Ext{Tower.add(d, Tower.mul(g, d, rx, ry),
                        Tower.mul(g, d, Tower.mul(g, d, ix, iy), d)),
              Tower.add(d, Tower.mul(g, d, rx, iy), Tower.mul(g, d, ix, ry)),
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
  for +d: Tower
  for a: R.Rat
  for b: R.Rat
  {Tower.add(d, Base{a}, Base{b}) == Base{R.Rat.add(a, b)} : Tower}

law Tower.add.ext:
  for +d: Tower
  for rx: Tower
  for ix: Tower
  for dx: Tower
  for ry: Tower
  for iy: Tower
  for dy: Tower
  {Tower.add(d, Ext{rx, ix, dx}, Ext{ry, iy, dy})
   == Ext{Tower.add(d, rx, ry), Tower.add(d, ix, iy), d} : Tower}

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
  for rx: Tower
  for ix: Tower
  for dx: Tower
  for ry: Tower
  for iy: Tower
  for dy: Tower
  {Tower.mul(1n+g, d, Ext{rx, ix, dx}, Ext{ry, iy, dy})
   == Ext{Tower.add(d, Tower.mul(g, d, rx, ry),
                    Tower.mul(g, d, Tower.mul(g, d, ix, iy), d)),
          Tower.add(d, Tower.mul(g, d, rx, iy), Tower.mul(g, d, ix, ry)),
          d} : Tower}

law Tower.one.base:
  for v: R.Rat
  {Tower.one(Base{v}) == Base{R.Rat.one()} : Tower}

law Tower.one.ext:
  for re: Tower
  for im: Tower
  for d: Tower
  {Tower.one(Ext{re, im, d}) == Ext{Tower.one(re), Tower.zero(im), d} : Tower}
