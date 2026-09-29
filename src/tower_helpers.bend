import Base
import ./rat.bend as R
import ./rat_helpers.bend as RH
import ./tower.bend as T

# Helper laws for Tower
# =====================
#
# The laws a reader of `tower.bend` does not need: variants of the readable
# laws, and the structural plumbing the layers above lean on. Same statements,
# moved here, with their fills still in tower_proofs.bend.
#
# `tower.bend` does not import this file -- a helper law is stated over that
# file's types and operations, so the import only goes one way.

law Tower.mul.fuel.zero:
  for +x: T.Tower
  for +y: T.Tower
  {T.Tower.mul(0n, x, y) == T.Fuel{} : T.Tower}

law Tower.mul.fuel.base:
  for +g: Nat
  for a: R.Rat
  for b: R.Rat
  T.Tower.clean(T.Tower.mul(1n+g, T.Base{a}, T.Base{b}))

# The two facts a product needs, proved as one induction
# ======================================================
#
# mul.clean and mul.depth are mutually dependent, and that is a measurement
# rather than a style choice. mul.depth's Ext/Ext arm calls mul on a product --
# `mul(g, mul(g, ix, iy), dx)` -- so that call needs *clean* evidence for
# `mul(g, ix, iy)`, and no depth law produces one. mul.clean's Ext/Ext arm needs
# the *depths* of the four sub-products: they are what add.clean's equal-depth
# hypothesis takes, and what the result's own level relations are built from.
# So neither law can be proved first: each one's Ext/Ext arm needs the other's
# conclusion about a product one recursion step down. Proving the pair in one
# induction is what removes the cycle. The recursive call returns both facts at
# the smaller fuel, so each is in hand exactly where the other is needed.
#
# Two measurements shaped the statement, and both are about the fuel.
#
# First, the fuel is a parameter with a sufficiency equation rather than a
# `1n+g` in the conclusion. At a fuel that runs out the claim is simply false:
# take x at depth 2 and fuel 1, and mul unfolds its arm with g = 0, so all four
# sub-products are `mul(0n, ...)` = Fuel{}, the coordinates are add(Fuel{},
# Fuel{}) = Fuel{}, and the product is Ext{Fuel{}, Fuel{}, dx}. Its depth is
# `1n+depth(Fuel{})` = 1, not depth(x) = 2, and its clean evidence would need
# `clean(Fuel{})`, which is Empty. So `hf: {f == 1n+Tower.depth(x)}` -- the fuel
# is exactly one level per operand, which is what the definition's own recursion
# consumes -- is not decoration. It is also what each recursive call needs: the
# operand one level down has depth one less, so its fuel is its own depth.
#
# Second, the fuel has to be a parameter for the fill's recursion to be legal at
# all. Bend requires a self-call's arguments to read left to right with each one
# unchanged until one shrinks, and the third recursive call is
# `mul(g, mul(g, ix, iy), dx)` -- a computed *product* in the second slot. With
# the fuel spelled `1n+g` in the conclusion it is the fill's first parameter that
# is already the smaller one, so nothing before the product can shrink and the
# call is rejected ("a decreasing self-call"). With the fuel as a parameter the
# fill matches on it, `case 1n+g` puts `g` in scope as a strict subterm of that
# parameter, and the fuel shrinking in the first slot frees every later argument
# -- which is exactly how Tower.mul's own definition gets away with the same
# call.
#
# Tower.Safe<x, p> is the pair for a product p of operands at x's level: p is
# clean, and p sits at x's level.

type Tower.Safe<-x: T.Tower, -p: T.Tower> is Data:
  SafeExt{csafe: T.Tower.clean(p),
          hdepth: {T.Tower.depth(p) == T.Tower.depth(x) : Nat}}

law Tower.mul.safe:
  for +f: Nat
  for +x: T.Tower
  for +y: T.Tower
  for hx: T.Tower.clean(x)
  for hy: T.Tower.clean(y)
  for h: {T.Tower.depth(x) == T.Tower.depth(y) : Nat}
  for hf: {f == Nat.add(1n, T.Tower.depth(x)) : Nat}
  Tower.Safe<x, T.Tower.mul(f, x, y)>

# The pair's two halves. Defs rather than laws, and they take the pair as a
# parameter, because that is the one place bend lets a destructuring match look
# at a value: "a match cannot scrutinize a computed value: give it its own def".
# A recursive call's result is computed, so the arm below cannot take it apart
# directly; it hands the pair to one of these instead.
def Tower.safe.clean(+f: Nat, +x: T.Tower, +y: T.Tower,
    s: Tower.Safe<x, T.Tower.mul(f, x, y)>) ->
    T.Tower.clean(T.Tower.mul(f, x, y)):
  match s:
    case SafeExt{cs, hd}:
      cs

def Tower.safe.depth(+f: Nat, +x: T.Tower, +y: T.Tower,
    s: Tower.Safe<x, T.Tower.mul(f, x, y)>) ->
    {T.Tower.depth(T.Tower.mul(f, x, y)) == T.Tower.depth(x) : Nat}:
  match s:
    case SafeExt{cs, hd}:
      hd

# mul_neg and neg_mul are one induction, for the same reason mul.depth and
# mul.clean are (round forty-five): each half needs the other where it is needed.
# mul(f, x, neg y)'s radicand coordinate is mul(g, mul(g, ix, neg iy), dx), and
# getting from there to neg(mul(g, mul(g, ix, iy), dx)) goes through the negation
# on the *first* argument -- which is neg_mul at the pair (mul(g, ix, iy), dx).
# Symmetrically neg_mul's radicand coordinate needs mul_neg at the same pair. So
# the two conclusions travel together, as one indexed evidence type: one
# recursive call hands back both, and each is in hand exactly where the other is
# wanted. The two readable laws in tower.bend are projections of this pair.
#
# The fuel is the exact one of mul.depth/mul.clean (f == 1n+depth(x)), for the
# same reason: the induction needs each sub-product's own cleanliness and level,
# and the pair that supplies those is stated at that fuel only.
type Tower.NegPair<-f: Nat, -x: T.Tower, -y: T.Tower> is Data:
  NegBoth{mneg: {T.Tower.mul(f, x, T.Tower.neg(y)) == T.Tower.neg(T.Tower.mul(f, x, y)) : T.Tower},
          nmul: {T.Tower.mul(f, T.Tower.neg(x), y) == T.Tower.neg(T.Tower.mul(f, x, y)) : T.Tower}}

law Tower.neg_pair:
  for +f: Nat
  for +x: T.Tower
  for +y: T.Tower
  for hx: T.Tower.clean(x)
  for hy: T.Tower.clean(y)
  for px: T.Tower.pos(x)
  for py: T.Tower.pos(y)
  for h: {T.Tower.depth(x) == T.Tower.depth(y) : Nat}
  for hf: {f == Nat.add(1n, T.Tower.depth(x)) : Nat}
  Tower.NegPair<f, x, y>

def Tower.negpair.mneg(+f: Nat, +x: T.Tower, +y: T.Tower,
    q: Tower.NegPair<f, x, y>) ->
    {T.Tower.mul(f, x, T.Tower.neg(y)) == T.Tower.neg(T.Tower.mul(f, x, y)) : T.Tower}:
  match q:
    case NegBoth{mneg, nmul}:
      mneg

def Tower.negpair.nmul(+f: Nat, +x: T.Tower, +y: T.Tower,
    q: Tower.NegPair<f, x, y>) ->
    {T.Tower.mul(f, T.Tower.neg(x), y) == T.Tower.neg(T.Tower.mul(f, x, y)) : T.Tower}:
  match q:
    case NegBoth{mneg, nmul}:
      nmul

# The same facts at any fuel above the threshold, plus the fuel law
# =================================================================
#
# mul.fuel.ext -- a product at a large enough fuel does not depend on how much
# fuel it was handed -- cannot be proved on its own. Its Ext/Ext arm makes the
# third recursive call multiply `mul(g, ix, iy)` by dx, and a recursive instance
# of the fuel law near the leaves needs its operands to be clean; using the
# exact-fuel pair (Tower.Safe) for that product is not available, because it is
# stated at f == 1n+depth(x) and this call is made at a fuel that may be larger.
# Getting from one to the other would mean transporting clean evidence along a
# *type* equality ({clean(a) == clean(b) : Data}), which is not what Equal.cong
# gives -- it composes a function over values.
#
# So the three facts are proved as one induction at the weaker hypothesis
# `cmp(depth(x), f) == LT{}`, and each is in hand where the other is wanted:
#
#   cabove: the product is clean
#   habove: the product sits at x's level
#   habeq:  the product is the threshold product mul(1n+depth(x), x, y)
#
# The exact-fuel pair stays as it is: its hypothesis is the one a caller of
# mul.depth and mul.clean has, and the two files' inductions differ only in the
# fuel hypothesis they start from.

type Tower.Above<-x: T.Tower, -f: Nat, -y: T.Tower> is Data:
  AboveExt{cabove: T.Tower.clean(T.Tower.mul(f, x, y)),
           habove: {T.Tower.depth(T.Tower.mul(f, x, y)) == T.Tower.depth(x) : Nat},
           habeq: {T.Tower.mul(f, x, y)
                   == T.Tower.mul(Nat.add(1n, T.Tower.depth(x)), x, y) : T.Tower}}

law Tower.mul.above:
  for +f: Nat
  for +x: T.Tower
  for +y: T.Tower
  for hx: T.Tower.clean(x)
  for hy: T.Tower.clean(y)
  for h: {T.Tower.depth(x) == T.Tower.depth(y) : Nat}
  for hf: {Nat.cmp(T.Tower.depth(x), f) == LT{} : Cmp}
  Tower.Above<x, f, y>

def Tower.above.clean(+f: Nat, +x: T.Tower, +y: T.Tower, s: Tower.Above<x, f, y>) ->
    T.Tower.clean(T.Tower.mul(f, x, y)):
  match s:
    case AboveExt{ca, ha, he}:
      ca

def Tower.above.depth(+f: Nat, +x: T.Tower, +y: T.Tower, s: Tower.Above<x, f, y>) ->
    {T.Tower.depth(T.Tower.mul(f, x, y)) == T.Tower.depth(x) : Nat}:
  match s:
    case AboveExt{ca, ha, he}:
      ha

def Tower.above.eq(+f: Nat, +x: T.Tower, +y: T.Tower, s: Tower.Above<x, f, y>) ->
    {T.Tower.mul(f, x, y)
     == T.Tower.mul(Nat.add(1n, T.Tower.depth(x)), x, y) : T.Tower}:
  match s:
    case AboveExt{ca, ha, he}:
      he

law Tower.mul.fuel.ext:
  for +f: Nat
  for +x: T.Tower
  for +y: T.Tower
  for hx: T.Tower.clean(x)
  for hy: T.Tower.clean(y)
  for h: {T.Tower.depth(x) == T.Tower.depth(y) : Nat}
  for hf: {Nat.cmp(T.Tower.depth(x), f) == LT{} : Cmp}
  {T.Tower.mul(f, x, y) == T.Tower.mul(1n+T.Tower.depth(x), x, y) : T.Tower}

# The witness is symmetric. Needed because the ring laws' inductions reach pairs
# the hypothesis is stated the other way round for -- mul_comm's third recursive
# call pairs ix with iy while the hypothesis pairs iy with ix.
law Tower.same.sym:
  for +x: T.Tower
  for +y: T.Tower
  for hs: T.Tower.same(x, y)
  T.Tower.same(y, x)

# ... and closed under add. This is the level discipline's first preservation law,
# and the reason the family had to be extended to agree on markers: the arms where
# one operand is Bad or Fuel are exactly the arms an induction over four shapes
# cannot avoid, and before round fifty-one the family was Empty there, so the law
# would have been unprovable rather than merely awkward.
#
# It reads as: if x and y have the same shape and so do u and v, then the sums do.
# At the leaves there is nothing to check -- the Rat laws are unconditional, and
# Base/Base lands on Base/Base -- and at an Ext pair the three fields are the two
# recursive instances plus the radicand equation the outer hypotheses already
# carry.
law Tower.same.add:
  for +x: T.Tower
  for +y: T.Tower
  for +u: T.Tower
  for +v: T.Tower
  for hx: T.Tower.same(x, y)
  for hu: T.Tower.same(u, v)
  T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v))

# ... and closed under mul, which is where the fuel comes in. The fuel is the first
# parameter so that the induction can shrink it -- the recursive instances are at
# `g`, and every later argument is free once the fuel has shrunk, which is what the
# first coordinates' rule requires (round forty-five).
law Tower.same.mul:
  for +f: Nat
  for +x: T.Tower
  for +y: T.Tower
  for +u: T.Tower
  for +v: T.Tower
  for hx: T.Tower.same(x, y)
  for hu: T.Tower.same(u, v)
  T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v))

# An equation between two tower values gives the witness. SameExt's third field is an
# *equation* between the radicands rather than a witness -- that is what makes add_comm
# true, since the result's third field is literally the first operand's -- so a law
# that needs a witness for a pair it only knows to be equal reads it through this.
law Tower.same.of_eq:
  for +x: T.Tower
  for +y: T.Tower
  for h: {x == y : T.Tower}
  T.Tower.same(x, y)

law Tower.level.refl:
  for +x: T.Tower
  T.Tower.level(x, x)

# Level is symmetric, and it is what makes the cross pair assemble: the three aligned
# pairs that sit around a value -- (re, im) inside x, (rx, ry) across the operands,
# (ry, iy) inside y -- combine, through symmetry and transitivity, into the cross pair
# (rx, iy) that mul_comm's recursive instance needs.
law Tower.level.sym:
  for +x: T.Tower
  for +y: T.Tower
  for h: T.Tower.level(x, y)
  T.Tower.level(y, x)

# Level is transitive, and transitivity is what assembles the cross pair. The three
# aligned pairs that sit around two operands -- x's own coordinates (re, im), the pair
# across the operands (rx, ry), y's own coordinates (ry, iy) -- chain into level(rx, iy),
# the pair mul_comm's recursive instance needs and same(x, y) cannot hand over.
law Tower.level.trans:
  for +x: T.Tower
  for +y: T.Tower
  for +z: T.Tower
  for hxy: T.Tower.level(x, y)
  for hyz: T.Tower.level(y, z)
  T.Tower.level(x, z)

# Closure under add: the first propagation law of the coefficient carrier. The leaf
# case is R.Rat.add.den.pos read at the two coordinates; the Ext case is two recursive
# instances. No depth agreement appears -- add computes Ext{..., dx} whatever the depths
# are, and positivity is a per-value fact, so unlike add.clean this law needs no
# hypothesis beyond the two witnesses.
law Tower.pos.add:
  for +x: T.Tower
  for +y: T.Tower
  for hx: T.Tower.pos(x)
  for hy: T.Tower.pos(y)
  T.Tower.pos(T.Tower.add(x, y))

# Closure under neg: neg is coordinatewise, so the leaf case is R.Rat.neg.den.pos and
# the Ext case is the two recursive instances with the radicand witness untouched
# (neg leaves d alone).
law Tower.pos.neg:
  for +x: T.Tower
  for hx: T.Tower.pos(x)
  T.Tower.pos(T.Tower.neg(x))

# Closure under mul -- the reason Pos.Ext carries a radicand field at all: mul's result
# is Ext{..., dx}, so the product's radicand belongs to the *first* operand and its
# positivity comes from x. Four recursive instances feed two pos.add calls (the re
# coordinate is a sum of a product and a product-with-the-radicand, the im coordinate a
# sum of two products), and the third mul call takes a *computed* product in its first
# argument -- legal because the fuel is a parameter and shrinks first, the same move
# Tower.mul.safe makes.
law Tower.pos.mul:
  for +f: Nat
  for +x: T.Tower
  for +y: T.Tower
  for hx: T.Tower.pos(x)
  for hy: T.Tower.pos(y)
  T.Tower.pos(T.Tower.mul(f, x, y))

# Level propagates through add. Four hypotheses, not two: add keeps its *first*
# operand's radicand, so add(x, y) and add(u, v) carry x's and u's radicands
# respectively and the conclusion needs {dx == du} -- that is hxu's ld field. The
# cross facts hxu/hyv are also what the Ext/Ext/Ext/Ext recursion consumes, so the
# law is exactly as strong as its own induction. E.g. the site that strengthens
# add.clean uses it at (rx, ry, ix, iy) with hxy = x's own level(re, im),
# huv = y's own, hxu = the law's cross level(rx, ry), hyv = level(ry, iy).
law Tower.level.add:
  for +x: T.Tower
  for +y: T.Tower
  for +u: T.Tower
  for +v: T.Tower
  for hxy: T.Tower.level(x, y)
  for huv: T.Tower.level(u, v)
  for hxu: T.Tower.level(x, u)
  for hyv: T.Tower.level(y, v)
  T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v))
