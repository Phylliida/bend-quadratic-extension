import Base

# Int: signed integers as a difference of naturals
# =================================================
#
# An Int is a pair (pos, neg) standing for pos - neg. Every operation is a
# constructor built out of Nat.add / Nat.mul, so operations always compose --
# no operation ever has to inspect its own result to canonicalize it -- and
# every ring law is a Nat semiring identity.
#
# What that costs: (pos, neg) is a *presentation*, not a canonical form.
# Int{1, 0} and Int{2, 1} are both 1 and are not ==. Deciding equality is
# Int.canon's job, needed only where a canonical representative matters (Rat
# normalization). The identities that name a specific representative of a
# value -- x + (-x) = 0 above all -- are therefore not == statements about
# Int, and land with Int.canon.
#
# The previous sign-magnitude Int (sign bit + magnitude, every op
# canonicalizing through Int.mk) did have decidable ==, but paid for it in
# case analysis: Int.add_assoc was ~545 proof lines over 8 sign patterns and
# their cmp/magnitude sub-splits, and Int.mul could not canonicalize at all
# without turning every composite product into a stuck term (which is what
# made Int.mul_distrib false as originally stated). See PROVING.md.
#
# Laws are stated here and left open; int_proofs.bend fills them via
# `def I.<name>(...)`.
type Int is Data:
  Int{pos: Nat, neg: Nat}
# the additive identity
def Int.zero() -> Int:
  Int{0n, 0n}
# the multiplicative identity
def Int.one() -> Int:
  Int{1n, 0n}
# Int.unit(n): the natural n as a non-negative Int. The name of the scaled
# units Int{d, 0n} the Rat operations multiply by, so that a proof can bind one
# (`Int.unit d`) instead of writing the constructor out at every mention.
def Int.unit(n: Nat) -> Int:
  Int{n, 0n}
def Int.add(x: Int, y: Int) -> Int:
  Int{+xp, +xn} = x
  Int{+yp, +yn} = y
  Int{Nat.add(xp, yp), Nat.add(xn, yn)}
# additive inverse: swap the two sides
def Int.neg(x: Int) -> Int:
  Int{+xp, +xn} = x
  Int{xn, xp}
# x - y, in the same shape as Int.add so the proofs line up
def Int.sub(x: Int, y: Int) -> Int:
  Int{+xp, +xn} = x
  Int{+yp, +yn} = y
  Int{Nat.add(xp, yn), Nat.add(xn, yp)}
# (xp - xn)(yp - yn) = (xp*yp + xn*yn) - (xp*yn + xn*yp)
def Int.mul(x: Int, y: Int) -> Int:
  Int{+xp, +xn} = x
  Int{+yp, +yn} = y
  Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)),
    Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp))}
# Int.add_comm: x + y = y + x
law Int.add_comm:
  for +x: Int
  for +y: Int
  {Int.add(x, y) == Int.add(y, x) : Int}
# Int.add_assoc: (x + y) + z = x + (y + z)
law Int.add_assoc:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.add(Int.add(x, y), z) == Int.add(x, Int.add(y, z)) : Int}
# Int.add_zero: x + 0 = x
law Int.add_zero:
  for +x: Int
  {Int.add(x, Int.zero()) == x : Int}
# Int.zero_add: 0 + x = x
law Int.zero_add:
  for +x: Int
  {Int.add(Int.zero(), x) == x : Int}
# Int.neg_invol: -(-x) = x
law Int.neg_invol:
  for +x: Int
  {Int.neg(Int.neg(x)) == x : Int}
# Int.neg_add: -(x + y) = -x + -y
law Int.neg_add:
  for +x: Int
  for +y: Int
  {Int.neg(Int.add(x, y)) == Int.add(Int.neg(x), Int.neg(y)) : Int}
# Int.neg_mul: -(x*y) = (-x)*y
law Int.neg_mul:
  for +x: Int
  for +y: Int
  {Int.neg(Int.mul(x, y)) == Int.mul(Int.neg(x), y) : Int}
# Int.sub_eq_add_neg: x - y = x + (-y)
law Int.sub_eq_add_neg:
  for +x: Int
  for +y: Int
  {Int.sub(x, y) == Int.add(x, Int.neg(y)) : Int}
# Int.mul_comm: x * y = y * x
law Int.mul_comm:
  for +x: Int
  for +y: Int
  {Int.mul(x, y) == Int.mul(y, x) : Int}
# Int.mul_assoc: (x * y) * z = x * (y * z)
law Int.mul_assoc:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.mul(Int.mul(x, y), z) == Int.mul(x, Int.mul(y, z)) : Int}
# Int.mul_distrib: x * (y + z) = x*y + x*z
law Int.mul_distrib:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.mul(x, Int.add(y, z)) == Int.add(Int.mul(x, y), Int.mul(x, z)) : Int}
# Int.mul_add_left: (x + y) * z = x*z + y*z  (the mirror of Int.mul_distrib)
law Int.mul_add_left:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.mul(Int.add(x, y), z) == Int.add(Int.mul(x, z), Int.mul(y, z)) : Int}
# Int.mul_zero: x * 0 = 0
law Int.mul_zero:
  for +x: Int
  {Int.mul(x, Int.zero()) == Int.zero() : Int}
# Int.mul_one: x * 1 = x
law Int.mul_one:
  for +x: Int
  {Int.mul(x, Int.one()) == x : Int}
# Int.one_mul: 1 * x = x
law Int.one_mul:
  for +x: Int
  {Int.mul(Int.one(), x) == x : Int}
# Int.canon: the canonical representative
# =======================================
#
# Int{pos, neg} is a presentation: Int{1,0} and Int{2,1} are both 1 and are
# not ==. Int.canon collapses a value to the representative with one side
# zero, which is what makes == decide integer equality and what Rat
# normalization divides out of a numerator.
#
# The comparison is threaded in as a Cmp parameter rather than written inline,
# for two reasons: a `match` scrutinee must be a parameter or a pattern-bound
# variable, never a computed value; and a def whose body matches on a stuck
# Nat.cmp cannot reduce, which would make every downstream term stuck. Callers
# that have no comparison in hand pass c := Nat.cmp(xp, xn) with evidence
# {==}, exactly as the Int.add_assoc helpers did.
def Int.canon.go(c: Cmp, xp: Nat, xn: Nat) -> Int:
  match c:
    case LT{}:
      Int{0n, Nat.sub(xn, xp)}
    case EQ{}:
      Int{0n, 0n}
    case GT{}:
      Int{Nat.sub(xp, xn), 0n}
def Int.canon(x: Int) -> Int:
  Int{+xp, +xn} = x
  Int.canon.go(Nat.cmp(xp, xn), xp, xn)
# Int.canon.pos: a non-negative value is already canonical
law Int.canon.pos:
  for +a: Nat
  for e: {Nat.cmp(a, 0n) == GT{} : Cmp}
  {Int.canon(Int{a, 0n}) == Int{a, 0n} : Int}
# Int.canon.neg: a non-positive value is already canonical
law Int.canon.neg:
  for +a: Nat
  for e: {Nat.cmp(0n, a) == LT{} : Cmp}
  {Int.canon(Int{0n, a}) == Int{0n, a} : Int}
# Int.canon.eqv.fwd: canon decides equality the way the cross sums do -- equal
# canonical forms force xp + yn = yp + xn. This is the half of
# "canon x == canon y iff xp + yn == yp + xn" that needs the work; the other
# half is Int.canon.eqv.bwd.
#
# The comparison of each side is a parameter (c1, c2 with their evidence), for
# the usual reason: Int.canon.go's body matches on it, and a computed match
# scrutinee is not legal, so a law that cases on it has to receive it.
#
# Every branch after the case split is one of two shapes:
#   - the two canon forms agree, so both sides are *non-zero* on the same side
#     (GT/GT, LT/LT) or both are zero (EQ/EQ). Int.eq.pos / Int.eq.neg turn the
#     Int equation into the coordinate equation, and the rest is Nat
#     shuffling: cmp_gt_sub_add / cmp_lt_sub_add say the coordinate is the
#     difference, and the goal follows by adding the common part to both sides.
#   - they disagree (a difference against zero, or a difference against a
#     difference of the other sign): the coordinate equation says a truncated
#     difference is 0, sub_pos says it is 1 + something, and a successor is not
#     zero -- so the branch is vacuous and Empty.absurd closes it.
law Int.canon.eqv.fwd:
  for c1: Cmp
  for +xp: Nat
  for +xn: Nat
  for c2: Cmp
  for +yp: Nat
  for +yn: Nat
  for +e1: {c1 == Nat.cmp(xp, xn) : Cmp}
  for +e2: {c2 == Nat.cmp(yp, yn) : Cmp}
  for +e: {Int.canon.go(c1, xp, xn) == Int.canon.go(c2, yp, yn) : Int}
  {Nat.add(xp, yn) == Nat.add(yp, xn) : Nat}
# Int.canon.eqv.bwd: the other half -- the cross sum forces the two canonical
# forms to agree. Almost all of the arithmetic is Nat-level, in the two laws
# nat.bend states for exactly this proof (cross_gt_gt, cross_cmp), so the
# branch structure here is only which law applies:
#
#   - GT/GT and LT/LT: both forms are a difference against zero, and the two
#     differences are equal -- cross_gt_gt for GT, the same law with the two
#     arguments swapped for LT, since the LT form holds sub(xn,xp).
#   - EQ/EQ: both forms are Int{0,0}, so the goal is reflexive.
#   - the six disagreeing pairs: the branch is impossible. cross_cmp is the
#     cross sum read as an equation between the two comparisons, and the
#     matching one of the six discrimination laws (gt_ne_eq, gt_ne_lt, ...)
#     refutes it -- no arithmetic in those branches at all.
#
# This is the reverse of Int.canon.eqv.fwd and the two together say canon
# decides Int equality: canon x == canon y exactly when xp + yn == yp + xn.
# Nothing downstream needs the reverse direction -- Rat equality goes through
# the forward one (canon.scale) and reads equal canonical fields off an equal
# pair -- so it is here because it is the law Int.canon's canonicality is
# *stated* with, not because the Rat route consumes it.
law Int.canon.eqv.bwd:
  for c1: Cmp
  for +xp: Nat
  for +xn: Nat
  for c2: Cmp
  for +yp: Nat
  for +yn: Nat
  for +e1: {c1 == Nat.cmp(xp, xn) : Cmp}
  for +e2: {c2 == Nat.cmp(yp, yn) : Cmp}
  for +e: {Nat.add(xp, yn) == Nat.add(yp, xn) : Nat}
  {Int.canon.go(c1, xp, xn) == Int.canon.go(c2, yp, yn) : Int}
