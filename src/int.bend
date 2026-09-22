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

# Int.add_exchange: x + (y + z) = y + (x + z)
law Int.add_exchange:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.add(x, Int.add(y, z)) == Int.add(y, Int.add(x, z)) : Int}

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

# Int.mul_assoc.pos / .neg: the two Nat halves of Int.mul_assoc.
#
# Splitting them is what keeps Int.mul_assoc readable: each chain then only
# ever spells one coordinate of the goal. The pos half is what a left
# multiplication by a sum leaves on the positive side,
#   (xp*yp + xn*yn)*zp + (xp*yn + xn*yp)*zn,
# and the neg half is the same with zp and zn exchanged.
law Int.mul_assoc.pos:
  for +xp: Nat
  for +xn: Nat
  for +yp: Nat
  for +yn: Nat
  for +zp: Nat
  for +zn: Nat
  {Nat.add(Nat.mul(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), zp), Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zn)) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}

law Int.mul_assoc.neg:
  for +xp: Nat
  for +xn: Nat
  for +yp: Nat
  for +yn: Nat
  for +zp: Nat
  for +zn: Nat
  {Nat.add(Nat.mul(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), zn), Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zp)) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}

# Int.mul_swap: (a * b) * c = (a * c) * b
law Int.mul_swap:
  for +a: Int
  for +b: Int
  for +c: Int
  {Int.mul(Int.mul(a, b), c) == Int.mul(Int.mul(a, c), b) : Int}

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

# Int.canon.idem: canon is idempotent
law Int.canon.idem:
  for c: Cmp
  for +xp: Nat
  for +xn: Nat
  for e: {c == Nat.cmp(xp, xn) : Cmp}
  {Int.canon(Int.canon.go(c, xp, xn)) == Int.canon.go(c, xp, xn) : Int}

# Int.canon.scale: canon is natural under scaling by a positive integer,
# canon(x*(1+kp)) = canon(x)*(1+kp). This is what Rat normalization uses: the
# normal form of a fraction scaled by k is the scaled normal form, so a
# canonical representative can be reached by scaling both sides.
#
# The statement is the same as Int.canon.scale.go's -- the go form only spells
# the right-hand canon through canon.go so that the fill can case on the
# comparison, which it must: Nat.cmp of two variables is not a legal match
# scrutinee ("a match cannot scrutinize a computed value"), so the comparison
# has to arrive as a parameter, exactly as in Int.canon.idem.
#
# Both are stated with k = 1 + kp rather than k >= 1, for the usual reason:
# the hypothesis is then a constructor, and cmp_mul_right is stated over
# 1 + kp.
law Int.canon.scale.go:
  for c: Cmp
  for +xp: Nat
  for +xn: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(xp, xn) : Cmp}
  {Int.canon(Int.mul(Int{xp, xn}, Int{1n+kp, 0n})) == Int.mul(Int.canon.go(c, xp, xn), Int{1n+kp, 0n}) : Int}

law Int.canon.scale:
  for +x: Int
  for +kp: Nat
  {Int.canon(Int.mul(x, Int{1n+kp, 0n})) == Int.mul(Int.canon(x), Int{1n+kp, 0n}) : Int}
