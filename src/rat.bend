import Base
import ./nat.bend as N
import ./int.bend as I

# Rat: rationals as canonical pairs
# =================================
#
# A Rat is a pair (num, den) standing for num/den, and the numbers Rat.mk
# produces are *canonical*: den is positive, num has one side zero (it is a
# difference pair, the shape Int.canon produces), and gcd(|num|, den) is 1.
# On canonical pairs the language's structural == decides rational equality --
# that is what Rat.mk.eqv proves, and it is the reason the gcd is cancelled at
# all: without it Int{1,0}/2n and Int{2,0}/4n would be different values of the
# same rational.
#
# The representation is chosen so that the operations are *never stuck*:
# Rat.mk has no match at all (it canonicalizes by arithmetic -- truncated
# subtraction for the numerator's two sides, gcd and div for the reduction), so
# all the case analysis lives in the laws, where it can be threaded in as a
# comparison parameter exactly as Int.canon does it. What the ops therefore
# satisfy for free is congruence: Rat.add(x,y) and Rat.add(y,x) are Rat.mk of
# two Ints that Int.add_comm says are equal, so Rat.add_comm is two Equal.cong
# steps and no arithmetic.
#
# What congruence does *not* give is the laws that make normalization
# disappear: Rat.mul(x, one) == x needs "mk is the identity on a reduced
# fraction" (Rat.mk.canon), and the laws that compose two normalized sums
# (add_assoc above all) need "mk is natural under scaling" (Rat.mk.scale) --
# the normalized numerator of x + y, multiplied by z's denominator, is the
# normalized numerator of (x + y)*z only up to that.

# Rat{num, den}: num/den, canonical when den is positive, num is one side zero
# and gcd(num.pos + num.neg, den) is 1.
type Rat is Data:
  Rat{num: I.Int, den: Nat}

# the additive and multiplicative identities: 0/1 and 1/1, already canonical
def Rat.zero() -> Rat:
  Rat{I.Int.zero(), 1n}

def Rat.one() -> Rat:
  Rat{I.Int.one(), 1n}

# Rat.num(np, nn): np - nn as a difference pair. Exactly one of the two sides
# is zero (or both), so this is the canonical numerator shape for the raw
# coordinates np, nn -- which is why Rat.mk produces it and why the canonical
# laws are stated over (np, nn) rather than over an arbitrary Int.
def Rat.num(+np: Nat, +nn: Nat) -> I.Int:
  I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}

# Rat.mag(np, nn): |np - nn|, the magnitude that is coprime with the
# denominator in a canonical Rat.
def Rat.mag(+np: Nat, +nn: Nat) -> Nat:
  Nat.add(Nat.sub(np, nn), Nat.sub(nn, np))

# Rat.g(np, nn, d): the common divisor Rat.mk cancels -- gcd(|np - nn|, d).
def Rat.g(+np: Nat, +nn: Nat, +d: Nat) -> Nat:
  N.Nat.gcd(Rat.mag(np, nn), d)

# Rat.mk.go: the normalization itself. Each coordinate is divided by the gcd;
# for a canonical numerator one of the two divisions is div(0, g) = 0, so the
# result still has one side zero.
#
# Nothing here matches, which is the point: the result of Rat.mk.go is a
# constructor whose fields are div/gcd terms, so it reduces as far as the
# arguments allow and never gets stuck on a comparison. d = 0 (a fraction with
# zero denominator) is not special-cased: it lands on den = 0, which is *not*
# canonical, and no law claims anything about it -- the field laws carry
# canonicality hypotheses, and every operation on canonical values keeps the
# denominator positive.
def Rat.mk.go(+np: Nat, +nn: Nat, +d: Nat) -> Rat:
  Rat{I.Int{Nat.div(Nat.sub(np, nn), Rat.g(np, nn, d)),
            Nat.div(Nat.sub(nn, np), Rat.g(np, nn, d))},
      Nat.div(d, Rat.g(np, nn, d))}

# Rat.mk(n, d): n/d in canonical form.
def Rat.mk(n: I.Int, d: Nat) -> Rat:
  I.Int{+np, +nn} = n
  Rat.mk.go(np, nn, d)

# Rat.add: x + y = (xn*yd + yn*xd) / (xd*yd), normalized. The two products are
# Int times a Nat, written Int.mul(n, Int{k, 0}) -- the representation's way of
# scaling an Int.
def Rat.add(x: Rat, y: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat{+yn, +yd} = y
  Rat.mk(I.Int.add(I.Int.mul(xn, I.Int{yd, 0n}), I.Int.mul(yn, I.Int{xd, 0n})),
    Nat.mul(xd, yd))

# Rat.neg: -x = (-xn)/xd
def Rat.neg(x: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat.mk(I.Int.neg(xn), xd)

# Rat.sub: x - y = x + (-y) -- the definition, so Int.sub_eq_add_neg's twin
# here is a definitional equality.
def Rat.sub(x: Rat, y: Rat) -> Rat:
  Rat.add(x, Rat.neg(y))

# Rat.mul: x * y = (xn*yn)/(xd*yd), normalized
def Rat.mul(x: Rat, y: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat{+yn, +yd} = y
  Rat.mk(I.Int.mul(xn, yn), Nat.mul(xd, yd))

# The congruence laws
# ===================
#
# Every law in this block holds for *every* pair of Rats, canonical or not: the
# two sides are Rat.mk applied to arguments that the Int and Nat ring laws
# identify, and Equal.cong carries the equation through Rat.mk. No canonicality
# hypothesis is needed and none is stated.
#
# The list is short on purpose. Congruence only reaches the laws whose two
# sides normalize *the same raw arguments* -- the commutations and the negation
# identity. As soon as an operation is applied to the result of another
# operation (mul_assoc, add_assoc, mul_distrib) the inner Rat.mk has already
# cancelled a gcd, and the outer one sees div/gcd terms: those laws need
# Rat.mk.scale (normalization is natural under scaling) and Rat.mk.eqv (equal
# values have equal normal forms), and they are added on top of it.

# Rat.add_comm: x + y = y + x
law Rat.add_comm:
  for +x: Rat
  for +y: Rat
  {Rat.add(x, y) == Rat.add(y, x) : Rat}

# Rat.mul_comm: x * y = y * x
law Rat.mul_comm:
  for +x: Rat
  for +y: Rat
  {Rat.mul(x, y) == Rat.mul(y, x) : Rat}

# Rat.sub_eq_add_neg: x - y = x + (-y) -- true by definition here
law Rat.sub_eq_add_neg:
  for +x: Rat
  for +y: Rat
  {Rat.sub(x, y) == Rat.add(x, Rat.neg(y)) : Rat}

# Canonicality
# ============
#
# The laws above hold for every Rat. The laws below are the ones that make
# normalization *disappear*, and they need to know that the value they are
# applied to is already normalized -- which is exactly the statement
# "Rat.mk is the identity here", taken as a hypothesis:
#
#     for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
#
# That hypothesis is what `canonical` means for this representation, and
# Rat.mk.fixed below is where it comes from for values built the way the rest
# of the development builds them (numerator a difference pair, gcd cancelled).
# Nothing else about canonicality is needed: not coprimality of the output, not
# gcd being the greatest.

# Rat.mk.canon: mk is the identity on a reduced fraction. The gcd it cancels is
# 1, so every division is by 1 and the difference pair comes back unchanged.
#
# This is the whole reason mk.go is stated over raw coordinates (np, nn): the
# divisor mk.go computes is literally Rat.g(np, nn, 1+dp), so the coprime
# hypothesis is about the *same* expression, and the proof needs no case split,
# no comparison and no sub rewrite.
law Rat.mk.canon:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.mk.go(np, nn, 1n+dp) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# Rat.mk.zero: 0/d normalizes to 0/1 for every positive d. The gcd of 0 and d
# is d (Nat.gcd answers its second argument at 0), so both numerator divisions
# are 0/d = 0 and the denominator division is d/d = 1.
law Rat.mk.zero:
  for +dp: Nat
  {Rat.mk(I.Int.zero(), 1n+dp) == Rat.zero() : Rat}

# Rat.mk.fixed: a reduced fraction in the difference-pair presentation is a
# fixed point of mk -- the hypothesis the identity laws take, discharged.
#
# mk destructures the numerator *it* produced, so it sees the pair's own sides
# (sub(np,nn), sub(nn,np)) as raw coordinates: that is where sub_diag comes in
# (the double truncation of a one-sided pair is a no-op) together with its
# mirror at the swapped comparison, after which mk.canon applies.
law Rat.mk.fixed:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.mk(Rat.num(np, nn), 1n+dp) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# The identity laws
# =================
#
# x + 0 = x, x * 1 = x and x * 0 = 0, for a canonical x (fx) and a positive
# denominator where that matters. Each fill is the same three steps: unfold the
# operation, carry the Int/Nat identity through Rat.mk with two Equal.cong, and
# close with fx (or, for mul_zero, with Rat.mk.zero).

# Rat.add_zero: x + 0 = x
law Rat.add_zero:
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  {Rat.add(Rat{n, d}, Rat.zero()) == Rat{n, d} : Rat}

# Rat.zero_add: 0 + x = x
law Rat.zero_add:
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  {Rat.add(Rat.zero(), Rat{n, d}) == Rat{n, d} : Rat}

# Rat.mul_one: x * 1 = x
law Rat.mul_one:
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  {Rat.mul(Rat{n, d}, Rat.one()) == Rat{n, d} : Rat}

# Rat.one_mul: 1 * x = x
law Rat.one_mul:
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  {Rat.mul(Rat.one(), Rat{n, d}) == Rat{n, d} : Rat}

# Rat.mul_zero: x * 0 = 0. No canonicality hypothesis is needed, only that the
# denominator is positive: mk(0, d) is 0/1 because gcd(0, d) = d.
law Rat.mul_zero:
  for +n: I.Int
  for +dp: Nat
  {Rat.mul(Rat{n, 1n+dp}, Rat.zero()) == Rat.zero() : Rat}
