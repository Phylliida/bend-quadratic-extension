import Base
import ./int.bend as I

# Helper laws for Int
# ===================
#
# The laws a reader of `int.bend` does not need: sign-split and direction
# variants of the ring laws, the rearrangement rules, the scaling plumbing the
# Rat layer leans on, and the internals of the canonical-form argument. They
# are stated exactly as they were in int.bend, and this file is where the
# proofs for them live too (int_proofs.bend fills both files).
#
# `int.bend` does not import this file: the readable layer stays readable, and
# a file that wants the whole Int surface imports both.

# I.Int.add_exchange: x + (y + z) = y + (x + z)
law Int.add_exchange:
  for +x: I.Int
  for +y: I.Int
  for +z: I.Int
  {I.Int.add(x, I.Int.add(y, z)) == I.Int.add(y, I.Int.add(x, z)) : I.Int}

# I.Int.mul_assoc.pos / .neg: the two Nat halves of I.Int.mul_assoc.
#
# Splitting them is what keeps I.Int.mul_assoc readable: each chain then only
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

# I.Int.mul_swap: (a * b) * c = (a * c) * b
law Int.mul_swap:
  for +a: I.Int
  for +b: I.Int
  for +c: I.Int
  {I.Int.mul(I.Int.mul(a, b), c) == I.Int.mul(I.Int.mul(a, c), b) : I.Int}

# I.Int.mul_scale: the raw spelling of "multiply by the natural d", I.Int.mul(x,
# I.Int{d, 0n}), is the coordinate pair (xp*d, xn*d).
#
# This is a *shape* law, not a ring law: it names what the I.Int product reduces
# to once the two zero products are off, and that shape is what the Rat value
# lemma's consumers want on both sides of their equations (num(mk(n,d))*d is
# I.Int.mul of the numerator with I.Int{d,0}, and the cleaned form is the same
# coordinates scaled). Stated over raw coordinates because I.Int.mul destructures
# its left argument, so the cleaned pair has to name xp and xn.
law Int.mul_scale:
  for +xp: Nat
  for +xn: Nat
  for +d: Nat
  {I.Int.mul(I.Int{xp, xn}, I.Int{d, 0n}) == I.Int{Nat.mul(xp, d), Nat.mul(xn, d)} : I.Int}

# I.Int.scale.pair: a Nat-scaled unit is the product of the two units -- the
# shape law that lets a proof take a single scale apart into its factors (and
# put it back together), which is what a *ring* permutation of a product needs:
# a factor that is a scale has to become factors before it can be moved.
law Int.scale.pair:
  for +p: Nat
  for +q: Nat
  {I.Int{Nat.mul(p, q), 0n} == I.Int.mul(I.Int{p, 0n}, I.Int{q, 0n}) : I.Int}

# I.Int.scale.cancel: a positive scale can be cancelled -- multiplication by
# I.Int{1+kp, 0n} is injective. The Nat content is Nat.mul_right_cancel; what
# this law adds is the I.Int spelling, and a consumer needs it whenever it has
# scaled *both* sides of an equation by a denominator to put them over a common
# one and then wants the unscaled equation back (which is what the cross
# product Rat.mk.eqv consumes looks like after the scaling).
#
# I.Int.mul_scale names the coordinate pair both sides reduce to, so the two
# coordinate equations are I.Int.eq.pos / I.Int.eq.neg at that pair, and the goal
# is rebuilt from them with two congs.
law Int.scale.cancel:
  for +u: I.Int
  for +v: I.Int
  for +kp: Nat
  for e: {I.Int.mul(u, I.Int{1n+kp, 0n}) == I.Int.mul(v, I.Int{1n+kp, 0n}) : I.Int}
  {u == v : I.Int}

# I.Int.canon.idem: canon is idempotent
law Int.canon.idem:
  for c: Cmp
  for +xp: Nat
  for +xn: Nat
  for e: {c == Nat.cmp(xp, xn) : Cmp}
  {I.Int.canon(I.Int.canon.go(c, xp, xn)) == I.Int.canon.go(c, xp, xn) : I.Int}

# I.Int.canon.scale: canon is natural under scaling by a positive integer,
# canon(x*(1+kp)) = canon(x)*(1+kp). This is what Rat normalization uses: the
# normal form of a fraction scaled by k is the scaled normal form, so a
# canonical representative can be reached by scaling both sides.
#
# The statement is the same as I.Int.canon.scale.go's -- the go form only spells
# the right-hand canon through canon.go so that the fill can case on the
# comparison, which it must: Nat.cmp of two variables is not a legal match
# scrutinee ("a match cannot scrutinize a computed value"), so the comparison
# has to arrive as a parameter, exactly as in I.Int.canon.idem.
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
  {I.Int.canon(I.Int.mul(I.Int{xp, xn}, I.Int{1n+kp, 0n})) == I.Int.mul(I.Int.canon.go(c, xp, xn), I.Int{1n+kp, 0n}) : I.Int}

law Int.canon.scale:
  for +x: I.Int
  for +kp: Nat
  {I.Int.canon(I.Int.mul(x, I.Int{1n+kp, 0n})) == I.Int.mul(I.Int.canon(x), I.Int{1n+kp, 0n}) : I.Int}

# I.Int.eq.pos / I.Int.eq.neg: constructor injectivity for I.Int, one coordinate at a
# time. Both are J steps whose motive projects the left-hand I.Int and the
# right-hand one, so nothing here is specific to a caller -- but the motive has
# to name a coordinate of an *arbitrary* I.Int, and that is what the proof-side
# projections I.Int.proj.pos / I.Int.proj.neg exist for.
law Int.eq.pos:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +e: {I.Int{a, b} == I.Int{c, d} : I.Int}
  {a == c : Nat}

law Int.eq.neg:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +e: {I.Int{a, b} == I.Int{c, d} : I.Int}
  {b == d : Nat}

# I.Int.scale_cross: the cross product two scaled value equations give -- the
# assembly step of every Rat law that composes two normalized results.
#
# e1 and e2 are two value equations in mk.value's shape (a numerator against a
# positive denominator), s1/s2 say the two difference-pair numerators are the
# raw products xn*yn and yn*zn (that is Rat.num.mul), and the conclusion is the
# cross product of the *composed* fraction: (A*zn)*(xd*b) == (xn*B)*(a*zd).
#
# The proof is one cancellation: both sides are scaled by 1+dyp -- which both
# denominators carry (d1 = xd*yd, d2 = yd*zd) -- and over that common factor the
# two sides meet at the single middle product xn*yn*a*zn*b, reached from e1
# (scaled by zn*b, with s1) and from e2 (scaled by xn*a, with s2). Everything
# else in the fill is the ring bookkeeping that moves the scales past the
# factors they have to sit next to, which is why the scales get split
# (I.Int.scale.pair) and why the statement is a law of its own: with letters
# instead of the spelled-out fractions, every motive stays short.
law Int.scale_cross:
  for +A: I.Int
  for +R1: I.Int
  for +B: I.Int
  for +R2: I.Int
  for +xn: I.Int
  for +yn: I.Int
  for +zn: I.Int
  for +a: Nat
  for +b: Nat
  for +xd: Nat
  for +zd: Nat
  for +dyp: Nat
  for e1: {I.Int.mul(A, I.Int{Nat.mul(xd, 1n+dyp), 0n}) == I.Int.mul(R1, I.Int{a, 0n}) : I.Int}
  for e2: {I.Int.mul(B, I.Int{Nat.mul(1n+dyp, zd), 0n}) == I.Int.mul(R2, I.Int{b, 0n}) : I.Int}
  for s1: {R1 == I.Int.mul(xn, yn) : I.Int}
  for s2: {R2 == I.Int.mul(yn, zn) : I.Int}
  {I.Int.mul(I.Int.mul(I.Int.mul(A, zn), I.Int{Nat.mul(xd, b), 0n}), I.Int{1n+dyp, 0n})
   == I.Int.mul(I.Int.mul(I.Int.mul(xn, B), I.Int{Nat.mul(a, zd), 0n}), I.Int{1n+dyp, 0n}) : I.Int}
