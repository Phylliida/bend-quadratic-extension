import Base
import ./nat.bend as N
import ./int.bend as I
import ./int_helpers.bend as IH

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

# Rat.numof(r) / Rat.denof(r): the two fields of a Rat as functions.
#
# The value lemma below is about a Rat *value* -- mk's output, or the result of
# an operation -- and such a numerator is a field of a constructor the statement
# cannot destructure (a statement has no body to put a match in). So the
# projection has to be a def, exactly as Rat.num is the numerator of a *raw*
# coordinate pair. Both are marked (+n, +d) so a caller can read a field twice.
def Rat.numof(r: Rat) -> I.Int:
  Rat{+n, +d} = r
  n

def Rat.denof(r: Rat) -> Nat:
  Rat{+n, +d} = r
  d

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

# Rat.of(np, nn, dp): the raw rational (np - nn)/(1 + dp) as a constructor --
# the spelling a divisor with literal coordinates is named in, and the one the
# division laws consume. A plain abbreviation like QExt.of: nothing is
# normalized here and no match is taken on the arguments, so it unfolds to the
# constructor wherever a law or a fill writes it. It exists because a *let*
# cannot hold a bare constructor -- the checker cannot infer the constructor's
# type without an expected type -- so a fill that wants to name the divisor once
# and use it ten times needs a def to name it with.
def Rat.of(+np: Nat, +nn: Nat, +dp: Nat) -> Rat:
  Rat{Rat.num(np, nn), 1n+dp}

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

# Rat.inv
# =======
#
# x^-1 for a fraction written in *raw* coordinates: given the difference pair
# (np, nn) its numerator is the pair np - nn and the reciprocal is
#
#     ((np - nn)/d)^-1 = d/(np - nn)
#
# -- the difference moves into the denominator slot -- so the sign of np - nn
# has to be known before the value can be written down at all. That is a
# Nat.cmp case split, and a computed Nat.cmp is not a legal match scrutinee
# ("scrutinees in binder order": a match takes parameters and pattern-bound
# variables, never a computed value), so the comparison arrives as a parameter
# with {c == Nat.cmp(np, nn)} evidence, exactly as Nat.gcd.go and Int.canon.go
# take theirs. What the split buys is that np - nn is a *difference of Nats with
# its sign settled*: on the GT branch the numerator coordinate np - nn is the
# magnitude, on the LT branch nn - np is, and in both cases Rat.num's other
# coordinate is div(0, ..) = 0, which is what makes the result canonical.
#
# The result is the raw constructor, not a call of Rat.mk: for a canonical
# input the pair (d, |np - nn|) is already reduced -- d is positive by the
# canonicality hypothesis and gcd(|np - nn|, d) is 1 by the coprimality one --
# so Rat.mk would return this same constructor, and writing it directly is what
# puts the following law's product in a shape that reduces. It also keeps the
# EQ branch honest: there the denominator is 0 and the value is junk, exactly
# the stance Rat.mk takes on d = 0 -- no law claims anything about either.
#
# Rat.div(a, b) = a * b^-1 is then a definition, like Rat.sub: with b handed to
# Rat.inv at its own tree the comparison is a computation and the {==} evidence
# is free.
def Rat.inv(+np: Nat, +nn: Nat, +d: Nat, c: Cmp, +e: {c == Nat.cmp(np, nn) : Cmp}) -> Rat:
  match c:
    case LT{}:
      Rat{Rat.num(0n, d), Nat.sub(nn, np)}
    case EQ{}:
      Rat{Rat.num(np, nn), Nat.sub(np, nn)}
    case GT{}:
      Rat{Rat.num(d, 0n), Nat.sub(np, nn)}

def Rat.div(a: Rat, b: Rat) -> Rat:
  match b:
    case Rat{I.Int{+bp, +bnn}, +bd}:
      Rat.mul(a, Rat.inv(bp, bnn, bd, Nat.cmp(bp, bnn), {==}))

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
# Rat.zero_mul: 0 * x = 0. The mirror of Rat.mul_zero, and it needs no
# successor spelling anywhere: the numerator is Int.mul(Int.zero(), xn), whose
# four products all carry the zero literal, and what is left after that is
# mk(Int{0,0}, Nat.mul(1, xd)) -- a diagonal numerator, which is what a zero
# numerator is in the difference presentation, so Rat.mk.diag applies with the
# positivity of Nat.mul(1, xd) from mul_pos. div_self's 1 + ap spelling never
# comes up: mk.diag is stated over a positivity witness and supplies the
# spelling itself (pos_witness, in its own fill).
#
# The positivity hypothesis is what that needs, and it is not cosmetic: at
# xd = 0 mk's divisor is gcd(0, 0) = 0, the denominator division is div(0,0) = 0
# and the result is Rat{Int{0,0}, 0}, which no law compares with Rat.zero() --
# the same stance Rat.add_neg records for a zero denominator.
law Rat.zero_mul:
  for +x: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  {Rat.mul(Rat.zero(), x) == Rat.zero() : Rat}

# Scaling
# =======
#
# Rat.mk.scale is the lemma the whole quotient machinery rests on: normalization
# is natural under scaling, mk(n*k, d*k) == mk(n, d) for k = 1 + kp. It is what
# makes "equal cross products" give "equal normal forms" (Rat.mk.eqv), and it is
# also what any law that composes two *normalized* results needs, because the
# inner Rat.mk has already cancelled a gcd by the time the outer one looks at
# its arguments.
#
# The proof is split into the three Nat coordinates of the result -- the
# normalization is a Rat of three Nats, and each coordinate is its own scalar
# equation -- so that no motive has to spell a whole Rat. The spelling is
# mk.go's own: the scaled numerator has raw coordinates (np*(1+kp), nn*(1+kp)),
# which is exactly what Rat.mk.scale hands mk.go after the Int.mul that scaled
# it has been reduced.
# Rat.mk.eqv: equal cross products give equal normal forms -- the "forward
# direction" of the quotient lemma, and the reason `==` on canonical Rats
# decides rational equality. Its fill is two applications of Rat.mk.scale (each
# side scaled by the other side's denominator) around one congruence, so this is
# where the scaling lemma, gcd_scale and the exact-division cancellation all
# land.
#
# Denominators are written 1 + dp rather than as an arbitrary Nat: a scaling
# factor has to be known positive, and a successor is that for free.
law Rat.mk.eqv:
  for +n1: I.Int
  for +dp1: Nat
  for +n2: I.Int
  for +dp2: Nat
  for +e: {I.Int.mul(n1, I.Int{1n+dp2, 0n}) == I.Int.mul(n2, I.Int{1n+dp1, 0n}) : I.Int}
  {Rat.mk(n1, 1n+dp1) == Rat.mk(n2, 1n+dp2) : Rat}
# Rat.mk.den.pos: the denominator of a normalized fraction is positive. This is
# the one canonicality clause of Rat.mk's output the normalization proves by
# itself -- the numerator is a difference pair by construction, and coprimality
# of the output is the deep part this route deliberately avoids.
law Rat.mk.den.pos:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  {Nat.cmp(0n, Nat.div(1n+dp, Rat.g(np, nn, 1n+dp))) == LT{} : Cmp}

# The value lemma
# ===============
#
# Everything above makes normalization *disappear* on values that are already
# normalized; these two say what normalization *does* to an arbitrary fraction:
#
#     num(mk(n, d)) * d == n * den(mk(n, d))
#
# -- the cross product of mk's output with its input, which is the hypothesis
# Rat.mk.eqv consumes and therefore the one bridge every law that composes two
# normalized results crosses (`mul_assoc`, `add_assoc`, ...). Read as
# "mk(n,d) = n/d", it is the statement that mk preserves the value.
#
# Why it is not free: Rat.mk cancels gcd(|n|, d), so its numerator is div of the
# input's difference coordinate by a gcd, and the cross product is a statement
# about division. What discharges it is div_cross, one call per coordinate, with
# the two divisibility witnesses gcd_divides hands over. What makes the two
# coordinates *different* cases is that the gcd's dividend is |n| = P + Q (P and
# Q the difference pair's own sides, one of them always 0), so `g | P` is only
# available once the comparison says which side is zero -- which is why the
# comparison is a parameter here, exactly as it is in mk.scale.
#
# The denominator is a general d with a positivity hypothesis rather than the
# 1 + dp spelling the rest of the file uses. Two reasons, both load-bearing:
# callers hold products of positive denominators (Rat.mul's xd*yd), and
# rewriting those into successors at every call site would cost an Equal.cong
# over the goal each time; and the positivity hypothesis is what keeps the law
# silent about d = 0, the deliberate junk case. div_cross is stated the same
# way, for the same first reason (its divisor is the computed gcd).
# Rat.mul_assoc
# =============
#
# (x*y)*z = x*(y*z) for canonical values -- the first law that composes two
# *normalized* results, and the one every other composing law is a variation
# of.
#
# The canonical value is spelled the way Rat.mk.fixed and the value lemma spell
# it: numerator Rat.num(np,nn) (the difference pair), denominator 1n+dp, with
# its comparison threaded in as a parameter. That presentation is what makes the
# fill work at all -- Rat.mk.value's right side names a *difference pair*, so a
# numerator that is a raw pair would not meet it (see Rat.num.mul, which is
# exactly that bridge). No coprimality hypothesis is needed: the law holds for
# every Rat of this shape.
#
# The fill is four calls and nothing else: mk.value on each product (the two
# value equations), num.mul on each product (their shapes), Int.scale_cross (the
# cross product of the composed fraction, which is the two value equations)
# scaled by the shared denominator and cancelled with Int.scale_cancel), and
# mk.eqv.raw to turn that cross product into the equality of the two normal
# forms. Every intermediate term is one of those laws' own conclusions, which is
# why nothing here needs a motive.
law Rat.mul_assoc:
  for +c1: Cmp
  for +np1: Nat
  for +nn1: Nat
  for +e1: {c1 == Nat.cmp(np1, nn1) : Cmp}
  for +dp1: Nat
  for +c2: Cmp
  for +np2: Nat
  for +nn2: Nat
  for +e2: {c2 == Nat.cmp(np2, nn2) : Cmp}
  for +dp2: Nat
  for +c3: Cmp
  for +np3: Nat
  for +nn3: Nat
  for +e3: {c3 == Nat.cmp(np3, nn3) : Cmp}
  for +dp3: Nat
  {Rat.mul(Rat.mul(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np2, nn2), 1n+dp2}),
            Rat{Rat.num(np3, nn3), 1n+dp3})
   == Rat.mul(Rat{Rat.num(np1, nn1), 1n+dp1},
              Rat.mul(Rat{Rat.num(np2, nn2), 1n+dp2}, Rat{Rat.num(np3, nn3), 1n+dp3})) : Rat}
# Rat.neg_neg
# ===========
#
# -(-x) = x, for a *canonical* x. This is the first law whose argument is
# another operation's output, and the canonicality hypothesis is not a
# convenience here -- it is required for truth, because == on Rat is
# structural and negation of a non-canonical term comes back mk-headed with
# div/gcd fields. np = 4, nn = 0, dp = 1 is a witness, evaluated:
#
#   neg(neg(Rat{Rat.num(4,0), 2}))   = Rat{Int{2,0}, 1}
#   Rat{Rat.num(4,0), 2}             = Rat{Int{4,0}, 2}
#
# The hypothesis is coprimality of the value -- Rat.mk.fixed's own hypothesis,
# which the identity laws' `fx` also carries -- and what it buys is that the
# value *and its negation* are fixed points of mk: the negation of
# Rat{Rat.num(np,nn), 1+dp} is mk of the swapped pair, whose gcd is the same
# gcd because Rat.mag is symmetric, so mk.fixed applies to it as well and the
# two mk-headed intermediates disappear.
#
# The fill is therefore two mk.fixed calls (one for the intermediate, one for
# the goal's own value) around one congruence, plus the add_comm that moves the
# swapped magnitude back to the stated one. No value equation and no case
# split: neg_neg never needs the cross products the *additive* and
# *multiplicative* composing laws do, because negation does not change the
# denominator.
law Rat.neg_neg:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.neg(Rat.neg(Rat{Rat.num(np, nn), 1n+dp})) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# The additive value equation
# ===========================
#
# Rat.add of two normal forms is the normal form of the *unreduced* sum. This
# is the additive twin of the product shape above, and the bridge every
# additive composing law crosses: the summands are spelled
# mk(Rat.num(np,nn), 1+dp) -- which is what an operation's output looks like,
# since Rat.neg(A) is mk of the swapped pair -- and the conclusion names the
# sum's coordinates the way mk itself sees them, the difference pair of each
# summand scaled by the other summand's denominator.
#
# Why it is not free: mk.eqv.raw compares two normal forms by a cross product
# of their *arguments*, and here those arguments are a sum of two div/gcd-headed
# numerators against a raw pair of products -- a cross product no rearrangement
# of the two mks can produce directly, because the sum's own coordinates are a
# different representative of the same value from the pieces' (that is the
# representative gap Rat.mk.rep closes one level up). What proves it is
# Rat.mk.value on each summand scaled into the shared denominator, merged by the
# ring laws -- the whole assembly is in the fill, and no additive law has to
# touch a div again.
# Rat.add.value: add of two normalized fractions is mk of their unreduced sum.
# d1 = 1+dp1 and d2 = 1+dp2 are successors so that both denominators are
# positive by computation, exactly as the rest of the file spells them, and the
# sum's numerator is written with Int{Nat.sub(np,nn), Nat.sub(nn,np)} -- the
# pair mk destructures Rat.num(np,nn) into.
law Rat.add.value:
  for +np1: Nat
  for +nn1: Nat
  for +dp1: Nat
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  {Rat.add(Rat.mk(Rat.num(np1, nn1), 1n+dp1), Rat.mk(Rat.num(np2, nn2), 1n+dp2))
   == Rat.mk(I.Int.add(
        I.Int.mul(I.Int{Nat.sub(np1, nn1), Nat.sub(nn1, np1)}, I.Int.unit(1n+dp2)),
        I.Int.mul(I.Int{Nat.sub(np2, nn2), Nat.sub(nn2, np2)}, I.Int.unit(1n+dp1))),
      Nat.mul(1n+dp1, 1n+dp2)) : Rat}
# Rat.add_assoc
# =============
#
# (x + y) + z = x + (y + z) for canonical values -- the law that composes a
# sum with a sum, and the second half of the additive block.
#
# The value laws alone do not reach it. add(y,z) is mk-headed with a div/gcd
# numerator, so the outer add's first argument is a *sum of two difference
# pairs*: not one-sided, hence a different representative of the same integer
# from the pair the canonical laws are stated over, and exactly the case
# Rat.mk.trunc bridges (Rat.mk.rep collapses a one-sided pair only). The
# mixed value law then names the outer sum by that assertion's own truncation
# pair, and the cross *sum* that closes the proof -- Rat.mk.eqv.val's
# hypothesis -- is a pure Nat identity in the two inner sums' truncation
# pairs. It is proved from two Nat.sub_cross instances combined criss-cross by
# Nat.cross_add: no new Nat law, and no case analysis anywhere.
#
# Statement and fill follow Rat.mul_assoc: canonical value
# Rat{Rat.num(np,nn), 1n+dp}, no coprimality hypothesis, and no comparison
# parameter -- nothing is cased on, since every sub_diag and sub_cross
# instance is called at an explicit Nat.cmp with {==} evidence.
#
# The fill is Rat.add_assoc.arb read at this law's own coordinates: at
# Rat{Rat.num(np,nn), 1n+dp} each of the general law's three positivity
# hypotheses is Nat.cmp(0n, 1n+dp) up to the definition of Rat.denof, which is
# LT{} by computation, so `{==}` supplies all three. The chain itself -- the two
# Int.mul_scale re-spellings of the inner sums, Rat.mk.trunc, the mixed value law
# per outer add, and the closing Rat.mk.eqv.val at the Nat cross sum -- is
# rat_proofs.bend's Rat.add.arb.coords, at the raw coordinates instead of the
# difference pairs. Nothing is weaker here for that: the general law is stated
# over arbitrary Rats, and this is one instantiation of it.
law Rat.add_assoc:
  for +np1: Nat
  for +nn1: Nat
  for +dp1: Nat
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  for +np3: Nat
  for +nn3: Nat
  for +dp3: Nat
  {Rat.add(Rat.add(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np2, nn2), 1n+dp2}),
            Rat{Rat.num(np3, nn3), 1n+dp3})
   == Rat.add(Rat{Rat.num(np1, nn1), 1n+dp1},
              Rat.add(Rat{Rat.num(np2, nn2), 1n+dp2}, Rat{Rat.num(np3, nn3), 1n+dp3})) : Rat}
# Rat.mul.den.pos / Rat.add.den.pos
# ==================================
#
# The denominator of a product (resp. a sum) of two positive-denominator Rats is
# positive. Both are *derived* facts, not hypotheses: mk's output denominator is
# div(d, G) with G = gcd(mag(U,V), d) a divisor of d, so it is div_pos_wit's
# content once the dividend's spelling is fixed (Rat.div.pos in the proofs file,
# which is the same two-rewrite bridge the rung-2 fills use).
#
# They exist as laws rather than proof-only helpers because the QExt fills need
# them and a helper of rat_proofs.bend is not reachable from qrat_proofs.bend
# (measured: `Rat.div.pos` there fails with "expected : a defined name"). The
# rung-2 distributive laws take the positivity of *three arbitrary* Rats, and a
# QExt coordinate is a product of products, so a fill that instantiates them has
# to build these facts itself.
law Rat.mul.den.pos:
  for +x: Rat
  for +y: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  {Nat.cmp(0n, Rat.denof(Rat.mul(x, y))) == LT{} : Cmp}
law Rat.add.den.pos:
  for +x: Rat
  for +y: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  {Nat.cmp(0n, Rat.denof(Rat.add(x, y))) == LT{} : Cmp}
# Rat.neg.den.pos: the third closure clause, -x's denominator positive when
# x's is. It is needed wherever a fill builds a *negation of a stuck term* --
# the rationalization's -b and -(b^2*d) are exactly that -- because Rat.neg
# destructures its argument before it calls Rat.mk: at a variable the whole
# term is stuck, so no congruence and no mk-headed positivity law reaches it and
# the fact has to arrive as a law stated at the stuck spelling, like its two
# siblings above.
law Rat.neg.den.pos:
  for +x: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  {Nat.cmp(0n, Rat.denof(Rat.neg(x))) == LT{} : Cmp}
# Rat.neg_add
# ===========
#
# -(x + y) = -x + -y, for the canonical presentation of the two summands and
# with no coprimality hypothesis. The statement is true as it stands (evaluated
# at x = 2/3, y = -3/5 both sides are the same Rat), and what makes it provable
# is the pair of bridges above:
#
#   - Rat.add.value turns the right-hand side -- add of two *normalized*
#     summands, both of them the mk Rat.neg produces -- into mk of the
#     unreduced sum, whose numerator is a raw pair of products;
#   - Rat.mk.rep turns the left-hand side's inner value into that same raw
#     spelling, after the negated value equation (Rat.mk.value carried through
#     Int.neg_mul) has moved it to mk(Rat.num(Sn,Sp), d) -- the representative
#     of the negated sum that the raw pair is exactly one mk.rep away from.
#
# Negation never touches a denominator, so no scaling appears anywhere: the
# only arithmetic left is the four Nat.add commutations relating the two raw
# spellings (the coordinates of Int.neg of the sum against the coordinates of
# the negated *pieces*), and the positivity of the one denominator the two
# fractions share.
law Rat.neg_add:
  for +np1: Nat
  for +nn1: Nat
  for +dp1: Nat
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  {Rat.neg(Rat.add(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np2, nn2), 1n+dp2}))
   == Rat.add(Rat.neg(Rat{Rat.num(np1, nn1), 1n+dp1}), Rat.neg(Rat{Rat.num(np2, nn2), 1n+dp2})) : Rat}
# Rat.mul_distrib
# ===============
#
# x * (y + z) = x*y + x*z for canonical values -- the law that makes a product
# meet a *sum*, and the last of the Rat field identities before QExt.
#
# It is the first law whose mk-headed argument is a sum of two difference
# pairs, and the closing step had to be measured twice before it was settled:
# **Rat.mk.eqv.raw cannot close it.** That law's hypothesis is a *cross product*
# between the two arguments' coordinate pairs, and the two numerators here are
# different representatives of the same rational -- the left-hand side's is the
# product of x's numerator with the inner sum's quotient pair (`a1*q2p +
# b1*q2n`), the right-hand side's is a sum of products of the two *products'*
# quotient pairs -- so the product equation is false (at 1/2, -1/3, 1/5 the two
# cross products are 360 against 720 in the reading of PROVING.md: the
# representatives differ, and no rearrangement of the two mks removes that).
# The consumer is Rat.mk.eqv.val, whose hypothesis is the cross *sum* -- the
# value equation -- and the fill reaches it in three comparisons:
#
#   left   mk(num(x)*numof(M2), xd*denof(M2))  against  U_L, the same value
#          written over the inner sum's own inputs (`num(x)*Rat.num(U2,V2)`
#          over `xd*d2`) -- two coordinates of Rat.mk.value at M2, i.e. exactly
#          the two Rat.value.scaled readings the previous unit landed;
#   middle U_L against U_R, the right-hand side's own unreduced sum: no value
#          equation at all, this is the pure Nat identity PROVING.md records as
#          (T) -- `(a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd = P1*Zd + P3*Yd + a1*Q2 +
#          b1*P2` -- multiplied by the common denominator d1*d3. It is proved
#          from the three truncation cross sums plus two pure ring facts that
#          put x's multipliers next to the inner pair's coordinates, combined
#          criss-cross by Nat.cross_add: the padded-hypotheses route, with no
#          case analysis and no new Nat law.
#   right  U_R against the right-hand side, which is *exactly*
#          Rat.add.value -- add of two normal forms is mk of their unreduced
#          sum -- so this step is three rewrites (Rat.mk.rep backwards on each
#          summand, the successor denominators by pos_witness, and
#          Int.mul_scale on the sum's two products) and no cross sum at all.
#
# No coprimality hypothesis and no comparison parameter, exactly like
# Rat.mul_assoc and Rat.add_assoc: nothing is cased on, every Nat.sub_cross and
# Nat.sub_diag instance is called at an explicit Nat.cmp with {==} evidence.
law Rat.mul_distrib:
  for +np1: Nat
  for +nn1: Nat
  for +dp1: Nat
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  for +np3: Nat
  for +nn3: Nat
  for +dp3: Nat
  {Rat.mul(Rat{Rat.num(np1, nn1), 1n+dp1},
           Rat.add(Rat{Rat.num(np2, nn2), 1n+dp2}, Rat{Rat.num(np3, nn3), 1n+dp3}))
   == Rat.add(Rat.mul(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np2, nn2), 1n+dp2}),
              Rat.mul(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np3, nn3), 1n+dp3})) : Rat}
# Rat.mul_neg
# ===========
#
# x * (-y) = -(x * y), for every pair of Rats whose denominators are positive.
#
# The two sides are not a congruence pair: each is a *composition*, an outer
# operation applied to the other operation's output. The raw spellings do line
# up -- the left side's numerator is Int.mul(xn, Int.neg(yn)) and the right
# side's is Int.neg(Int.mul(xn,yn)), which are the same Int constructor pair --
# but that is invisible to the checker here, because Rat.mul destructures its
# second argument and Rat.neg(y) is an mk whose first argument Int.neg(yn) is
# stuck while yn is a variable. So the goal never reduces to the congruence
# shape, and the law needs a route of its own.
#
# The route is that negation *is* multiplication by -1:
#
#   Rat.neg_eq_mul_negone (rat_proofs.bend):  -y = (-1)*y,
#
# an unconditional law (its fill is two congruences, both sides being mk of raw
# pairs one Nat.add_zero per coordinate apart), which turns the statement into
#
#   x*((-1)*y) = (x*(-1))*y = ((-1)*x)*y = (-1)*(x*y)
#
# -- Rat.mul_assoc.arb twice around one Rat.mul_comm. No value law, no cross sum
# and no div/gcd spelling appears, and no Int or Nat arithmetic at all.
#
# The two hypotheses are the positivity of x's and y's denominators, which is
# what Rat.mul_assoc.arb asks for at arbitrary values; the -1 factor's own
# denominator is 1, positive by computation. They are the hypothesis every
# rung-2 law of this file carries, and the ones the QExt layer already states
# about its coefficients -- at a zero denominator mk's output is junk, and no
# law in this file compares two such outputs.
law Rat.mul_neg:
  for +x: Rat
  for +y: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  {Rat.mul(x, Rat.neg(y)) == Rat.neg(Rat.mul(x, y)) : Rat}
# Rat.neg_mul: the same law with the negation on the *left*, (-x)*y = -(x*y).
# Rat.mul_neg cannot be turned around to give this -- its negation is in the
# second factor -- so the fact is stated separately; the fill is Rat.mul_comm,
# Rat.mul_neg and one more commutativity under a congruence, which is why the
# statement is worth having rather than a three-step detour at every use. The
# rationalization needs it three times: b*(-b), d*(-(b*b)) and (-(b*b))*rh.
law Rat.neg_mul:
  for +x: Rat
  for +y: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  {Rat.mul(Rat.neg(x), y) == Rat.neg(Rat.mul(x, y)) : Rat}
# Rat.add_neg
# ===========
#
# x + (-x) = 0 for every Rat with a positive denominator -- the additive
# inverse identity, and the first law here whose add carries an operation's
# output on *both* sides.
#
# It names a specific representative (Rat.zero()), so no congruence can reach
# it: the raw sum of a value with its negation is the diagonal pair Int{T,T}
# over xd*xd -- zero in *value*, but the constructor Rat{Int{T,T}, xd*xd} is not
# Rat.zero() and Int{T,T} is not Int{0,0}. Two bridges close the gap:
#
#   - Rat.mul_comm puts the mk-headed summand (-x) in the slot
#     Rat.add.value.mixed takes, and Rat.mk.rep re-spells its raw numerator
#     Int{xnn,xp} as the truncation pair Rat.num(xnn,xp) that law is stated
#     over -- so the mixed value law lands on mk of the raw sum of two scaled
#     pairs;
#   - Rat.mk.diag turns mk(Int{T,T}, d) into Rat.zero() for *any* positive d,
#     which is the only place the denominator xd*xd enters.
#
# The one piece of arithmetic left is the diagonal itself: the mixed law's
# numerator is a sum of scaled pairs whose two coordinates differ only by the
# order of the products and of the truncations, and they meet at
# mul(sub(xnn,xp) + xp, xd) = mul(sub(xp,xnn) + xnn, xd) -- Nat.mul_add_left
# read backwards, Nat.sub_cross at cmp(xnn,xp), and four mul_zero/add_zero
# steps. No value equation, no cross sum, no coprimality: unlike Rat.neg_neg
# (whose two sides are a raw value and an mk of it), this law's two sides are
# both *compositions*, and the diagonal numerator reaches zero on its own.
#
# The positivity hypothesis is the rung-2 hypothesis again, and it is needed:
# at xd = 0 the sum's denominator is 0, mk's output there is Rat{Int{0,0},0}
# rather than Rat{Int{0,0},1}, and no law compares the two.
law Rat.add_neg:
  for +x: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  {Rat.add(x, Rat.neg(x)) == Rat.zero() : Rat}
# Rat.mul_add_left
# ================
#
# (x + y) * z = x*z + y*z for canonical values -- the mirror of the law above,
# and free from it: `(x + y)*z = z*(x + y) = z*x + z*y = x*z + y*z` is
# Rat.mul_comm, Rat.mul_distrib (at the summands in the other order) and two
# Rat.mul_comms under a congruence -- the same three-step shape Rat.add_exchange
# has on the additive side. No new arithmetic, no cross sum, no case split.
law Rat.mul_add_left:
  for +np1: Nat
  for +nn1: Nat
  for +dp1: Nat
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  for +np3: Nat
  for +nn3: Nat
  for +dp3: Nat
  {Rat.mul(Rat.add(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np2, nn2), 1n+dp2}),
           Rat{Rat.num(np3, nn3), 1n+dp3})
   == Rat.add(Rat.mul(Rat{Rat.num(np1, nn1), 1n+dp1}, Rat{Rat.num(np3, nn3), 1n+dp3}),
              Rat.mul(Rat{Rat.num(np2, nn2), 1n+dp2}, Rat{Rat.num(np3, nn3), 1n+dp3})) : Rat}
# Rat.mul_inv
# ===========
#
# x * x^-1 = 1, stated per branch of the comparison Rat.inv splits on. The two
# branch laws are the two halves of the claim, and between them they carry what
# "x is non-zero" means here: the branch that applies *is* the evidence that
# np != nn, so nothing has to be said about it and no c != EQ side condition has
# to be spelled (this language has no natural form for one).
#
# GT is stated first because that is the branch the rationalization consumes
# when the norm is positive: a divisor whose numerator is positive is the case
# Rat.div's own GT spelling covers, and the payoff law is stated there. It is
# *not* the general case -- an earlier version of this comment said the norm
# a^2 - b^2*d of a non-zero extension is positive, and that is false in d itself:
# the norm is indefinite, so 1 + 2*sqrt 3 (norm -11) has no positive spelling at
# all and no GT law can state it. Measured: that extension against the positive
# spelling 11 multiplies out to -1, not 1. The case waits on an LT twin of the
# payoff law (PROVING.md, round five).
#
# The hypothesis is {GT{} == Nat.cmp(np, nn)}, not the reverse: Rat.inv's own
# parameter is {c == Nat.cmp(np,nn)}, so this is the orientation its caller
# wants, and it is also the one this checker can consume -- a law parameter is
# read by rewriting the goal's RHS-of-e occurrences with the LHS (PROVING.md),
# so {Nat.cmp(np,nn) == GT{}} cannot produce the {GT{} == Nat.cmp(np,nn)} that
# instantiating Rat.inv needs. Same for LT and Nat.cmp_lt_of_gt.
law Rat.mul_inv.gt:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {GT{} == Nat.cmp(np, nn) : Cmp}
  {Rat.mul(Rat{Rat.num(np, nn), 1n+dp},
           Rat.inv(np, nn, 1n+dp, GT{}, e))
   == Rat.one() : Rat}
law Rat.mul_inv.lt:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {LT{} == Nat.cmp(np, nn) : Cmp}
  {Rat.mul(Rat{Rat.num(np, nn), 1n+dp},
           Rat.inv(np, nn, 1n+dp, LT{}, e))
   == Rat.one() : Rat}

# Division
# ========
#
# Rat.div(a, b) is Rat.mul(a, Rat.inv(..)) with the comparison Nat.cmp(bp, bnn)
# computed from b's numerator coordinates and handed to Rat.inv *inside that
# call*. That single argument decides the shape of every law below.
#
# It only reduces when it is a computation on constructors. For a divisor
# spelled Rat{Rat.num(np, nn), 1n+dp} with variables np and nn the comparison is
# stuck -- and it is stuck inside Rat.inv's argument list, next to the {==} whose
# type mentions it, so no `%` step can move it: the pattern would have to rebuild
# that argument list, and Rat.inv's evidence slot wants {x == Nat.cmp(np,nn)}
# while the pattern's own evidence binder has type {GT{} == x}. A derived
# evidence term typechecks in the pattern but fails the goal fit (the fit
# compares the two evidence terms and {==} is not the same term), and {==}
# itself does not typecheck against a stuck equation. Measured, not assumed.
#
# So the divisor's *sign sits in the spelling*: positive is written
# Rat{Rat.num(1n+ap, 0n), 1n+dp} (coordinates 1+ap against 0n), negative is
# Rat{Rat.num(0n, 1n+bp), 1n+dp}. Both make Nat.cmp compute, so Rat.div reduces
# to a plain product by the reciprocal and each law below is a statement about
# that product. This is the mirror of the branch split Rat.mul_inv already makes:
# the spelling *is* the branch evidence, which is why no law needs a c != EQ
# side condition -- and why the two branches must be stated separately.
#
# The reciprocals differ in sign as well as in shape: for a positive divisor y
# the reciprocal reduces to Rat{Rat.num(1n+dp, 0n), 1n+ap}, for a negative one
# to Rat{Rat.num(0n, 1n+dp), 1n+bp}. (Getting that wrong is the one error the
# checker catches only after the whole chain is written.)
# Rat.div.value.gt: the value form, positive divisor, at raw coordinates
law Rat.div.value.gt:
  for +ap: Nat
  for +dp: Nat
  for +Zp: Nat
  for +Zn: Nat
  for +D: Nat
  {Rat.div(Rat{I.Int{Zp, Zn}, D}, Rat{Rat.num(1n+ap, 0n), 1n+dp})
   == Rat.mk(I.Int.mul(I.Int{Zp, Zn}, Rat.num(1n+dp, 0n)),
             Nat.mul(D, 1n+ap)) : Rat}
# Rat.div.value.lt: the same for a negative divisor
law Rat.div.value.lt:
  for +bp: Nat
  for +dp: Nat
  for +Zp: Nat
  for +Zn: Nat
  for +D: Nat
  {Rat.div(Rat{I.Int{Zp, Zn}, D}, Rat{Rat.num(0n, 1n+bp), 1n+dp})
   == Rat.mk(I.Int.mul(I.Int{Zp, Zn}, Rat.num(0n, 1n+dp)),
             Nat.mul(D, 1n+bp)) : Rat}
# Rat.div.value.eq: the divisor is zero -- numerator coordinates 0n against 0n,
# the canonical spelling of a zero divisor -- so the comparison computes to EQ
# and the value is 0/0 written out: Rat.mk(0, 0). That is the value zero, but it
# is *not* the term Rat.zero() (= Rat{Int{0,0}, 1n}), measured: a structural
# x/0 = 0 law cannot exist, and a caller who wants the constructor has to go
# through the value laws (Rat.mk.eqv), not through {==}.
law Rat.div.value.eq:
  for +dp: Nat
  for +Zp: Nat
  for +Zn: Nat
  for +D: Nat
  {Rat.div(Rat{I.Int{Zp, Zn}, D}, Rat{Rat.num(0n, 0n), 1n+dp})
   == Rat.mk(I.Int.mul(I.Int{Zp, Zn}, Rat.num(0n, 0n)),
             Nat.mul(D, 0n)) : Rat}
# Rat.div_self.gt / Rat.div_self.lt: x / x = 1. The branches are what "x is
# non-zero" means here, exactly as for Rat.mul_inv: the branch that applies is
# the evidence of it.
law Rat.div_self.gt:
  for +ap: Nat
  for +dp: Nat
  {Rat.div(Rat{Rat.num(1n+ap, 0n), 1n+dp},
           Rat{Rat.num(1n+ap, 0n), 1n+dp})
   == Rat.one() : Rat}
law Rat.div_self.lt:
  for +bp: Nat
  for +dp: Nat
  {Rat.div(Rat{Rat.num(0n, 1n+bp), 1n+dp},
           Rat{Rat.num(0n, 1n+bp), 1n+dp})
   == Rat.one() : Rat}
# Rat.div_one: x / 1 = x. Branch-free: 1 is the literal Rat.one(), its
# coordinates are 1n and 0n, so Nat.cmp computes to GT with nothing to say.
law Rat.div_one:
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  {Rat.div(Rat{n, d}, Rat.one()) == Rat{n, d} : Rat}
# Rat.div_mul_cancel.gt / Rat.div_mul_cancel.lt: (x / y) * y = x, the field
# axiom, for a positive resp. negative y. px is the positivity of x's
# denominator, which the three-factor associativity law needs.
law Rat.div_mul_cancel.gt:
  for +ap: Nat
  for +dp: Nat
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  {Rat.mul(Rat.div(Rat{n, d}, Rat{Rat.num(1n+ap, 0n), 1n+dp}),
           Rat{Rat.num(1n+ap, 0n), 1n+dp})
   == Rat{n, d} : Rat}
law Rat.div_mul_cancel.lt:
  for +bp: Nat
  for +dp: Nat
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  {Rat.mul(Rat.div(Rat{n, d}, Rat{Rat.num(0n, 1n+bp), 1n+dp}),
           Rat{Rat.num(0n, 1n+bp), 1n+dp})
   == Rat{n, d} : Rat}
# Rat.div_add.gt / Rat.div_add.lt: (x + y) / z = x / z + y / z -- division
# distributes over addition, and with the divisor's sign in the spelling both
# sides are products by the same reciprocal, so this is Rat.mul_add_left.arb.
law Rat.div_add.gt:
  for +ap: Nat
  for +dp: Nat
  for +x: Rat
  for +y: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  {Rat.div(Rat.add(x, y), Rat{Rat.num(1n+ap, 0n), 1n+dp})
   == Rat.add(Rat.div(x, Rat{Rat.num(1n+ap, 0n), 1n+dp}),
              Rat.div(y, Rat{Rat.num(1n+ap, 0n), 1n+dp})) : Rat}
law Rat.div_add.lt:
  for +bp: Nat
  for +dp: Nat
  for +x: Rat
  for +y: Rat
  for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  {Rat.div(Rat.add(x, y), Rat{Rat.num(0n, 1n+bp), 1n+dp})
   == Rat.add(Rat.div(x, Rat{Rat.num(0n, 1n+bp), 1n+dp}),
              Rat.div(y, Rat{Rat.num(0n, 1n+bp), 1n+dp})) : Rat}
# Rat.mul_eq_zero
# ===============
#
#
#     x * y = 0   and   y * q = 1   ==>   x = 0
#
# -- the zero-product law: a product is zero only if a factor is, in the form a
# proof can *use*. "x*y = 0 implies x = 0 or y = 0" has no form in this
# language (an equation has two sides, not a disjunction), so the branch is the
# caller's to take: whoever knows y is non-zero hands over a right inverse q.
# That is exactly what Rat.mul_inv's two branches produce, and their branch
# evidence *is* what "y is non-zero" means here -- so no sign appears in this
# law at all: no GT/LT hypothesis, no numerator spelling, only y * q = 1.
#
# The fill is the four-step chain the statement is shaped around,
#
#     x = x*1 = x*(y*q) = (x*y)*q = 0*q = 0
#
# with Rat.mul_one read backwards, the inverse equation carried by a congruence,
# Rat.mul_assoc.arb read backwards, the zero equation carried by a congruence,
# and Rat.zero_mul to finish. x is spelled Rat{n,d} because Rat.mul_one is
# stated over that spelling (fx is its canonicality hypothesis), and the three
# denominators are positive because mul_assoc.arb's normalization asks for them
# -- not a canonicality condition, the same hypothesis that law's callers pass.
law Rat.mul_eq_zero:
  for +n: I.Int
  for +d: Nat
  for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for +y: Rat
  for +py: {Nat.cmp(0n, Rat.denof(y)) == LT{} : Cmp}
  for +q: Rat
  for +pq: {Nat.cmp(0n, Rat.denof(q)) == LT{} : Cmp}
  for +hq: {Rat.mul(y, q) == Rat.one() : Rat}
  for +hz: {Rat.mul(Rat{n, d}, y) == Rat.zero() : Rat}
  {Rat{n, d} == Rat.zero() : Rat}
