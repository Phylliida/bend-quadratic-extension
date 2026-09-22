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

# Rat.mk.scale.num: the positive coordinate of mk.go's numerator.
law Rat.mk.scale.num:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.div(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
           Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))
   == Nat.div(Nat.sub(np, nn), Rat.g(np, nn, 1n+dp)) : Nat}

# Rat.mk.scale.neg: the negative coordinate. The mirror of .num at the swapped
# comparison, which is also how its fill is written: nothing new is proved.
law Rat.mk.scale.neg:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.div(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
           Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))
   == Nat.div(Nat.sub(nn, np), Rat.g(np, nn, 1n+dp)) : Nat}

# Rat.mk.scale.den: the denominator. Same shape of proof as .num -- the same
# rewrite of the scaled gcd, and the same div_scale with the other half of the
# divisibility witness -- but the EQ branch is the interesting one here: with
# np = nn the denominator's two sides are d/d and (d*(1+kp))/(d*(1+kp)), equal
# by div_self rather than by 0/d = 0.
law Rat.mk.scale.den:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.div(Nat.mul(1n+dp, 1n+kp),
           Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))
   == Nat.div(1n+dp, Rat.g(np, nn, 1n+dp)) : Nat}

# Rat.mk.scale.go: the three coordinates together. mk.go's binder is the raw
# coordinates, so this is the statement for a scaled numerator whose Int.mul has
# already been reduced to its two coordinates.
law Rat.mk.scale.go:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Rat.mk.go(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp))
   == Rat.mk.go(np, nn, 1n+dp) : Rat}

# Rat.mk.scale: normalization is natural under scaling by k = 1 + kp. The three
# rewrites at the top of the fill are the only place the *Int* spelling of the
# scaled numerator shows up: Int.mul(x, Int{1+kp, 0}) is
# Int{add(xp*(1+kp), xn*0), add(xp*0, xn*(1+kp))}, and the two zero products
# have to come off before mk.go's raw coordinates are np*(1+kp), nn*(1+kp).
law Rat.mk.scale:
  for +n: I.Int
  for +dp: Nat
  for +kp: Nat
  {Rat.mk(I.Int.mul(n, I.Int{1n+kp, 0n}), Nat.mul(1n+dp, 1n+kp)) == Rat.mk(n, 1n+dp) : Rat}

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

# Rat.mk.eqv.raw: mk.eqv with the denominators as they come -- an arbitrary
# positive Nat rather than the 1n+dp spelling -- and with the cross product in
# that same raw spelling. A consumer that has just composed two fractions holds
# products of denominators (Rat.mul's xd*yd, Rat.add's) and a cross product
# whose scales are written as those products; this is the form it can call.
#
# The fill is bookkeeping: pos_witness rewrites each denominator into the
# successor mk.eqv is stated over, the same rewrite is carried through the cross
# product by two congs, and mk.eqv closes it.
law Rat.mk.eqv.raw:
  for +n1: I.Int
  for +d1: Nat
  for +n2: I.Int
  for +d2: Nat
  for +p1: {Nat.cmp(0n, d1) == LT{} : Cmp}
  for +p2: {Nat.cmp(0n, d2) == LT{} : Cmp}
  for e: {I.Int.mul(n1, I.Int{d2, 0n}) == I.Int.mul(n2, I.Int{d1, 0n}) : I.Int}
  {Rat.mk(n1, d1) == Rat.mk(n2, d2) : Rat}

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

# Rat.mk.value.go: the value equation in mk.go's own coordinate spelling -- both
# Int products already reduced to their coordinate pairs, which is the shape
# Int.mul_scale produces and the shape both halves of the cross product are
# provable in. Rat.mk.value is the wrapper that gets the *raw* products into
# this spelling.
#
# The two divisibility witnesses are binders rather than calls to gcd_divides,
# for the reason div_scale and divides_pos_wit take theirs as binders: the
# caller's witnesses are fields of the pair gcd_divides returns, and a pair that
# arrives as a computed value cannot be destructured where it is produced. As
# parameters they can be taken apart, which is what the fill does first (and
# they are linear, so each is read once and the fields -- which are +fields, so
# Many -- are what gets reused).
law Rat.mk.value.go:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +d: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for wm: N.Nat.divides(Rat.g(np, nn, d), Rat.mag(np, nn))
  for wd: N.Nat.divides(Rat.g(np, nn, d), d)
  {I.Int{Nat.mul(Nat.div(Nat.sub(np, nn), Rat.g(np, nn, d)), d),
         Nat.mul(Nat.div(Nat.sub(nn, np), Rat.g(np, nn, d)), d)}
   == I.Int{Nat.mul(Nat.sub(np, nn), Nat.div(d, Rat.g(np, nn, d))),
            Nat.mul(Nat.sub(nn, np), Nat.div(d, Rat.g(np, nn, d)))} : I.Int}

# Rat.mk.value: mk preserves the value -- the cross product relating a
# normalized fraction to the fraction it came from. The headline law of the
# block above, stated about a Rat *value* (hence numof/denof) rather than about
# mk.go's coordinates.
#
# Its fill is the two Int.mul_scale bridges around Rat.mk.value.go, which is
# what the raw spelling buys: the untouched statement is the one a caller has in
# hand after an operation, and the reduced one is the one division can be
# reasoned about in.
law Rat.mk.value:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +d: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  {I.Int.mul(Rat.numof(Rat.mk(I.Int{np, nn}, d)), I.Int{d, 0n})
   == I.Int.mul(Rat.num(np, nn), I.Int{Rat.denof(Rat.mk(I.Int{np, nn}, d)), 0n}) : I.Int}

# Rat.mk_idem: mk is the identity on its own output -- the bridge every law
# whose operation argument is *another operation's output* crosses.
#
# An outer operation destructures what the inner one produced, so the numerator
# it writes is Rat.numof(M) -- div/gcd terms -- while the raw statements
# (Rat.num.mul, Rat.mk.value) and the composing laws are written over the
# difference pair the value came from. This law says the two agree: mk of the
# projection is M again, i.e. normalizing a normalized fraction changes
# nothing, which is what lets an outer operation's arguments meet the raw
# spelling.
#
# Two hypotheses, neither of them canonicality and neither of them about
# coprimality:
#
#   - pd: d is positive. Exactly Rat.mk.value's hypothesis, for the same reason
#     -- d = 0 is the junk case no law speaks about (the denominator is a
#     general d rather than the 1 + dp spelling for the same reason it is in
#     mk.value: callers hold products of positive denominators).
#   - pq: the *output's* denominator is positive. This is the whole reason the
#     law is a bridge rather than a computation. denof(M) is div(d, gcd(...)),
#     and the gcd Rat.mk computes once it has destructured its own
#     difference-pair argument is a different *spelling* of Rat.mag's -- the
#     two are equal by one sub_diag per coordinate -- and no congruence reaches
#     a rewrite under Nat.div (the checker expands Nat.div into divmod form
#     first, see PROVING.md). A caller holding an operation's output has this
#     fact for free: Rat.mk.den.pos at its own gcd spelling, with gcd_divides'
#     witness, is exactly pq. So the hypothesis costs the caller nothing, while
#     deriving it inside the fill is what blocked three earlier rounds.
#     Unconditional mk_idem stays future work.
#
# The fill is Rat.mk.eqv.raw at the cross product Rat.mk.value already gives --
# no coprimality, no case split. The only arithmetic is the two sub_diag
# rewrites that carry mk.value's Rat.num-of-the-raw-coordinates numerator to
# the difference pair this statement is written over (the same pair of
# rewrites, with the same flip evidence, that Rat.mk.fixed makes).
law Rat.mk_idem:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +d: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for +pq: {Nat.cmp(0n, Rat.denof(Rat.mk(Rat.num(np, nn), d))) == LT{} : Cmp}
  {Rat.mk(Rat.numof(Rat.mk(Rat.num(np, nn), d)), Rat.denof(Rat.mk(Rat.num(np, nn), d)))
   == Rat.mk(Rat.num(np, nn), d) : Rat}

# The product shape
# =================
#
# The composing laws (mul_assoc and its siblings) relate two *normalized*
# results, and the only tool for that is Rat.mk.eqv, whose hypothesis is a cross
# product of raw numerators. Rat.mk.value supplies each factor's cross product,
# but it names its numerator in Rat.num spelling -- the difference pair -- while
# the products the operations write are raw coordinates, and those two are not
# the same Int: Rat.num(np,nn) is the one-sided pair sub(np,nn), sub(nn,np),
# a different *pair* from Int{np,nn}. The three laws below close that gap.

# Rat.dp.eq.right / Rat.dp.eq.left: a difference pair with one side zero is its
# own Rat.num. That is the whole content of "the product of two difference pairs
# is a difference pair" once the sign is known (Rat.num.mul below): one side of
# the product's coordinate pair vanishes, and the two truncations in Rat.num
# collapse with sub_zero / sub_zero_left.
law Rat.dp.eq.right:
  for +U: Nat
  for +V: Nat
  for z: {V == 0n : Nat}
  {I.Int{U, V} == Rat.num(U, V) : I.Int}

law Rat.dp.eq.left:
  for +U: Nat
  for +V: Nat
  for z: {U == 0n : Nat}
  {I.Int{U, V} == Rat.num(U, V) : I.Int}

# Rat.num.mul: the product of two difference pairs is Rat.num of the product's
# own coordinates -- the product is one-sided again, and which side is zero is
# exactly the sign of the two factors. The two comparisons therefore arrive as
# parameters (a computed Nat.cmp is not a legal scrutinee), the fill splits on
# them, and each branch derives the zeros with sub_of_lt at the flipped
# comparison and finishes with dp.eq.right / dp.eq.left.
#
# This is the bridge the composing laws need between Rat.mk.value (whose right
# side is in Rat.num spelling) and the Int ring laws (which only see raw
# coordinates): with it, a value equation's difference-pair numerator can be
# replaced by the raw product xn*yn and Int.mul_assoc applies.
law Rat.num.mul:
  for c1: Cmp
  for +np1: Nat
  for +nn1: Nat
  for +e1: {c1 == Nat.cmp(np1, nn1) : Cmp}
  for c2: Cmp
  for +np2: Nat
  for +nn2: Nat
  for +e2: {c2 == Nat.cmp(np2, nn2) : Cmp}
  {I.Int.mul(Rat.num(np1, nn1), Rat.num(np2, nn2))
   == Rat.num(Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(np2, nn2)),
                      Nat.mul(Nat.sub(nn1, np1), Nat.sub(nn2, np2))),
              Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(nn2, np2)),
                      Nat.mul(Nat.sub(nn1, np1), Nat.sub(np2, nn2)))) : I.Int}

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
