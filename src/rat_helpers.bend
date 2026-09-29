import Base
import ./nat.bend as N
import ./int.bend as I
import ./int_helpers.bend as IH
import ./rat.bend as R

# Helper laws for Rat
# ===================
#
# The laws a reader of `rat.bend` does not need: variants of the readable
# laws, and the structural plumbing the layers above lean on. Same statements,
# moved here, with their fills still in rat_proofs.bend.
#
# `rat.bend` does not import this file -- a helper law is stated over that
# file's types and operations, so the import only goes one way.

# R.Rat.mk.scale.num: the positive coordinate of mk.go's numerator.
law Rat.mk.scale.num:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.div(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
           R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))
   == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}

# R.Rat.mk.scale.neg: the negative coordinate. The mirror of .num at the swapped
# comparison, which is also how its fill is written: nothing new is proved.
law Rat.mk.scale.neg:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.div(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
           R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))
   == Nat.div(Nat.sub(nn, np), R.Rat.g(np, nn, 1n+dp)) : Nat}

# R.Rat.mk.scale.den: the denominator. Same shape of proof as .num -- the same
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
           R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))
   == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}

# R.Rat.mk.scale.go: the three coordinates together. mk.go's binder is the raw
# coordinates, so this is the statement for a scaled numerator whose Int.mul has
# already been reduced to its two coordinates.
law Rat.mk.scale.go:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {R.Rat.mk.go(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp))
   == R.Rat.mk.go(np, nn, 1n+dp) : R.Rat}

# R.Rat.mk.scale: normalization is natural under scaling by k = 1 + kp. The three
# rewrites at the top of the fill are the only place the *Int* spelling of the
# scaled numerator shows up: Int.mul(x, Int{1+kp, 0}) is
# Int{add(xp*(1+kp), xn*0), add(xp*0, xn*(1+kp))}, and the two zero products
# have to come off before mk.go's raw coordinates are np*(1+kp), nn*(1+kp).
law Rat.mk.scale:
  for +n: I.Int
  for +dp: Nat
  for +kp: Nat
  {R.Rat.mk(I.Int.mul(n, I.Int{1n+kp, 0n}), Nat.mul(1n+dp, 1n+kp)) == R.Rat.mk(n, 1n+dp) : R.Rat}

# R.Rat.mk.eqv.raw: mk.eqv with the denominators as they come -- an arbitrary
# positive Nat rather than the 1n+dp spelling -- and with the cross product in
# that same raw spelling. A consumer that has just composed two fractions holds
# products of denominators (R.Rat.mul's xd*yd, R.Rat.add's) and a cross product
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
  {R.Rat.mk(n1, d1) == R.Rat.mk(n2, d2) : R.Rat}

# R.Rat.mk.eqv.val: mk is *determined by the value* -- two fractions whose cross
# sums agree normalize to the same R.Rat, whatever representative of the numerator
# each one carries.
#
# This is the general quotient lemma, and it is what R.Rat.mk.eqv.raw cannot say.
# mk.eqv.raw's hypothesis is a cross *product* of the two numerators as pairs
# (mul(n1, unit d2) == mul(n2, unit d1)), and that equation is simply false for
# two different representatives of the same integer: 6/24 and -14/24 have equal
# value, but their numerators (6,20) and (0,14) give different products (144,480)
# against (0,336). The hypothesis here is the value equation read as Nats:
#
#     xp*d2 + yn*d1 == yp*d1 + xn*d2
#
# -- (xp - xn)/d1 = (yp - yn)/d2 cleared of denominators -- which is
# Int.canon.eqv's own cross-sum shape and is what every composing law can
# actually produce.
#
# Its fill is R.Rat.mk.canon.go doing the representative work: pos_witness turns
# each denominator into a successor, R.Rat.mk.scale re-spells each side over the
# common denominator d1*d2, mk.canon.go canonicalizes both numerators (with the
# comparisons of the *scaled* pairs threaded in), Int.canon.eqv.bwd turns the
# cross sum into the equality of the two canonical forms, and one congruence
# carries that through mk. No coprimality anywhere; the two denominators are
# positive by hypothesis, exactly as mk.eqv.raw's are.
law Rat.mk.eqv.val:
  for +xp: Nat
  for +xn: Nat
  for +d1: Nat
  for +p1: {Nat.cmp(0n, d1) == LT{} : Cmp}
  for +yp: Nat
  for +yn: Nat
  for +d2: Nat
  for +p2: {Nat.cmp(0n, d2) == LT{} : Cmp}
  for +e: {Nat.add(Nat.mul(xp, d2), Nat.mul(yn, d1)) == Nat.add(Nat.mul(yp, d1), Nat.mul(xn, d2)) : Nat}
  {R.Rat.mk(I.Int{xp, xn}, d1) == R.Rat.mk(I.Int{yp, yn}, d2) : R.Rat}

# R.Rat.mk.value.go: the value equation in mk.go's own coordinate spelling -- both
# Int products already reduced to their coordinate pairs, which is the shape
# Int.mul_scale produces and the shape both halves of the cross product are
# provable in. R.Rat.mk.value is the wrapper that gets the *raw* products into
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
  for wm: N.Nat.divides(R.Rat.g(np, nn, d), R.Rat.mag(np, nn))
  for wd: N.Nat.divides(R.Rat.g(np, nn, d), d)
  {I.Int{Nat.mul(Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, d)), d),
         Nat.mul(Nat.div(Nat.sub(nn, np), R.Rat.g(np, nn, d)), d)}
   == I.Int{Nat.mul(Nat.sub(np, nn), Nat.div(d, R.Rat.g(np, nn, d))),
            Nat.mul(Nat.sub(nn, np), Nat.div(d, R.Rat.g(np, nn, d)))} : I.Int}

# R.Rat.mk.value: mk preserves the value -- the cross product relating a
# normalized fraction to the fraction it came from. The headline law of the
# block above, stated about a R.Rat *value* (hence numof/denof) rather than about
# mk.go's coordinates.
#
# Its fill is the two Int.mul_scale bridges around R.Rat.mk.value.go, which is
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
  {I.Int.mul(R.Rat.numof(R.Rat.mk(I.Int{np, nn}, d)), I.Int{d, 0n})
   == I.Int.mul(R.Rat.num(np, nn), I.Int{R.Rat.denof(R.Rat.mk(I.Int{np, nn}, d)), 0n}) : I.Int}

# R.Rat.mk_idem: mk is the identity on its own output -- the bridge every law
# whose operation argument is *another operation's output* crosses.
#
# An outer operation destructures what the inner one produced, so the numerator
# it writes is R.Rat.numof(M) -- div/gcd terms -- while the raw statements
# (R.Rat.num.mul, R.Rat.mk.value) and the composing laws are written over the
# difference pair the value came from. This law says the two agree: mk of the
# projection is M again, i.e. normalizing a normalized fraction changes
# nothing, which is what lets an outer operation's arguments meet the raw
# spelling.
#
# It is unconditional -- the comparison is the only parameter, and no
# canonicality, coprimality or positivity hypothesis is stated. The fill is
# R.Rat.mk.eqv.raw at the cross product R.Rat.mk.value already gives, and the two
# facts that had been blocking it turn out to be one line each:
#
#   - the *positivity* of the output's denominator, which is what an earlier
#     round could not produce, is one div_pos_wit at the gcd spelling *the goal
#     itself carries* (R.Rat.g of the raw coordinates mk destructured, not
#     R.Rat.g(np,nn)), with the divisibility witness gcd_divides returns for that
#     same magnitude. R.Rat.mk.den.pos is at the *other* spelling of that gcd --
#     the unexpanded R.Rat.mag(np,nn) -- which is why it looked like it should
#     apply verbatim and does not; it is not needed here.
#   - the numerator spelling: R.Rat.mk.value's right side names
#     R.Rat.num(raw coordinates), while the statement is written over the
#     difference pair, and the two are one sub_diag per coordinate apart (the
#     same pair of rewrites, with the same flip evidence, that R.Rat.mk.fixed
#     makes). Those rewrites are reachable by Equal.cong even though they sit
#     under Nat.mul: no congruence has to reach under Nat.div at all.
#
# R.Rat.mk_idem.raw below is the same law with the denominator as it comes.
law Rat.mk_idem:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {R.Rat.mk(R.Rat.numof(R.Rat.mk(R.Rat.num(np, nn), 1n+dp)), R.Rat.denof(R.Rat.mk(R.Rat.num(np, nn), 1n+dp)))
   == R.Rat.mk(R.Rat.num(np, nn), 1n+dp) : R.Rat}

# R.Rat.mk_idem.raw: the same identity with a general denominator, which is the
# form a caller holds after R.Rat.add/R.Rat.mul (their denominators are products of
# two, not a successor literal). Two hypotheses, neither of them canonicality:
#
#   - pd: d is positive -- exactly R.Rat.mk.value's hypothesis, and for the same
#     reason: d = 0 is the junk case no law speaks about.
#   - pq: the output's denominator is positive. This one is not derivable in the
#     fill the way it is above, because d is a variable here: div_pos_wit
#     concludes at the 1 + ap spelling and the witness it needs would have to be
#     re-spelled from divides(G, d) to divides(G, 1 + ap), which is a rewrite of
#     an *evidence type*, not of a term. It costs a caller nothing: the caller's
#     own R.Rat.g/gcd_divides pair at the spelling it wrote M with gives it in one
#     call, exactly as R.Rat.mul_assoc derives the positivity of its two
#     denominators.
law Rat.mk_idem.raw:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +d: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for +pq: {Nat.cmp(0n, R.Rat.denof(R.Rat.mk(R.Rat.num(np, nn), d))) == LT{} : Cmp}
  {R.Rat.mk(R.Rat.numof(R.Rat.mk(R.Rat.num(np, nn), d)), R.Rat.denof(R.Rat.mk(R.Rat.num(np, nn), d)))
   == R.Rat.mk(R.Rat.num(np, nn), d) : R.Rat}

# The representative bridge
# =========================
#
# R.Rat.num(U, V) and Int{U, V} are the same integer in two *representations*:
# R.Rat.num is the one-sided difference pair (sub(U,V), sub(V,U)), Int{U,V} is the
# raw pair. They are equal in value and not ==, and that difference is invisible
# to mk as long as the value is one-sided -- but mk *destructures* what it is
# handed, so it sees the two presentations as different raw coordinates:
# mag(sub(U,V),sub(V,U)) is a sum of two truncations where mag(U,V) is the pair
# itself. The bridge says the normalization does not care: mk's output is the
# same R.Rat either way. This is what the additive laws need, because an Int.add
# numerator is a sum of two difference pairs and R.Rat.mk.value names *that* sum
# in R.Rat.num spelling, while the Int ring laws see the raw pair.

# R.Rat.mk.rep: mk is blind to which representative of the numerator's value it is
# handed. Unconditional, and no comparison parameter is needed: the two
# sub_diags that collapse mag(sub(U,V),sub(V,U)) are instances at the explicit
# comparisons cmp(U,V) and cmp(V,U), so nothing has to be flipped in.
law Rat.mk.rep:
  for +U: Nat
  for +V: Nat
  for +d: Nat
  {R.Rat.mk(R.Rat.num(U, V), d) == R.Rat.mk(I.Int{U, V}, d) : R.Rat}

# R.Rat.mk.canon.go: mk is blind to which representative of the numerator's *value*
# it is handed, at the raw-pair level: mk(Int{xp,xn}, d) and
# mk(canon.go(c, xp, xn), d) are the same R.Rat, for the comparison c that
# Int.canon.go itself cases on. (The name is .go because this is the
# comparison-threaded coordinate spelling, exactly as Int.canon.go is; R.Rat.mk.canon
# above is the unrelated fixed-point law.)
#
# This is the bridge the additive composing laws need. An Int.add numerator is a
# sum of two difference pairs, so its two coordinates are both non-zero for a
# mixed-sign sum -- a *different representative* of the same integer from the
# one-sided pair the canonical laws are stated over -- and mk.eqv.raw compares
# cross products of the representation it is given, so it can never equate the
# two: mul(X, unit d) == mul(Y, unit d) is simply false for two different
# representatives. Canonicalizing both numerators first is what makes "two pairs
# of equal value have equal mks" reachable, and with it the already-proved
# Int.canon.eqv supplies that fact.
#
# The comparison is a parameter with its evidence, for the usual reason: mk.canon
# reaches canon.go's body, which matches on it, and a computed Nat.cmp is not a
# legal scrutinee.
#
# The fill is two steps: one congruence putting R.Rat.num(xp,xn) where canon.go's
# branch value is -- the two are the same pair, since the branch's own sign
# forces one of the two truncations to zero (canon.go's GT value is
# Int{sub(xp,xn), 0}, and sub(xn,xp) is 0 under GT) -- and then R.Rat.mk.rep read
# backwards, which is that statement verbatim.
law Rat.mk.canon.go:
  for c: Cmp
  for +xp: Nat
  for +xn: Nat
  for +d: Nat
  for +e: {c == Nat.cmp(xp, xn) : Cmp}
  {R.Rat.mk(I.Int{xp, xn}, d) == R.Rat.mk(I.Int.canon.go(c, xp, xn), d) : R.Rat}

# R.Rat.mk.trunc: mk of a raw pair is mk of the pair's own truncation pair --
# mk(Int{U,V}, d) against mk(R.Rat.num(sub(U,V), sub(V,U)), d). The two are the
# same integer in two representations (the second has one side zero, and it is
# the presentation R.Rat.num spells), so this is R.Rat.mk.canon.go's content with the
# truncations written out instead of canon.go's case split -- and *no comparison
# parameter is needed*: canon.go's branch value is exactly this pair, and sub_diag
# reaches the collapse at the two explicit comparisons Nat.cmp(U,V) and
# Nat.cmp(V,U), so nothing has to be cased on.
#
# This is the bridge a *composite* numerator needs, and the reason R.Rat.mk.rep is
# not enough for it: a sum of two difference pairs has coordinates that are not
# truncations of anything, so rep's collapse does not apply, while its *canonical*
# coordinates are precisely (sub(U,V), sub(V,U)). With this law a value whose
# numerator is an operation's output (an Int.add of two scaled difference pairs)
# is one step away from the presentation the mixed value law and the composing
# laws are stated over.
law Rat.mk.trunc:
  for +U: Nat
  for +V: Nat
  for +d: Nat
  {R.Rat.mk(I.Int{U, V}, d) == R.Rat.mk(R.Rat.num(Nat.sub(U, V), Nat.sub(V, U)), d) : R.Rat}

# The product shape
# =================
#
# The composing laws (mul_assoc and its siblings) relate two *normalized*
# results, and the only tool for that is R.Rat.mk.eqv, whose hypothesis is a cross
# product of raw numerators. R.Rat.mk.value supplies each factor's cross product,
# but it names its numerator in R.Rat.num spelling -- the difference pair -- while
# the products the operations write are raw coordinates, and those two are not
# the same Int: R.Rat.num(np,nn) is the one-sided pair sub(np,nn), sub(nn,np),
# a different *pair* from Int{np,nn}. The three laws below close that gap.

# R.Rat.dp.eq.right / R.Rat.dp.eq.left: a difference pair with one side zero is its
# own R.Rat.num. That is the whole content of "the product of two difference pairs
# is a difference pair" once the sign is known (R.Rat.num.mul below): one side of
# the product's coordinate pair vanishes, and the two truncations in R.Rat.num
# collapse with sub_zero / sub_zero_left.
law Rat.dp.eq.right:
  for +U: Nat
  for +V: Nat
  for z: {V == 0n : Nat}
  {I.Int{U, V} == R.Rat.num(U, V) : I.Int}

law Rat.dp.eq.left:
  for +U: Nat
  for +V: Nat
  for z: {U == 0n : Nat}
  {I.Int{U, V} == R.Rat.num(U, V) : I.Int}

# R.Rat.num.mul: the product of two difference pairs is R.Rat.num of the product's
# own coordinates -- the product is one-sided again, and which side is zero is
# exactly the sign of the two factors. The two comparisons therefore arrive as
# parameters (a computed Nat.cmp is not a legal scrutinee), the fill splits on
# them, and each branch derives the zeros with sub_of_lt at the flipped
# comparison and finishes with dp.eq.right / dp.eq.left.
#
# This is the bridge the composing laws need between R.Rat.mk.value (whose right
# side is in R.Rat.num spelling) and the Int ring laws (which only see raw
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
  {I.Int.mul(R.Rat.num(np1, nn1), R.Rat.num(np2, nn2))
   == R.Rat.num(Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(np2, nn2)),
                      Nat.mul(Nat.sub(nn1, np1), Nat.sub(nn2, np2))),
              Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(nn2, np2)),
                      Nat.mul(Nat.sub(nn1, np1), Nat.sub(np2, nn2)))) : I.Int}

# R.Rat.add.value.mixed: the same law when only *one* summand is mk-spelled.
#
# R.Rat.add.value above requires both summands spelled mk(R.Rat.num(np,nn), 1+dp),
# and that is not the shape the outer add of add_assoc has: there the first
# summand is an operation's output (mk-headed, with a denominator that is a
# *product* of two others) and the second is still a constructor. This is that
# law's mixed twin, and its right-hand side is the same unreduced sum: each
# summand's numerator scaled by the *other* summand's denominator.
#
# Why the first summand is named by the presentation's coordinates (np1, nn1)
# rather than by mk.go's own: mk(R.Rat.num(np1,nn1), d) destructures the difference
# pair, so the coordinates the value lemma speaks about are
# (sub(np1,nn1), sub(nn1,np1)) -- and those *are* truncations of (np1,nn1), which
# is exactly what makes the two sub_diags (and so the cross product mk.eqv.raw
# consumes) collapse. A numerator that is a sum of two difference pairs has no
# such collapse, which is why the *composite* case is not this law.
#
# The second summand is a *raw* coordinate pair (Zp, Zn) over its own
# denominator D, not the difference pair R.Rat.num(np2,nn2) over a successor. That
# is the form the rung-2 composing law needs: its inputs are arbitrary R.Rat
# *variables*, so what its fill has in hand after destructuring is
# R.Rat{Int{Zp,Zn}, D} -- a raw pair over a denominator that is carried rather than
# computed -- and R.Rat.num(Zp,Zn) is a *different* pair from Int{Zp,Zn} unless one
# of the two coordinates is zero. Reading this law at Zp := sub(np2,nn2),
# Zn := sub(nn2,np2) and D := 1n+dp2 gives back the difference-pair/successor
# statement it had before, because R.Rat.num(np2,nn2) *is*
# Int{sub(np2,nn2), sub(nn2,np2)}.
#
# The three denominators are spelled differently on purpose. The second
# summand's is the general D its constructor carries, and the first's is the
# general d the mk was handed -- mk's own reduced denominator div(d, G) is not a
# successor, and the value equation's scale has to be d for the cross product to
# close. d, D and the *output's* denominator all arrive as general Nats with a
# positivity hypothesis, exactly as R.Rat.mk.value and R.Rat.mk_idem.raw take them:
# div_pos_wit concludes at the successor spelling of its dividend, so a caller
# whose denominator is a product supplies the fact the same way it supplies it to
# those two laws.
#
# The mirror image (constructor first, mk second) is this law through
# R.Rat.add_comm, so it is not stated separately.
law Rat.add.value.mixed:
  for +np1: Nat
  for +nn1: Nat
  for +d: Nat
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for +pq: {Nat.cmp(0n, R.Rat.denof(R.Rat.mk(R.Rat.num(np1, nn1), d))) == LT{} : Cmp}
  for +Zp: Nat
  for +Zn: Nat
  for +D: Nat
  for +pD: {Nat.cmp(0n, D) == LT{} : Cmp}
  {R.Rat.add(R.Rat.mk(R.Rat.num(np1, nn1), d), R.Rat{I.Int{Zp, Zn}, D})
   == R.Rat.mk(I.Int.add(
        I.Int.mul(I.Int{Nat.sub(np1, nn1), Nat.sub(nn1, np1)}, I.Int.unit(D)),
        I.Int.mul(I.Int{Zp, Zn}, I.Int.unit(d))),
      Nat.mul(d, D)) : R.Rat}

# R.Rat.add_assoc.arb
# =================
#
# (x + y) + z = x + (y + z) for *arbitrary* Rats, with the positivity of the
# three input denominators as the only hypotheses. This is the form a caller
# whose summands are pattern variables can use -- a law stated over
# R.Rat.mk(...)/R.Rat{R.Rat.num(np,nn), 1+dp} applications cannot be instantiated at a
# stuck term, which is exactly what an arbitrary R.Rat is -- and it is the form
# the QExt composing laws need, since a QExt coordinate is a R.Rat *variable*.
#
# R.Rat.add_assoc above is the same law in the canonical presentation, with no
# hypothesis at all. Neither is derivable from the other as a statement: the
# canonical form has no positivity slot to fill, and the general form's inputs
# are not mk-shaped, so the extra hypotheses are not a weakening that could be
# discharged. The canonical law's fill is this one at its own coordinates.
#
# The hypotheses are what the *normalization* needs, not a canonicality
# condition: mk's output denominator div(d, G) is positive only when it is a
# quotient of positive numbers, and for an arbitrary input the caller is the only
# one who knows that. Nothing here needs coprimality.
law Rat.add_assoc.arb:
  for +x: R.Rat
  for +y: R.Rat
  for +z: R.Rat
  for +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp}
  for +pz: {Nat.cmp(0n, R.Rat.denof(z)) == LT{} : Cmp}
  {R.Rat.add(R.Rat.add(x, y), z) == R.Rat.add(x, R.Rat.add(y, z)) : R.Rat}

# R.Rat.mul.value.mixed
# ===================
#
# mul(mk(np1/nn1 over d), (Zp - Zn)/D) named by the raw product pair -- the
# multiplicative twin of R.Rat.add.value.mixed above, at the same telescope and
# with the same two positivity hypotheses (d is the denominator mk was handed,
# pq is the one mk's own reduction produced; D is the second factor's).
#
# The difference from the additive law is the whole reason the rung-2
# multiplicative fill is not a mechanical port: an Int.add numerator is a sum of
# two scaled pairs, so the additive law's right side is a *sum* whose coordinates
# are not a constructor and the fill has to assemble them (R.Rat.add.mixed.cross,
# the Int.mul_scale steps, the sub_diag rewrites). An Int.mul numerator of two
# raw coordinate pairs *is* a constructor: Int.mul(Int{P1,Q1}, Int{Zp,Zn})
# reduces to the pair (P1*Zp + Q1*Zn, P1*Zn + Q1*Zp), so this law's right side
# needs no shape law at all, and its fill's cross product is a pure ring
# permutation with no sums in it (R.Rat.mul.mixed.cross).
#
# The second factor is a *raw* coordinate pair (Zp, Zn) over its own D, not a
# difference pair over a successor, exactly as in the additive law -- that is the
# form the rung-2 law needs, since its inputs are arbitrary R.Rat variables. And
# the first summand is mk(R.Rat.num(np1,nn1), d) rather than mk(Int{np1,nn1}, d)
# for the same reason the additive law spells it that way: mk.value's right side
# names R.Rat.num, and R.Rat.mk.trunc is the one step from a raw numerator to it.
law Rat.mul.value.mixed:
  for +np1: Nat
  for +nn1: Nat
  for +d: Nat
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for +pq: {Nat.cmp(0n, R.Rat.denof(R.Rat.mk(R.Rat.num(np1, nn1), d))) == LT{} : Cmp}
  for +Zp: Nat
  for +Zn: Nat
  for +D: Nat
  for +pD: {Nat.cmp(0n, D) == LT{} : Cmp}
  {R.Rat.mul(R.Rat.mk(R.Rat.num(np1, nn1), d), R.Rat{I.Int{Zp, Zn}, D})
   == R.Rat.mk(I.Int.mul(I.Int{Nat.sub(np1, nn1), Nat.sub(nn1, np1)}, I.Int{Zp, Zn}),
        Nat.mul(d, D)) : R.Rat}

# R.Rat.mul_assoc.arb
# =================
#
# (x*y)*z = x*(y*z) for *arbitrary* Rats, with the positivity of the three
# input denominators as the only hypotheses -- the multiplicative twin of
# R.Rat.add_assoc.arb above, at the same telescope and for the same reasons.
#
# It is the statement a caller whose multiplicands are pattern variables can
# instantiate, which is what the QExt composing laws need: `QExt.mul`'s
# coordinates are sums of products of R.Rat *variables*, so every R.Rat law those
# coordinates need has to be usable at a stuck term. R.Rat.mul_assoc below is the
# same law in the canonical presentation and has no hypothesis at all; its fill
# is this law at its own coordinates.
#
# The answer to "why a second rung rather than a bridge" is the same as the
# additive law's, and the multiplicative chain states it more sharply: a
# product of two *raw* coordinate pairs is itself a raw pair, but it is not the
# one-sided difference pair the canonical laws are stated over. `R.Rat.mk.value`
# names its numerator in R.Rat.num spelling, so at a raw pair the value equation
# speaks about `R.Rat.num(cin, din)` -- a *different* Int from `Int{cin, din}`
# whenever both coordinates are non-zero, which is the generic case here (the
# product of two mixed-sign factors has two non-zero coordinates).
#
# What the fill actually uses is measured, and it is *not* the additive one's
# value machinery: the inner products are bridged by R.Rat.mk.rep alone (mk.trunc
# is its truncation-spelled twin and plays no part), and the outer operation
# needs a value law of its own, R.Rat.mul.value.mixed above -- because an outer
# R.Rat.mul destructures the mk the inner one produced, so its numerator is the
# div/gcd-spelled projection and not a raw pair. What makes that law cheap is
# the constructor fact: its right side is a product of two raw pairs, so its
# cross product is a pure Int ring permutation with no sums in it. See the end
# of PROVING.md for the measured route and for the Nat closing, which is where
# the port to the multiplicative case genuinely stops being mechanical.
#
# The hypotheses are what the *normalization* needs -- mk's output denominator
# div(d, G) is positive only when it is a quotient of positive numbers -- not a
# canonicality condition, exactly as in R.Rat.add_assoc.arb. No coprimality.
law Rat.mul_assoc.arb:
  for +x: R.Rat
  for +y: R.Rat
  for +z: R.Rat
  for +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp}
  for +pz: {Nat.cmp(0n, R.Rat.denof(z)) == LT{} : Cmp}
  {R.Rat.mul(R.Rat.mul(x, y), z) == R.Rat.mul(x, R.Rat.mul(y, z)) : R.Rat}

# R.Rat.mul_distrib.arb / R.Rat.mul_add_left.arb
# ==========================================
#
# x*(y + z) = x*y + x*z, and its mirror, for *arbitrary* Rats, with the
# positivity of the three input denominators as the only hypotheses -- the
# distributive laws at the rung-2 telescope, next to R.Rat.mul_assoc.arb and for
# the same reason.
#
# They are what a caller whose factors are *stuck terms* needs, and the QExt
# multiplicative laws are exactly that caller: a `QExt.mul` coordinate is
# `R.Rat.add(R.Rat.mul(..), R.Rat.mul(..))`, an mk-headed sum of mk-headed products, so
# expanding `(a*c + d*(b*e))*f` is distributivity at three arbitrary Rats.
# R.Rat.mul_distrib and R.Rat.mul_add_left below are stated over
# `R.Rat{R.Rat.num(np,nn), 1n+dp}` only, and no unconditional distributive law exists
# in this file at all -- `==` on R.Rat is structural, so no value law or bridge
# turns an arbitrary R.Rat into a canonical one.
#
# The mirror is not proved separately: (x + y)*z = z*(x + y) = z*x + z*y
# = x*z + y*z is R.Rat.mul_comm, the law above and two R.Rat.mul_comms under a
# congruence -- the same three-step shape the canonical R.Rat.mul_add_left has.
law Rat.mul_distrib.arb:
  for +x: R.Rat
  for +y: R.Rat
  for +z: R.Rat
  for +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp}
  for +pz: {Nat.cmp(0n, R.Rat.denof(z)) == LT{} : Cmp}
  {R.Rat.mul(x, R.Rat.add(y, z)) == R.Rat.add(R.Rat.mul(x, y), R.Rat.mul(x, z)) : R.Rat}

law Rat.mul_add_left.arb:
  for +x: R.Rat
  for +y: R.Rat
  for +z: R.Rat
  for +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp}
  for +pz: {Nat.cmp(0n, R.Rat.denof(z)) == LT{} : Cmp}
  {R.Rat.mul(R.Rat.add(x, y), z) == R.Rat.add(R.Rat.mul(x, z), R.Rat.mul(y, z)) : R.Rat}

# R.Rat.add_exchange
# ================
#
# x + (y + z) = y + (x + z) for canonical values -- the additive block's
# exchange law, and the only law of the block whose proof needs no value
# equation and no cross sum: it is the standard three-step derivation from the
# two laws above it,
#
#   x + (y + z) = (y + z) + x = y + (z + x) = y + (x + z),
#
# i.e. R.Rat.add_comm, R.Rat.add_assoc read backwards, and one congruence carrying
# R.Rat.add_comm under the outer sum. Both of those are proved over exactly this
# presentation, so the fill is three steps and no Nat arithmetic at all -- the
# cross-sum machinery R.Rat.add_assoc needs plays no part here. (The mirror,
# (x + y) + z = (x + z) + y, is this law through R.Rat.add_comm, as in Int.)
law Rat.add_exchange:
  for +np1: Nat
  for +nn1: Nat
  for +dp1: Nat
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  for +np3: Nat
  for +nn3: Nat
  for +dp3: Nat
  {R.Rat.add(R.Rat{R.Rat.num(np1, nn1), 1n+dp1},
            R.Rat.add(R.Rat{R.Rat.num(np2, nn2), 1n+dp2}, R.Rat{R.Rat.num(np3, nn3), 1n+dp3}))
   == R.Rat.add(R.Rat{R.Rat.num(np2, nn2), 1n+dp2},
              R.Rat.add(R.Rat{R.Rat.num(np1, nn1), 1n+dp1}, R.Rat{R.Rat.num(np3, nn3), 1n+dp3})) : R.Rat}

# R.Rat.mk.diag
# ===========
#
# A numerator whose two sides are equal is zero, so it normalizes to R.Rat.zero()
# for every positive denominator. This is the law that reads the *sum* of
# x and -x: R.Rat.add scales each summand by the other's denominator, and for the
# two sides of one value those scales are the same product twice, so the raw sum
# is the diagonal pair Int{T,T} -- a pair no value equation can reach, since the
# cross product of a canonical fraction needs a one-sided numerator. The
# diagonal case is where the divergence is visible: gcd(|T - T|, d) is d itself,
# both coordinate divisions are 0/d and the denominator's is d/d.
#
# No coprimality hypothesis, exactly as R.Rat.mk.zero: what makes the reduction
# fire is the magnitude, mag(T,T) = (T - T) + (T - T) = 0, not the divisor.
law Rat.mk.diag:
  for +T: Nat
  for +d: Nat
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  {R.Rat.mk(I.Int{T, T}, d) == R.Rat.zero() : R.Rat}

# R.Rat.neg_add.arb: -(x + y) = (-x) + (-y) for *arbitrary* values -- the rung-2
# twin of R.Rat.neg_add, which is stated over the canonical spelling
# R.Rat{num(np,nn), 1n+dp} because its own fill pushes the negation through mk one
# coordinate at a time.
#
# The gap this fills is real rather than cosmetic: R.Rat.neg_add cannot be applied
# where the summands are operation outputs (a QExt coordinate, say, where the sum
# is an Int.add of two scaled difference pairs), and the QExt negation laws are
# exactly such a place. The route is the one R.Rat.mul_neg uses -- negation *is*
# multiplication by -1 -- and it needs no value law at all:
#
#   -(x+y) = (-1)*(x+y) = (-1)*x + (-1)*y = (-x) + (-y)
#
# R.Rat.neg_eq_mul_negone, R.Rat.mul_distrib.arb, and then that same law under two
# congruences. The only hypotheses are the positivity of x and y, which
# R.Rat.mul_distrib.arb asks for; the -1 factor's own denominator is 1, so its
# positivity is `{==}` by computation, and the sum's is not needed.
law Rat.neg_add.arb:
  for +x: R.Rat
  for +y: R.Rat
  for +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp}
  for +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp}
  {R.Rat.neg(R.Rat.add(x, y)) == R.Rat.add(R.Rat.neg(x), R.Rat.neg(y)) : R.Rat}

# R.Rat.neg.reduced: on a *reduced* spelled value, negation is the flipped
# spelling -- neg(R.Rat{num(np,nn), 1+dp}) = R.Rat{num(nn,np), 1+dp}.
#
# R.Rat.neg_neg's fill already makes exactly this step, but only as the inner half
# of a double negation. Stated on its own it is the rung the product laws were
# missing: it puts neg(X) back in *constructor* form, so that R.Rat.mul can
# destructure it and see the raw difference pair instead of the div/gcd-headed
# output mk produces -- which is what a product of two negations needs before any
# Int-level law can reach it.
#
# The one hypothesis is coprimality, the same one R.Rat.mk.fixed and R.Rat.neg_neg
# carry, and it is not removable: at np = 4, nn = 0, dp = 1 (mag 4, gcd 2) the
# left side is R.Rat{Int{0,2}, 1} while the flipped spelling is R.Rat{Int{0,4}, 2}
# (measured, PROVING.md round eleven).
law Rat.neg.reduced:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +g1: {N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {R.Rat.neg(R.Rat{R.Rat.num(np, nn), 1n+dp}) == R.Rat{R.Rat.num(nn, np), 1n+dp} : R.Rat}

# R.Rat.mul.neg_neg.reduced: negating *both* factors of a product is invisible --
# mul(neg X, neg Y) = mul(X, Y) for spelled X and Y with coprime coordinates.
#
# This is the identity QExt.conj_mul was missing, and it is not a rearrangement
# that holds at arbitrary values: at an unreduced spelling the two sides
# normalize to different terms (the measured obstruction, PROVING.md round ten).
# The two hypotheses are the coordinates' coprimality, which is what makes each
# negation land back in constructor form (R.Rat.neg.reduced) -- and once both
# factors are constructors again, the two sides of the product are the same mk
# applied to two Ints that differ only by
#
#   Int.mul(Int.neg a, Int.neg b) = Int.mul(a, b),
#
# an identity of Int representatives. No Nat gcd fact appears anywhere in the
# fill; the coprime spelling is hypothesis, not work.
law Rat.mul.neg_neg.reduced:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +g1: {N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  for +g2: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat}
  {R.Rat.mul(R.Rat.neg(R.Rat{R.Rat.num(np, nn), 1n+dp}),
           R.Rat.neg(R.Rat{R.Rat.num(mq, mn), 1n+dq}))
   == R.Rat.mul(R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat{R.Rat.num(mq, mn), 1n+dq}) : R.Rat}
