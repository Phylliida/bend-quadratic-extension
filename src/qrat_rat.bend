import Base
import ./int.bend as I
import ./nat.bend as N

# Rat core: the definitions this layer needs, with the two laws `Rat.add_comm`
# and `Rat.mul_comm` restated here so that their fills can live in this
# namespace (\qrat_proofs.bend) instead of reaching into rat.bend's.
#
# Why a second file at all. `Rat.add_comm`/`Rat.mul_comm` are declared in
# rat.bend and *filled* in rat_proofs.bend, and rat_proofs.bend cannot be
# imported: the checker reads its proof-only helper defs out of another
# namespace and dies on the first of them ("expected : a defined name / observed
# : R.Rat.add.piece"). That is PROVING.md's measurement, re-measured here for
# this layer at several import orders. A fill may be attached from a *different*
# file (that is what this file's own laws are for), but the fills that
# rat_proofs.bend attaches cannot be reached from here, so the two Rat facts
# this layer consumes are declared and filled in this closure.
#
# The definitions are rat.bend's own, unchanged: Rat{num, den} with num/den
# standing for a rational, Rat.mk canonicalizing by arithmetic (no match, so no
# case analysis leaks into the laws), and add/neg/sub/mul written exactly as
# rat.bend writes them so that the fills below are the same proofs.

type Rat is Data:
  Rat{num: I.Int, den: Nat}

def Rat.numof(r: Rat) -> I.Int:
  Rat{+n, +d} = r
  n

def Rat.denof(r: Rat) -> Nat:
  Rat{+n, +d} = r
  d

def Rat.zero() -> Rat:
  Rat{I.Int.zero(), 1n}

def Rat.one() -> Rat:
  Rat{I.Int.one(), 1n}

def Rat.num(+np: Nat, +nn: Nat) -> I.Int:
  I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}

def Rat.mag(+np: Nat, +nn: Nat) -> Nat:
  Nat.add(Nat.sub(np, nn), Nat.sub(nn, np))

def Rat.g(+np: Nat, +nn: Nat, +d: Nat) -> Nat:
  N.Nat.gcd(Rat.mag(np, nn), d)

def Rat.mk.go(+np: Nat, +nn: Nat, +d: Nat) -> Rat:
  Rat{I.Int{Nat.div(Nat.sub(np, nn), Rat.g(np, nn, d)),
            Nat.div(Nat.sub(nn, np), Rat.g(np, nn, d))},
      Nat.div(d, Rat.g(np, nn, d))}

def Rat.mk(n: I.Int, d: Nat) -> Rat:
  I.Int{+np, +nn} = n
  Rat.mk.go(np, nn, d)

def Rat.add(x: Rat, y: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat{+yn, +yd} = y
  Rat.mk(I.Int.add(I.Int.mul(xn, I.Int{yd, 0n}), I.Int.mul(yn, I.Int{xd, 0n})),
    Nat.mul(xd, yd))

def Rat.neg(x: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat.mk(I.Int.neg(xn), xd)

def Rat.sub(x: Rat, y: Rat) -> Rat:
  Rat.add(x, Rat.neg(y))

def Rat.mul(x: Rat, y: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat{+yn, +yd} = y
  Rat.mk(I.Int.mul(xn, yn), Nat.mul(xd, yd))

# Rat.mk.canon: mk is the identity on a reduced fraction -- the gcd it cancels
# is 1, so every division is by 1 and the difference pair comes back unchanged.
# This is the shape every "normalization disappears" fact starts from, and the
# reason mk.go is stated over raw coordinates: the divisor it computes is
# literally Rat.g(np, nn, 1+dp), so the coprime hypothesis is about the same
# expression and no rewrite has to reach under a division.
law Rat.mk.canon:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.mk.go(np, nn, 1n+dp) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

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

# Rat.mk.fixed: a reduced fraction in the difference-pair presentation is a
# fixed point of mk -- the canonicality hypothesis the conditional laws take,
# discharged. Transcription-identical to rat.bend's law of the same name (the
# same statement, the same comment); it is restated here because its fill lives
# in this closure, exactly as Rat.add_comm's and Rat.mul_comm's do.
law Rat.mk.fixed:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.mk(Rat.num(np, nn), 1n+dp) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# Rat.neg_neg: -(-x) = x for a canonical x. Transcription-identical to
# rat.bend's law of the same name: the coprime hypothesis is required for truth
# (== on Rat is structural, so negation of a non-canonical term comes back
# mk-headed), and it is Rat.mk.fixed's own hypothesis.
law Rat.neg_neg:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.neg(Rat.neg(Rat{Rat.num(np, nn), 1n+dp})) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# The Rat value machinery the composing law needs
# ===============================================
#
# Rat.add_assoc is a law over the *canonical presentation*, and every law it
# rests on -- the mk.scale block (normalization is natural under scaling), the
# value equation mk.value, the representative bridge mk.rep, the composite
# truncation mk.trunc and the value comparison mk.eqv.val -- is declared in
# rat.bend and filled in rat_proofs.bend. None of them can be reached from
# here: rat_proofs.bend is not importable (its proof-only helpers do not
# resolve across files), and a fill attached there is callable only where it is
# declared. So this block restates rat.bend's own law for each of them, and
# qrat_proofs.bend fills every one of them with the same proof, at the same
# argument names, that rat_proofs.bend writes. The statements are
# transcription-identical to rat.bend's; the only difference is the `R.` prefix
# on the law key -- Rat.mk.value and Rat.mk.rep are also *definitions* in this
# file (the projections the value laws are stated over), so the law keys need
# the prefix a fill attaches to.

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

# Rat.mk.eqv.val: mk is *determined by the value* -- two fractions whose cross
# sums agree normalize to the same Rat, whatever representative of the numerator
# each one carries.
#
# This is the general quotient lemma, and it is what Rat.mk.eqv.raw cannot say.
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
# Its fill is Rat.mk.canon.go doing the representative work: pos_witness turns
# each denominator into a successor, Rat.mk.scale re-spells each side over the
# common denominator d1*d2, mk.canon.go canonicalizes both numerators (with the
# comparisons of the *scaled* pairs threaded in), Int.canon.eqv.bwd turns the
# cross sum into the equality of the two canonical forms, and one congruence
# carries that through mk. No coprimality anywhere; the two denominators are
# positive by hypothesis, exactly as mk.eqv.raw's are.

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
# It is unconditional -- the comparison is the only parameter, and no
# canonicality, coprimality or positivity hypothesis is stated. The fill is
# Rat.mk.eqv.raw at the cross product Rat.mk.value already gives, and the two
# facts that had been blocking it turn out to be one line each:
#
#   - the *positivity* of the output's denominator, which is what an earlier
#     round could not produce, is one div_pos_wit at the gcd spelling *the goal
#     itself carries* (Rat.g of the raw coordinates mk destructured, not
#     Rat.g(np,nn)), with the divisibility witness gcd_divides returns for that
#     same magnitude. Rat.mk.den.pos is at the *other* spelling of that gcd --
#     the unexpanded Rat.mag(np,nn) -- which is why it looked like it should
#     apply verbatim and does not; it is not needed here.
#   - the numerator spelling: Rat.mk.value's right side names
#     Rat.num(raw coordinates), while the statement is written over the
#     difference pair, and the two are one sub_diag per coordinate apart (the
#     same pair of rewrites, with the same flip evidence, that Rat.mk.fixed
#     makes). Those rewrites are reachable by Equal.cong even though they sit
#     under Nat.mul: no congruence has to reach under Nat.div at all.
#
# Rat.mk_idem.raw below is the same law with the denominator as it comes.

# Rat.mk.canon.go: mk is blind to which representative of the numerator's *value*
# it is handed, at the raw-pair level: mk(Int{xp,xn}, d) and
# mk(canon.go(c, xp, xn), d) are the same Rat, for the comparison c that
# Int.canon.go itself cases on. (The name is .go because this is the
# comparison-threaded coordinate spelling, exactly as Int.canon.go is; Rat.mk.canon
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
# The fill is two steps: one congruence putting Rat.num(xp,xn) where canon.go's
# branch value is -- the two are the same pair, since the branch's own sign
# forces one of the two truncations to zero (canon.go's GT value is
# Int{sub(xp,xn), 0}, and sub(xn,xp) is 0 under GT) -- and then Rat.mk.rep read
# backwards, which is that statement verbatim.
law Rat.mk.canon.go:
  for c: Cmp
  for +xp: Nat
  for +xn: Nat
  for +d: Nat
  for +e: {c == Nat.cmp(xp, xn) : Cmp}
  {Rat.mk(I.Int{xp, xn}, d) == Rat.mk(I.Int.canon.go(c, xp, xn), d) : Rat}

# Rat.mk.trunc: mk of a raw pair is mk of the pair's own truncation pair --
# mk(Int{U,V}, d) against mk(Rat.num(sub(U,V), sub(V,U)), d). The two are the
# same integer in two representations (the second has one side zero, and it is
# the presentation Rat.num spells), so this is Rat.mk.canon.go's content with the
# truncations written out instead of canon.go's case split -- and *no comparison
# parameter is needed*: canon.go's branch value is exactly this pair, and sub_diag
# reaches the collapse at the two explicit comparisons Nat.cmp(U,V) and
# Nat.cmp(V,U), so nothing has to be cased on.
#
# This is the bridge a *composite* numerator needs, and the reason Rat.mk.rep is
# not enough for it: a sum of two difference pairs has coordinates that are not
# truncations of anything, so rep's collapse does not apply, while its *canonical*
# coordinates are precisely (sub(U,V), sub(V,U)). With this law a value whose
# numerator is an operation's output (an Int.add of two scaled difference pairs)
# is one step away from the presentation the mixed value law and the composing
# laws are stated over.

# Rat.mk.rep: mk is blind to which representative of the numerator's value it is
# handed. Unconditional, and no comparison parameter is needed: the two
# sub_diags that collapse mag(sub(U,V),sub(V,U)) are instances at the explicit
# comparisons cmp(U,V) and cmp(V,U), so nothing has to be flipped in.
law Rat.mk.rep:
  for +U: Nat
  for +V: Nat
  for +d: Nat
  {Rat.mk(Rat.num(U, V), d) == Rat.mk(I.Int{U, V}, d) : Rat}

# Rat.mk.canon.go: mk is blind to which representative of the numerator's *value*
# it is handed, at the raw-pair level: mk(Int{xp,xn}, d) and
# mk(canon.go(c, xp, xn), d) are the same Rat, for the comparison c that
# Int.canon.go itself cases on. (The name is .go because this is the
# comparison-threaded coordinate spelling, exactly as Int.canon.go is; Rat.mk.canon
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
# The fill is two steps: one congruence putting Rat.num(xp,xn) where canon.go's
# branch value is -- the two are the same pair, since the branch's own sign
# forces one of the two truncations to zero (canon.go's GT value is
# Int{sub(xp,xn), 0}, and sub(xn,xp) is 0 under GT) -- and then Rat.mk.rep read
# backwards, which is that statement verbatim.

# Rat.mk.trunc: mk of a raw pair is mk of the pair's own truncation pair --
# mk(Int{U,V}, d) against mk(Rat.num(sub(U,V), sub(V,U)), d). The two are the
# same integer in two representations (the second has one side zero, and it is
# the presentation Rat.num spells), so this is Rat.mk.canon.go's content with the
# truncations written out instead of canon.go's case split -- and *no comparison
# parameter is needed*: canon.go's branch value is exactly this pair, and sub_diag
# reaches the collapse at the two explicit comparisons Nat.cmp(U,V) and
# Nat.cmp(V,U), so nothing has to be cased on.
#
# This is the bridge a *composite* numerator needs, and the reason Rat.mk.rep is
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
  {Rat.mk(I.Int{U, V}, d) == Rat.mk(Rat.num(Nat.sub(U, V), Nat.sub(V, U)), d) : Rat}

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

# Rat.mk.eqv.val: mk is *determined by the value* -- two fractions whose cross
# sums agree normalize to the same Rat, whatever representative of the numerator
# each one carries.
#
# This is the general quotient lemma, and it is what Rat.mk.eqv.raw cannot say.
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
# Its fill is Rat.mk.canon.go doing the representative work: pos_witness turns
# each denominator into a successor, Rat.mk.scale re-spells each side over the
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
  {Rat.mk(I.Int{xp, xn}, d1) == Rat.mk(I.Int{yp, yn}, d2) : Rat}

# Rat.mk.den.pos: the denominator of a normalized fraction is positive. This is
# the one canonicality clause of Rat.mk's output the normalization proves by
# itself -- the numerator is a difference pair by construction, and coprimality
# of the output is the deep part this route deliberately avoids.

# Rat.add.value.mixed: the same law when only *one* summand is mk-spelled.
#
# Rat.add.value above requires both summands spelled mk(Rat.num(np,nn), 1+dp),
# and that is not the shape the outer add of add_assoc has: there the first
# summand is an operation's output (mk-headed, with a denominator that is a
# *product* of two others) and the second is still a constructor. This is that
# law's mixed twin, and its right-hand side is the same unreduced sum: each
# summand's numerator scaled by the *other* summand's denominator.
#
# Why the first summand is named by the presentation's coordinates (np1, nn1)
# rather than by mk.go's own: mk(Rat.num(np1,nn1), d) destructures the difference
# pair, so the coordinates the value lemma speaks about are
# (sub(np1,nn1), sub(nn1,np1)) -- and those *are* truncations of (np1,nn1), which
# is exactly what makes the two sub_diags (and so the cross product mk.eqv.raw
# consumes) collapse. A numerator that is a sum of two difference pairs has no
# such collapse, which is why the *composite* case is not this law.
#
# The denominators are spelled differently on purpose. The second summand's is
# the successor 1+dp2 its constructor carries, and the first's is the general d
# the mk was handed -- mk's own reduced denominator div(d, G) is not a successor,
# and the value equation's scale has to be d for the cross product to close. d is
# a general Nat with a positivity hypothesis and the *output's* denominator
# positivity as a second one, exactly as Rat.mk.value and Rat.mk_idem.raw take
# them: div_pos_wit concludes at the successor spelling of its dividend, and a
# caller whose d is a product supplies the fact the same way it supplies it to
# those two laws.
#
# The mirror image (constructor first, mk second) is this law through
# Rat.add_comm, so it is not stated separately.
law Rat.add.value.mixed:
  for +np1: Nat
  for +nn1: Nat
  for +d: Nat
  for +pd: {Nat.cmp(0n, d) == LT{} : Cmp}
  for +pq: {Nat.cmp(0n, Rat.denof(Rat.mk(Rat.num(np1, nn1), d))) == LT{} : Cmp}
  for +np2: Nat
  for +nn2: Nat
  for +dp2: Nat
  {Rat.add(Rat.mk(Rat.num(np1, nn1), d), Rat{Rat.num(np2, nn2), 1n+dp2})
   == Rat.mk(I.Int.add(
        I.Int.mul(I.Int{Nat.sub(np1, nn1), Nat.sub(nn1, np1)}, I.Int.unit(1n+dp2)),
        I.Int.mul(I.Int{Nat.sub(np2, nn2), Nat.sub(nn2, np2)}, I.Int.unit(d))),
      Nat.mul(d, 1n+dp2)) : Rat}

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

# Rat.add_exchange
# ================
#
# x + (y + z) = y + (x + z) for canonical values -- the additive block's
# exchange law, and the only law of the block whose proof needs no value
# equation and no cross sum: it is the standard three-step derivation from the
# two laws above it,
#
#   x + (y + z) = (y + z) + x = y + (z + x) = y + (x + z),
#
# i.e. Rat.add_comm, Rat.add_assoc read backwards, and one congruence carrying
# Rat.add_comm under the outer sum. Both of those are proved over exactly this
# presentation, so the fill is three steps and no Nat arithmetic at all -- the
# cross-sum machinery Rat.add_assoc needs plays no part here. (The mirror,
# (x + y) + z = (x + z) + y, is this law through Rat.add_comm, as in Int.)
