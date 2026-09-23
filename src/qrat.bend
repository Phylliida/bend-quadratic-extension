import Base
import ./nat.bend as N
import ./rat.bend as R

# QExt over Rat: the quadratic extension Q(sqrt d) with rational coefficients
# ==========================================================================
#
# Elements are a + b*sqrt(d) with a, b : Rat, exactly as qext.bend's elements
# are re + im*sqrt(d) with re, im : Int. The radicand d is a Nat parameter of
# the *operations* rather than of the type, so one QExt type serves every
# extension level (and, later, towers) -- which is why QExt.zero/one/nat take
# no radicand, exactly as in qext.bend.
#
# Why a new file pair rather than an extension of qext.bend. qext.bend is the
# extension over Int: it is finished, its gate is green, and its two laws are
# stated about Int coefficients. The coefficient type is a type *parameter*
# this language does not have, so the Rat layer cannot reuse those statements
# -- it would have to restate every operation and every law anyway -- and the
# two sets of fills share nothing at all: over Int every composition is
# congruence (Int's operations are constructors, so Int.add_comm is two
# cong steps), while over Rat every composition crosses a normalization and is
# the whole difficulty. Keeping them apart leaves qext.bend and its proof
# untouched. The Int version is not superseded: it is the coefficient-free
# half, and it fixes the shape the laws here are stated in.
#
# The coefficient layer is rat.bend, not a copy of it. This file imports
# `./rat.bend as R` and is filled by qrat_proofs.bend, which imports
# `./rat_proofs.bend` as well -- the same three-file arrangement int_proofs.bend
# uses for nat.bend (laws file + proofs file, then the layer above calls the
# proved laws through the laws file's alias). Every Rat law a QExt fill needs is
# therefore called as `R.Rat.<law>` and not restated: an earlier round carried a
# second copy of Rat's definitions and statements (`src/qrat_rat.bend`) because
# importing rat_proofs.bend appeared impossible, and it was not -- the cause was
# a naming rule, not a limitation (PROVING.md, "Cross-file proof helpers: the
# naming rule, verified").
#
# Laws are stated here and left open; qrat_proofs.bend fills them via
# `def Q.<name>(...)`.
#
# The canonical presentation
# --------------------------
#
# QExt.of spells a QExt value the way every canonical law of rat.bend spells
# its coefficients -- Rat{Rat.num(np, nn), 1n+dp}, a one-sided difference pair
# over a successor -- and it is the presentation QExt.neg_neg is stated in,
# because that is where the Rat-level law it calls (Rat.neg_neg) lives, and the
# shape Rat.mk itself produces. It is *not* the presentation the composing laws
# need any more: QExt.add_assoc is stated over arbitrary values, with the
# positivity of the six coefficients as its hypotheses, which is the form a
# caller holding an operation's output can instantiate. (Assembly of a QExt
# value was never restricted to the presentation: the operations below are
# defined on any two Rats.) The comparison of a numerator is a parameter with
# its evidence, because which side of the difference pair is zero is only known
# from Nat.cmp.
#
# Coprimality is *not* part of the presentation, and is added only to the one
# law whose truth needs it -- QExt.neg_neg, whose Rat-level twin Rat.neg_neg is
# false unconditionally for the same reason: == on Rat is structural. With it,
# the Rat fact Rat.mk.fixed turns "the gcd of the value and the denominator is
# 1" into "mk is the identity here", which is what lets the mk-headed output of
# Rat.neg meet the constructor-headed value it came from.

type QExt is Data:
  QExt{re: R.Rat, im: R.Rat}

# QExt.re(x) / QExt.im(x): the two coefficients as functions. The general
# add_assoc below states its positivity hypotheses about an *arbitrary* QExt's
# coefficients, and a statement has no body to put a match in -- so the
# projection has to be a def, exactly as Rat.numof/Rat.denof are. Both are
# (+a, +b), so a caller can read a coordinate twice.
def QExt.re(x: QExt) -> R.Rat:
  QExt{+a, +b} = x
  a

def QExt.im(x: QExt) -> R.Rat:
  QExt{+a, +b} = x
  b

# QExt.nat(d): the natural d as a rational -- the coefficient of the sqrt(d)*
# sqrt(d) = d step in QExt.mul.
def QExt.nat(d: Nat) -> R.Rat:
  R.Rat{R.Rat.num(d, 0n), 1n}

def QExt.zero() -> QExt:
  QExt{R.Rat.zero(), R.Rat.zero()}

def QExt.one() -> QExt:
  QExt{R.Rat.one(), R.Rat.zero()}

def QExt.add(x: QExt, y: QExt) -> QExt:
  QExt{+xa, +xb} = x
  QExt{+ya, +yb} = y
  QExt{R.Rat.add(xa, ya), R.Rat.add(xb, yb)}

def QExt.neg(x: QExt) -> QExt:
  QExt{+xa, +xb} = x
  QExt{R.Rat.neg(xa), R.Rat.neg(xb)}

def QExt.sub(x: QExt, y: QExt) -> QExt:
  QExt.add(x, QExt.neg(y))

# QExt.of(np, nn, dp, mq, mn, dq): a QExt value spelled the way the laws below
# name their elements -- re = (np - nn)/(1 + dp), im = (mq - mn)/(1 + dq), each
# coordinate in the canonical presentation the Rat laws are stated over. A plain
# abbreviation (nothing is normalized here, and no match is taken on the
# arguments), so it unfolds to the constructor wherever a law or a fill writes
# it; it exists to keep the six-coordinate statements readable.
def QExt.of(+np: Nat, +nn: Nat, +dp: Nat, +mq: Nat, +mn: Nat, +dq: Nat) -> QExt:
  QExt{R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat{R.Rat.num(mq, mn), 1n+dq}}

# QExt.mul(d, x, y) = (xa + xb*sqrt d)(ya + yb*sqrt d)
#                   = (xa*ya + d*xb*yb) + (xa*yb + xb*ya)*sqrt d
def QExt.mul(+d: Nat, x: QExt, y: QExt) -> QExt:
  QExt{+xa, +xb} = x
  QExt{+ya, +yb} = y
  di = QExt.nat(d)
  QExt{R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(di, R.Rat.mul(xb, yb))),
       R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))}

# QExt.conj(x): the conjugate a - b*sqrt(d) -- the real coefficient unchanged,
# the imaginary one negated. It is what gives the extension an inverse at all:
# x * conj(x) is a *rational* number, and QExt.norm names it.
def QExt.conj(+x: QExt) -> QExt:
  QExt{QExt.re(x), R.Rat.neg(QExt.im(x))}

# QExt.norm(d, x): the norm a^2 - b^2 d, as the Rat the product x*conj(x) lands
# on. The radicand coefficient is QExt.nat(d), the same one QExt.mul multiplies
# the imaginary product by, and the subtraction is Rat.sub -- so this is
# literally the cleared denominator of the rationalization, which is why the
# inverse can be stated without a Rat division: conj(x)/norm(d,x) *is* the
# inverse up to the division that is still open.
def QExt.norm(+d: Nat, +x: QExt) -> R.Rat:
  R.Rat.sub(R.Rat.mul(QExt.re(x), QExt.re(x)),
            R.Rat.mul(QExt.nat(d), R.Rat.mul(QExt.im(x), QExt.im(x))))

# The inverse, as an operation
# ============================
#
#     QExt.inv(x, q) = conj(x) / q,     QExt.div(d, x, y, q) = x * QExt.inv(y, q)
#
# -- the rationalization `x^-1 = conj(x)/norm(d,x)`, now a function rather than a
# relation between spelled terms. (Both relations are still stated, as
# QExt.inv.value.gt / .lt and as QExt.mul_inv.gt / .lt below; those laws are what
# say the operation means the inverse, because the operation itself is defined at
# every q.)
#
# The divisor is a *parameter* rather than something the operation computes, and
# that is forced rather than a convenience. QExt.norm(d, x) is an operation's
# output -- a sum of products -- while Rat.div needs a constructor-headed divisor
# for the Nat.cmp inside its Rat.inv argument to compute: at an arbitrary Rat
# that comparison is stuck, inside an argument list, next to the {==} whose type
# mentions it, where no rewrite step can reach (measured in rat.bend's division
# round). So the caller hands over the norm as a spelled rational q --
# `R.Rat.of(1n+ap, 0n, dp)` when the norm is positive, `R.Rat.of(0n, 1n+bp, dp)`
# when it is negative -- and the hZ hypothesis of the inv laws is what says q *is*
# the norm. This is the sign-in-the-spelling discipline of every division law in
# rat.bend, at the QExt level.
#
# Two things this is not. It is not partial: like Rat.inv's EQ branch and Rat.mk
# at denominator 0, it is defined at every q, and no law claims anything about a
# q that is not the norm. And it is not a helper that hides the spelling: the
# coordinate expression in the body is verbatim the left-hand side of
# QExt.inv.value.gt / .lt, so those laws apply to it by conversion alone.
def QExt.inv(+x: QExt, +q: R.Rat) -> QExt:
  QExt{R.Rat.div(QExt.re(x), q), R.Rat.div(R.Rat.neg(QExt.im(x)), q)}

# QExt.div: x / y = x * y^-1 -- a definition, like Rat.sub and Rat.div. Its q is
# the same parameter QExt.inv takes, and it is *y's*: the sign in the spelling is
# the sign of y's norm, which is what makes the product reduce.
def QExt.div(+d: Nat, x: QExt, y: QExt, q: R.Rat) -> QExt:
  QExt.mul(d, x, QExt.inv(y, q))

# QExt.add_comm: x + y = y + x. Holds for every pair: addition is
# componentwise, and Rat.add_comm is unconditional.
law QExt.add_comm:
  for +x: QExt
  for +y: QExt
  {QExt.add(x, y) == QExt.add(y, x) : QExt}

# QExt.mul_comm: x * y = y * x. Also unconditional: the radicand coefficient is
# the same term on both sides (it is a *parameter*, not an operation's output),
# and the Rat ring laws that permute the coefficients hold for every Rat.
law QExt.mul_comm:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  {QExt.mul(d, x, y) == QExt.mul(d, y, x) : QExt}

# QExt.sub_eq_add_neg: x - y = x + (-y) -- true by definition here, exactly as
# Rat.sub_eq_add_neg is
law QExt.sub_eq_add_neg:
  for +x: QExt
  for +y: QExt
  {QExt.sub(x, y) == QExt.add(x, QExt.neg(y)) : QExt}

# QExt.neg_neg: -(-x) = x -- false unconditionally, exactly like Rat.neg_neg,
# and for the same reason: == on QExt is structural, and the coordinates of a
# negated QExt are mk-headed with div/gcd fields.
#
# The hypothesis is the coprimality of *both* coordinates -- the two Rat-level
# values the QExt value is made of, each at the divisor spelling
# Rat.mag(np,nn) that Rat.mk.fixed consumes. It is not a convenience:
# QExt.neg_neg is componentwise Rat.neg_neg, and that Rat law is conditional for
# exactly this reason (rat.bend records np = 4, nn = 0, dp = 1 as a witness).
law QExt.neg_neg:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +g: {N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +h: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat}
  {QExt.neg(QExt.neg(QExt{R.Rat{R.Rat.num(np, nn), 1n+dp},
                          R.Rat{R.Rat.num(mq, mn), 1n+dq}}))
   == QExt{R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat{R.Rat.num(mq, mn), 1n+dq}} : QExt}

# QExt.add_assoc: (x + y) + z = x + (y + z) for the additive group, over
# *arbitrary* QExt values.
#
# Addition is componentwise, so this is one Rat.add_assoc.arb per coordinate and
# nothing else: two calls into rat_proofs.bend's fill, no arithmetic of its own.
#
# The six hypotheses are the positivity of the six coefficients. They are what
# the Rat-level law needs, and they are not avoidable by a bridge: an arbitrary
# Rat's denominator may be zero (Rat{Int{1,0}, 0} is a legal argument, mk's
# behaviour there is junk, and every value lemma in rat.bend carries the same
# hypothesis for exactly that reason), and == on Rat is structural, so no law
# turns an arbitrary Rat into a canonical one. So the hypotheses are stated
# rather than discharged -- and a caller with canonical values supplies each of
# them with `{==}`, by computation.
#
# The presentation: this law needs no canonical spelling at all (that is the
# point of it), and neither do the two commuting laws above. QExt.neg_neg is the
# one law that still uses QExt.of's presentation, because its Rat-level twin is
# false unconditionally.
law QExt.add_assoc:
  for +x: QExt
  for +y: QExt
  for +z: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +gz: {Nat.cmp(0n, R.Rat.denof(QExt.re(z))) == LT{} : Cmp}
  for +hz: {Nat.cmp(0n, R.Rat.denof(QExt.im(z))) == LT{} : Cmp}
  {QExt.add(QExt.add(x, y), z) == QExt.add(x, QExt.add(y, z)) : QExt}

# QExt.mul_assoc: (x * y) * z = x * (y * z) over *arbitrary* QExt values.
#
# Multiplication here is not componentwise -- a coordinate is a sum of products,
# `xa*ya + d*(xb*yb)` -- so this is not one Rat law per coordinate the way
# QExt.add_assoc is. Each coordinate is a ring identity over *stuck* Rat terms
# (products and sums of the six coefficients), which is what the rung-2 laws
# Rat.mul_assoc.arb / Rat.mul_distrib.arb / Rat.mul_add_left.arb exist for: the
# canonical Rat.mul_distrib and Rat.mul_assoc are stated over
# `Rat{Rat.num(np,nn), 1n+dp}` and cannot be instantiated at `Rat.mul(xa,ya)`.
# Rat.add_assoc.arb and the unconditional Rat.add_comm / Rat.mul_comm carry the
# sum-level bookkeeping, and Rat.mul.den.pos / Rat.add.den.pos supply the
# positivity every one of those laws asks for at a *compound* term.
#
# The radicand coefficient QExt.nat(d) is the canonical value
# Rat{Rat.num(d,0), 1}, so its denominator's positivity is `{==}` at every call
# site -- the same computation the canonical laws' fills rely on.
#
# The six hypotheses are the positivity of the six coefficients, exactly as in
# QExt.add_assoc and for the same reason: an arbitrary Rat's denominator may be
# zero, and `==` on Rat is structural, so no law turns an arbitrary Rat into a
# canonical one.
law QExt.mul_assoc:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  for +z: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +gz: {Nat.cmp(0n, R.Rat.denof(QExt.re(z))) == LT{} : Cmp}
  for +hz: {Nat.cmp(0n, R.Rat.denof(QExt.im(z))) == LT{} : Cmp}
  {QExt.mul(d, QExt.mul(d, x, y), z) == QExt.mul(d, x, QExt.mul(d, y, z)) : QExt}

# QExt.mul_distrib: x * (y + z) = x*y + x*z over arbitrary QExt values.
#
# Each coordinate is one rung-2 distributivity and one rearrangement: the
# imaginary coordinate is literally Rat.mul_distrib.arb twice (the coefficient
# products), and the real one is the same law three times, because the radicand
# coefficient D multiplies a sum of products on the inner factor as well. No
# associativity shuffle appears anywhere, which is the whole difference from
# QExt.mul_assoc -- there the two sides' products are associated differently,
# here they are the same products summed in a different order.
law QExt.mul_distrib:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  for +z: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +gz: {Nat.cmp(0n, R.Rat.denof(QExt.re(z))) == LT{} : Cmp}
  for +hz: {Nat.cmp(0n, R.Rat.denof(QExt.im(z))) == LT{} : Cmp}
  {QExt.mul(d, x, QExt.add(y, z))
   == QExt.add(QExt.mul(d, x, y), QExt.mul(d, x, z)) : QExt}

# QExt.mul_conj: x * conj(x) = a^2 - b^2 d -- the division-free form of the
# rationalization, and the fact the inverse rests on.
#
# The product is the conjugate pair, so its *imaginary* coordinate is
# xa*(-xb) + xb*xa: two products that are each other's negative, and zero by the
# additive inverse identity. Its real coordinate is xa*xa + d*(xb*(-xb)), which
# is QExt.norm written with the negation pushed inside the radicand product.
# Both coordinates are therefore Rat chains over the two coefficients and
# nothing else -- `Rat.mul_neg` (`x*(-y) = -(x*y)`) twice in the real one and
# once in the imaginary one, `Rat.mul_comm` and `Rat.add_comm` to put the
# products in the order the identity law wants, and `Rat.add_neg`
# (`x + (-x) = 0`) to close.
#
# The two hypotheses are the positivity of the two coefficients' denominators,
# which is what those Rat laws carry at arbitrary values -- the same rung-2
# hypothesis every composing QExt law above states, and supplied by `{==}` at
# every canonical call site. The radicand coefficient QExt.nat(d) needs none: it
# is Rat{Rat.num(d,0), 1}, whose denominator is 1 by computation.
#
# What is *not* here is the division: `1/(a + b*sqrt d) = conj(x)/norm(d,x)` is
# one Rat division away, and that operation and its laws are their own unit --
# they are in, and the law is QExt.inv.value.gt below.
law QExt.mul_conj:
  for +d: Nat
  for +x: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  {QExt.mul(d, x, QExt.conj(x)) == QExt{QExt.norm(d, x), R.Rat.zero()} : QExt}

# QExt.conj_add: conj(x + y) = conj(x) + conj(y) -- the conjugate is additive.
# One Rat.neg_add.arb on the imaginary coordinate and nothing else: QExt.conj
# touches the imaginary coefficient alone, addition is componentwise, and the real
# coordinate is the *same term* on both sides, so no congruence is even needed.
# The positivity hypotheses are the imaginary coefficients', for the same reason
# as in QExt.neg_add.
law QExt.conj_add:
  for +x: QExt
  for +y: QExt
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  {QExt.conj(QExt.add(x, y)) == QExt.add(QExt.conj(x), QExt.conj(y)) : QExt}

# QExt.conj_conj: conj(conj(x)) = x -- the conjugate is an involution, so the
# additive law above plus this one say conj is an additive automorphism of QExt.
#
# Conditional, and only on the imaginary coordinate: conj(conj(x)) has the real
# coefficient re(x) unchanged and the imaginary one neg(neg(im x)), so the gap is
# one Rat.neg_neg -- the Rat law that is false unconditionally (rat.bend records
# np = 4, nn = 0, dp = 1 as a witness) and needs the imaginary coefficient to be
# a spelled value with coprime numerator and denominator. It is the same
# hypothesis as QExt.neg_neg's, minus the real coordinate's, which this law does
# not touch.
#
# Multiplicativity -- conj(x*y) = conj(x)*conj(y) -- is QExt.conj_mul below,
# stated over QExt.of's six coordinates. It is not free at this presentation: the
# real coordinate needs the Rat identity mul(neg a, neg b) = mul(a, b) at a
# *reduced* pair, which no law reached until this round. The law that does is
# Rat.mul.neg_neg.reduced (rat.bend), the rung-2 twin of the canonical
# Rat.neg_neg: its fill rewrites each negation through Rat.neg.reduced and leaves
# an Int-level identity, so the coprimality of the two coefficients is the only
# Nat fact it consumes. An earlier round recorded the obstruction here as
# unreachable; it was reached by stating the identity at a reduced pair rather
# than by rearranging a stuck product.
#
law QExt.conj_conj:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +h: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat}
  {QExt.conj(QExt.conj(QExt{R.Rat{R.Rat.num(np, nn), 1n+dp},
                           R.Rat{R.Rat.num(mq, mn), 1n+dq}}))
   == QExt{R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat{R.Rat.num(mq, mn), 1n+dq}} : QExt}

# QExt.conj_mul: conj(x*y) = conj(x)*conj(y) -- the multiplicativity of the
# conjugate, and with QExt.conj_add the pair that makes conj a ring
# automorphism of QExt.
#
# Conditional, and only on the two *imaginary* coefficients: the real coordinate
# of the identity reads
#
#     mul(xr,yr) + d*mul(neg xi, neg yi)  ==  mul(xr,yr) + d*mul(xi, yi)
#
# and the surrounding sum cancels, so the whole gap is the bracket -- one call to
# Rat.mul.neg_neg.reduced (rat.bend) under the radicand congruence. The
# imaginary coordinate needs no hypothesis at all: it is the neg_add/mul_neg
# chain QExt.neg_add and QExt.mul_neg already use, over products rather than
# spelled pairs.
#
# The hypotheses are the coprimality of each imaginary coefficient, and they are
# not cosmetic: measured this round, `{==}` on the identity at the unreduced pair
# Rat{Rat.num(4n,0n), 2n} prints expected Rat{Int{0,2},1} against observed
# Rat{Int{0,4},2} -- the left side goes through mk, which cancels the common
# factor, the right is a raw spelling. The real coefficients need nothing: they
# meet inside Rat.add, whose own normalization absorbs whatever spelling they
# carry, and Rat.neg.reduced's hypotheses are spent inside the one Rat law.
law QExt.conj_mul:
  for +d: Nat
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +rp: Nat
  for +rn: Nat
  for +dr: Nat
  for +sp: Nat
  for +sn: Nat
  for +ds: Nat
  for +h1: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat}
  for +h2: {N.Nat.gcd(R.Rat.mag(sp, sn), 1n+ds) == 1n : Nat}
  {QExt.conj(QExt.mul(d, QExt.of(np, nn, dp, mq, mn, dq),
                         QExt.of(rp, rn, dr, sp, sn, ds)))
   == QExt.mul(d, QExt.conj(QExt.of(np, nn, dp, mq, mn, dq)), QExt.conj(QExt.of(rp, rn, dr, sp, sn, ds))) : QExt}

# QExt.mul_one: x * 1 = x, at the canonical presentation.
#
# Stated over QExt.of's six coordinates and not over an arbitrary value, because
# at an arbitrary value it is *false*: == on QExt is structural, the product
# comes back normalized, and the two are not the same term. Measured (PROVING.md,
# round seven): at the unreduced real coordinate Rat{Int{2,0}, 2} the product is
# the canonical Rat{Int{1,0}, 1}, so no variable form of this law exists. The two
# bridges are Rat.mul_one's own hypothesis, one per coordinate -- what a
# canonical value supplies by `{==}` at a literal and with Rat.mk.fixed in
# general.
#
# The real coordinate is where the work is, and not by symmetry: QExt.mul's real
# coordinate multiplies the radicand coefficient QExt.nat(d) by the imaginary
# product, and QExt.nat(d) is Rat{Rat.num(d,0), 1} -- a denominator of base 1,
# which Rat.mul_zero's spelling (Rat{n, 1n+dp}) cannot reach. So the real
# coordinate is the four Rat identity laws plus that one base-denominator zero;
# the imaginary coordinate is three of them.
law QExt.mul_one:
  for +d: Nat
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp) == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  for +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq) == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}
  {QExt.mul(d, QExt.of(np, nn, dp, mq, mn, dq), QExt.one())
   == QExt.of(np, nn, dp, mq, mn, dq) : QExt}

# QExt.add_zero: x + 0 = x, at the canonical presentation -- the additive twin
# of QExt.mul_one, and the same restriction for the same reason. Measured, at the
# unreduced real coordinate Rat{Int{2,0}, 2}: x + 0 comes back Rat{Int{1,0}, 1},
# so == cannot compare the two and no variable form of this law exists. The two
# bridges are Rat.add_zero's own hypothesis, the same pair QExt.mul_one takes.
#
# What makes this law short is that addition is componentwise: each coordinate is
# Rat.add(Rat{n, 1n+dp}, Rat.zero()) and there is no radicand coefficient in
# sight, so the fill is one Rat.add_zero call per coordinate and no helper is
# needed (QExt.mul_one's real coordinate needed qext.nat.mul_zero for the base
# denominator of QExt.nat(d), a term that never appears here). It is also why this
# law takes no `d`: the radicand is QExt.mul's parameter, not QExt.add's.
law QExt.add_zero:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp) == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  for +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq) == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}
  {QExt.add(QExt.of(np, nn, dp, mq, mn, dq), QExt.zero())
   == QExt.of(np, nn, dp, mq, mn, dq) : QExt}

# QExt.zero_add: 0 + x = x -- Rat.zero_add per coordinate, the mirror of the law
# above with the same two bridges, the same canonical presentation and the same
# reason for it.
law QExt.zero_add:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp) == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  for +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq) == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}
  {QExt.add(QExt.zero(), QExt.of(np, nn, dp, mq, mn, dq))
   == QExt.of(np, nn, dp, mq, mn, dq) : QExt}

# QExt.add_neg: x + (-x) = 0, for an *arbitrary* value -- one Rat.add_neg per
# coordinate. No canonical presentation and no bridges, unlike the two laws above:
# Rat.add_neg is unconditional in the spelling (its own hypothesis is the
# denominator's positivity, which is what lets Rat.neg's output, an mk, meet
# Rat.zero), and QExt.neg is componentwise and produces no mk of its own, so ==
# compares the two sides directly here. The positivity of the two coefficients is
# the rung-2 hypothesis, as everywhere in these two layers.
#
# There is deliberately no QExt.neg_add for (-x) + x = 0. In this tree Rat.neg_add
# is the *distribution* law -(x + y) = (-x) + (-y) -- not the flipped inverse --
# so a QExt law with that name would mean something else than its Rat namesake,
# and the flipped form is QExt.add_comm followed by this law, two steps any caller
# can take.
law QExt.add_neg:
  for +x: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  {QExt.add(x, QExt.neg(x)) == QExt.zero() : QExt}

# QExt.neg_add: -(x + y) = (-x) + (-y) -- the distribution of the negation over
# the sum, and the additive half of "conj is a ring homomorphism" below. It is
# Rat.neg_add.arb per coordinate, which is the rung-2 form: the coordinates of an
# arbitrary QExt are operation outputs, and the canonical Rat.neg_add the earlier
# unit added cannot be applied there.
#
# Note which hypotheses are there and why: the negation is componentwise, so
# *both* coordinates are negated sums and both need their summands' positivity --
# the real coordinate's for its own Rat.neg_add.arb, the imaginary coordinate's
# for its. The sum of two reals is formed (as it is on both sides of the law), but
# its positivity is not needed: Rat.neg_add.arb asks for its summands' only.
law QExt.neg_add:
  for +x: QExt
  for +y: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  {QExt.neg(QExt.add(x, y)) == QExt.add(QExt.neg(x), QExt.neg(y)) : QExt}

# QExt.mul_neg / QExt.neg_mul: -(x*y) = x*(-y) = (-x)*y -- the negation laws of
# the product, the multiplicative twins of QExt.neg_add, and both stated over
# *arbitrary* values. Each coordinate is the corresponding Rat law (Rat.mul_neg
# for the first, Rat.neg_mul for the second) plus the same law under a
# congruence, because a product's coordinates are sums of two products and a
# negation has to be pushed to whichever factor carries it.
#
# The full positivity telescope: every coefficient of both factors, as in
# QExt.add_assoc and QExt.mul_assoc, because every coordinate's product is fed to
# a Rat law that asks for its factors' denominators.
law QExt.mul_neg:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  {QExt.mul(d, x, QExt.neg(y)) == QExt.neg(QExt.mul(d, x, y)) : QExt}

law QExt.neg_mul:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  {QExt.mul(d, QExt.neg(x), y) == QExt.neg(QExt.mul(d, x, y)) : QExt}

# QExt.inv.value.gt
# =================
#
#     x^-1 = conj(x) / norm(d, x),   x = a + b*sqrt(d)
#
# -- the rationalization, and the reason the division unit exists: with Rat.div
# the inverse of an extension is the conjugate divided by the norm, and
# QExt.mul_conj plus Rat.mul_inv already say that that product is 1.
#
# The divisor's sign is in the *spelling*, as it is for every division law in
# rat.bend: norm(d,x) is written below as the positive raw pair (1+ap, 0n) over
# 1+dp, and hZ is the equation that says the norm *is* that rational. With the
# sign a literal, the Nat.cmp inside Rat.div's Rat.inv argument computes on
# constructors and the whole left-hand side reduces -- measured, it unfolds to
# Rat.mul(a, d/(1+ap)) with no law and no rewrite, which is what makes the fill
# a rearrangement of products rather than a fight with a stuck comparison.
#
# A caller whose coefficients are literals gets hZ by `{==}`; a caller with a
# variable norm needs it as a hypothesis, exactly as Rat.mul_inv does. The norm
# being positive is what GT carries, so there is no branch-free form of this
# law. That is a real restriction, not a presentational one: the norm is
# indefinite in d, so an extension like 1 + 2*sqrt 3 (norm -11) cannot be stated
# by this law at all -- there is no positive raw pair equal to -11 and no hZ to
# hand over. Measured: that extension against the positive spelling 11 gives -1.
# An LT twin of this law is what that case waits on (PROVING.md, round five).
law QExt.inv.value.gt:
  for +d: Nat
  for +x: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +ap: Nat
  for +dp: Nat
  for +hZ: {R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp} == QExt.norm(d, x) : R.Rat}
  {QExt.mul(d, x,
     QExt{R.Rat.div(QExt.re(x), R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}),
          R.Rat.div(R.Rat.neg(QExt.im(x)), R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp})})
   == QExt.one() : QExt}

# QExt.inv.value.lt
# =================
#
# The same relation, with the norm on the other side of zero:
#
#     x^-1 = conj(x) / norm(d, x),   norm(d, x) = a^2 - b^2*d < 0
#
# and it is not a courtesy twin. The norm is *indefinite* in d, so half of the
# non-zero extensions land here -- 1 + 2*sqrt 3 has norm -11, one of the cases
# the GT law provably cannot state (there is no positive raw pair equal to -11,
# so no hZ exists for it; PROVING.md round five measured that the same product
# built against the positive spelling 11 comes out -1). With this law that
# extension is statable, and `probe.payoff.bend` states it.
#
# The spelling is round four's negative one: `Rat{Rat.num(0n, 1n+bp), 1n+dp}`,
# i.e. -(1+bp)/(1+dp), and hZ says the norm *is* that rational. Nat.cmp(0n, 1n+bp)
# computes to LT on constructors, so Rat.div against it reduces by conversion to
# a product by the reciprocal -- and the reciprocal here is
# `Rat{Rat.num(0n, 1n+dp), 1n+bp}`, the *negative* coordinate shape, not the GT
# reciprocal with a coordinate flipped (measured in round four; the fill below
# relies on it).
#
# Between them the two laws cover every extension whose norm is non-zero. They
# do not cover norm = 0, and that is correct rather than a gap: a^2 = b^2*d can
# happen for non-zero x when d is a perfect square (x = 2 + sqrt 4 = 4), and
# such an extension is a zero divisor with no inverse to state.
law QExt.inv.value.lt:
  for +d: Nat
  for +x: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +bp: Nat
  for +dp: Nat
  for +hZ: {R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp} == QExt.norm(d, x) : R.Rat}
  {QExt.mul(d, x,
     QExt{R.Rat.div(QExt.re(x), R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}),
          R.Rat.div(R.Rat.neg(QExt.im(x)), R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp})})
   == QExt.one() : QExt}

# QExt.mul_inv.gt / QExt.mul_inv.lt
# =================================
#
#     x * x^-1 = 1,   x^-1 = QExt.inv(x, norm's spelling)
#
# -- the operation-level form of the rationalization, one law per sign of the
# norm, and what makes QExt.inv *the* inverse rather than a coordinate
# expression that happens to look right.
#
# These are the value laws above with the spelled constructor replaced by the
# operation: `R.Rat.of(1n+ap, 0n, dp)` names exactly the constructor
# QExt.inv.value.gt spells, and QExt.inv unfolds to exactly that law's
# left-hand-side divisor expression -- so each fill below is one call, and the
# pair is also what keeps the operation and the spelled relation from drifting
# apart, since the one is proved by the other. What the pair adds over the two
# value laws is a name a consumer cites while thinking in operations and a
# statement that does not mention a raw QExt constructor at all.
#
# The same two facts the payoff laws carry are the same two here. There is no
# branch-free form -- the norm is indefinite in d, so no single hZ covers both
# signs, measured in round five on 1 + 2*sqrt 3 -- and norm = 0 is uncovered on
# purpose: a^2 = b^2*d is reachable for non-zero x when d is a square
# (x = 2 + sqrt 4 = 4), and that extension is a zero divisor that has no inverse
# to state.
#
# `x / x = 1` is *not* a third law. QExt.div(d, x, x, q) unfolds to
# QExt.mul(d, x, QExt.inv(x, q)), which is this law's left-hand side verbatim, so
# a caller states the quotient form and cites QExt.mul_inv.gt; at the Rat level
# the twin Rat.div_self.gt is a real law only because Rat.div's divisor there is
# a raw coordinate spelling rather than an operation's output.
law QExt.mul_inv.gt:
  for +d: Nat
  for +x: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +ap: Nat
  for +dp: Nat
  for +hZ: {R.Rat.of(1n+ap, 0n, dp) == QExt.norm(d, x) : R.Rat}
  {QExt.mul(d, x, QExt.inv(x, R.Rat.of(1n+ap, 0n, dp))) == QExt.one() : QExt}

law QExt.mul_inv.lt:
  for +d: Nat
  for +x: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +bp: Nat
  for +dp: Nat
  for +hZ: {R.Rat.of(0n, 1n+bp, dp) == QExt.norm(d, x) : R.Rat}
  {QExt.mul(d, x, QExt.inv(x, R.Rat.of(0n, 1n+bp, dp))) == QExt.one() : QExt}

# QExt.div_add.gt / QExt.div_add.lt
# ================================
#
#     (x + y)/z = x/z + y/z,   one law per sign of the divisor's spelling
#
# -- division is additive in its dividend. This is the law that makes the
# quotient of a *sum* computable, and it is the QExt twin of Rat.div_add: on the
# Rat side the fill is one Rat.mul_add_left.arb, here it is one right
# distributivity over QExt (QExt.mul_distrib is stated on the left, the mirror
# follows by QExt.mul_comm, unconditionally).
#
# Where the divisor comes from is the caller's business here: the law is about
# dividing by the spelled rational, and unlike QExt.mul_inv it carries no hZ.
# Nothing in the fill uses the relation between q and a norm -- what a caller
# establishes is that the two quotients they care about are the two quotients
# this law names, which is the same hZ the inv laws take, used at the call site.
#
# The six hypotheses are the positivity of x's and y's two coordinates each and
# of z's -- the same list QExt.mul_distrib takes, because the fill *is* that law
# at the reciprocal. The positivity of the reciprocal's coordinates, which that
# law also needs, is not a hypothesis: the reciprocal of a spelled rational is a
# constructor (Rat{Rat.num(1n+dp,0n), 1n+ap}), so its denominator is 1n+ap and
# its positivity is {==}, and Rat.mul.den.pos turns z's positivity into the
# quotient's. That derivation lives in the fill, not in the statement -- a
# consumer never writes it.
law QExt.div_add.gt:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  for +z: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +gz: {Nat.cmp(0n, R.Rat.denof(QExt.re(z))) == LT{} : Cmp}
  for +hz: {Nat.cmp(0n, R.Rat.denof(QExt.im(z))) == LT{} : Cmp}
  for +ap: Nat
  for +dp: Nat
  {QExt.div(d, QExt.add(x, y), z, R.Rat.of(1n+ap, 0n, dp))
   == QExt.add(QExt.div(d, x, z, R.Rat.of(1n+ap, 0n, dp)),
               QExt.div(d, y, z, R.Rat.of(1n+ap, 0n, dp))) : QExt}

law QExt.div_add.lt:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  for +z: QExt
  for +gx: {Nat.cmp(0n, R.Rat.denof(QExt.re(x))) == LT{} : Cmp}
  for +hx: {Nat.cmp(0n, R.Rat.denof(QExt.im(x))) == LT{} : Cmp}
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +gz: {Nat.cmp(0n, R.Rat.denof(QExt.re(z))) == LT{} : Cmp}
  for +hz: {Nat.cmp(0n, R.Rat.denof(QExt.im(z))) == LT{} : Cmp}
  for +bp: Nat
  for +dp: Nat
  {QExt.div(d, QExt.add(x, y), z, R.Rat.of(0n, 1n+bp, dp))
   == QExt.add(QExt.div(d, x, z, R.Rat.of(0n, 1n+bp, dp)),
               QExt.div(d, y, z, R.Rat.of(0n, 1n+bp, dp))) : QExt}

# QExt.div_mul_cancel.gt / QExt.div_mul_cancel.lt
# ==============================================
#
#     (x/y)*y = x,   one law per sign of the norm's spelling
#
# The field axiom the pair of division laws above exists for. x is stated in the
# canonical presentation and that is forced, not stylistic: the route runs
# through QExt.mul_one, whose hypothesis is Rat.mul_one's own, and round seven
# measured why the identity has to be asked for in that presentation -- x*1 = x
# is false at a non-canonical value (the real coordinate of mul(x, one()) comes
# back normalized, Rat{Int{2,0},2} printing as Rat{Int{1,0},1}, against an x that
# keeps the unreduced spelling). The two bridges are exactly what QExt.mul_one
# takes, so a caller holding coprimality gets them from Rat.mk.fixed, one call
# per coordinate.
#
# Positivity of x is *not* a hypothesis: a spelled x has successor denominators,
# so Nat.cmp computes it and the fill passes {==}, the same way QExt.div_add's
# fill computes the quotient's positivity. y is arbitrary and its positivity is
# asked for, as everywhere; its norm is the spelled rational, as in
# QExt.mul_inv.

law QExt.div_mul_cancel.gt:
  for +d: Nat
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
            == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  for +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
            == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}
  for +y: QExt
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +ap: Nat
  for +ep: Nat
  for +hZ: {R.Rat.of(1n+ap, 0n, ep) == QExt.norm(d, y) : R.Rat}
  {QExt.mul(d, QExt.div(d, QExt.of(np, nn, dp, mq, mn, dq), y,
                        R.Rat.of(1n+ap, 0n, ep)), y)
   == QExt.of(np, nn, dp, mq, mn, dq) : QExt}

law QExt.div_mul_cancel.lt:
  for +d: Nat
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +mq: Nat
  for +mn: Nat
  for +dq: Nat
  for +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
            == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  for +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
            == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}
  for +y: QExt
  for +gy: {Nat.cmp(0n, R.Rat.denof(QExt.re(y))) == LT{} : Cmp}
  for +hy: {Nat.cmp(0n, R.Rat.denof(QExt.im(y))) == LT{} : Cmp}
  for +bp: Nat
  for +ep: Nat
  for +hZ: {R.Rat.of(0n, 1n+bp, ep) == QExt.norm(d, y) : R.Rat}
  {QExt.mul(d, QExt.div(d, QExt.of(np, nn, dp, mq, mn, dq), y,
                        R.Rat.of(0n, 1n+bp, ep)), y)
   == QExt.of(np, nn, dp, mq, mn, dq) : QExt}
