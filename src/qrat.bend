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
