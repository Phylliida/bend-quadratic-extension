import Base
import ./nat.bend as N
import ./int.bend as I
import ./rat.bend as R
import ./qrat.bend as Q
import ./nat_proofs.bend as NP
import ./int_proofs.bend as IP
import ./rat_proofs.bend as RP

# QExt over Rat: proofs
# =====================
#
# Fills every law of qrat.bend, and nothing else. The Rat facts the fills call
# are rat.bend's own, filled by the rat_proofs.bend import above and reached
# through the rat.bend alias as `R.Rat.<law>` -- exactly the arrangement
# int_proofs.bend uses for nat.bend's laws (`N.add_comm`, `N.mul_assoc`, ...).
# The laws files come first in the import list and the proofs files after them,
# which is the order this checker needs.
#
# No Rat statement or fill is duplicated here. The earlier round carried a
# second copy of both (`src/qrat_rat.bend` plus a ported block below), because
# importing rat_proofs.bend appeared impossible; the real cause was that 35
# proof-only helper defs in rat_proofs.bend were named with the import-alias
# prefix (`R.Rat.add.piece`), a spelling that resolves only while that file is
# the main file -- the rule PROVING.md records for nat_proofs, whose helpers
# (`Nat.pred`, `NatIsPos`) are bare. With them renamed bare, a third file that
# imports rat.bend + rat_proofs.bend checks, so the copies are gone.
#
# The only helper defs here are the two coordinate witnesses and the two
# QExt.mul coordinate chains, all bare (a helper must not carry the alias
# prefix; only a fill of a law key declared in qrat.bend may).
#
# The QExt laws need three Rat facts and nothing else:
#
#   Rat.add_comm / Rat.mul_comm -- unconditional, and what makes the two
#   *commuting* QExt laws hold with no hypothesis at all;
#
#   Rat.neg_neg -- the one conditional Rat fact, exactly as conditional as it is
#   in rat.bend, and the reason QExt.neg_neg carries coprimality. It consumes
#   Rat.mk.fixed (a reduced fraction is a fixed point of mk), which consumes
#   Rat.mk.canon -- gcd = 1 turns into div by 1 turns into the constructor.
#
# One checker limitation shapes every fill below, and it was measured rather
# than guessed. `Equal.cong` is fine as a *whole* proof (R.Rat.add_comm and
# R.Rat.mul_comm are bare congs), but a cong whose function is a lambda cannot
# be handed to anything: the application's arguments are elaborated before the
# parameter's type is known, so the lambda's binder is typed by the *term being
# rewritten* rather than by the type that term lives in. Measured four ways --
# as a def body ("expected : Nat / observed : Quant"), as an argument of
# Equal.trans ("expected : a / observed : f"), with the lambda handed to a
# wrapper declaring `f: Nat -> Nat` ("expected : the whole goal / observed : the
# goal with one side rewritten"), and with the lambda passed explicitly
# ("expected : Type / observed : non-inferrable term"). What does check is a
# bare cong that rewrites a whole *coordinate* (qext.re/qext.im below), or a cong
# whose position is a def parameter (gcd.at/nat.add.right). Every fill here is
# built from those.

# --- coordinate witnesses ---

# qext.re / qext.im: rewrite one coordinate of a QExt and hold the other. These
# two are the steps every QExt fill is made of.
def qext.re(+y: R.Rat, +a: R.Rat, +b: R.Rat, e: {a == b : R.Rat})
  -> {Q.QExt{a, y} == Q.QExt{b, y} : Q.QExt}:
  Equal.trans(Q.QExt, Q.QExt{a, y}, Q.QExt{b, y}, Q.QExt{b, y},
    Equal.cong(R.Rat, Q.QExt, u => Q.QExt{u, y}, a, b, e), {==})

def qext.im(+x: R.Rat, +a: R.Rat, +b: R.Rat, e: {a == b : R.Rat})
  -> {Q.QExt{x, a} == Q.QExt{x, b} : Q.QExt}:
  Equal.trans(Q.QExt, Q.QExt{x, a}, Q.QExt{x, b}, Q.QExt{x, b},
    Equal.cong(R.Rat, Q.QExt, u => Q.QExt{x, u}, a, b, e), {==})

# --- QExt ---

# QExt.add_comm: addition is componentwise, so this is Rat.add_comm once per
# coordinate -- one qext.re step and one qext.im step.

def Q.QExt.add_comm(x, y):
  match x y:
    case Q.QExt{xa, xb} Q.QExt{ya, yb}:
      Equal.trans(Q.QExt,
        Q.QExt{R.Rat.add(xa, ya), R.Rat.add(xb, yb)},
        Q.QExt{R.Rat.add(ya, xa), R.Rat.add(xb, yb)},
        Q.QExt{R.Rat.add(ya, xa), R.Rat.add(yb, xb)},
        qext.re(R.Rat.add(xb, yb), R.Rat.add(xa, ya), R.Rat.add(ya, xa),
          R.Rat.add_comm(xa, ya)),
        qext.im(R.Rat.add(ya, xa), R.Rat.add(xb, yb), R.Rat.add(yb, xb),
          R.Rat.add_comm(xb, yb)))

# QExt.mul.re: the real coordinate of QExt.mul's commutation, as its own
# chain: the first summand swaps outright, and the second swaps *inside* the
# radicand multiplication (one Rat.mul_comm under a nested cong).

def QExt.mul.re(+d: Nat, +xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat)
  -> {R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb)))
      == R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb))) : R.Rat}:
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))),
    R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))),
    R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb))),
    Equal.cong(R.Rat, R.Rat,
      u => R.Rat.add(u, R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))),
      R.Rat.mul(xa, ya), R.Rat.mul(ya, xa), R.Rat.mul_comm(xa, ya)),
    Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(ya, xa), u),
      R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb)),
      R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(Q.QExt.nat(d), u),
        R.Rat.mul(xb, yb), R.Rat.mul(yb, xb), R.Rat.mul_comm(xb, yb))))

# QExt.mul.im: the imaginary coordinate -- two products that swap, the first
# outright and the second under a cong, then one Rat.add_comm to put the two
# summands in the order the right-hand side writes them.

def QExt.mul.im(+xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat)
  -> {R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))
      == R.Rat.add(R.Rat.mul(ya, xb), R.Rat.mul(yb, xa)) : R.Rat}:
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)),
    R.Rat.add(R.Rat.mul(yb, xa), R.Rat.mul(ya, xb)),
    R.Rat.add(R.Rat.mul(ya, xb), R.Rat.mul(yb, xa)),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)),
      R.Rat.add(R.Rat.mul(yb, xa), R.Rat.mul(xb, ya)),
      R.Rat.add(R.Rat.mul(yb, xa), R.Rat.mul(ya, xb)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat.mul(xb, ya)),
        R.Rat.mul(xa, yb), R.Rat.mul(yb, xa), R.Rat.mul_comm(xa, yb)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(yb, xa), u),
        R.Rat.mul(xb, ya), R.Rat.mul(ya, xb), R.Rat.mul_comm(xb, ya))),
    R.Rat.add_comm(R.Rat.mul(yb, xa), R.Rat.mul(ya, xb)))

# QExt.mul_comm: x * y = y * x. The radicand coefficient is the same term on
# both sides (it is a *parameter*, not an operation's output), so the real
# coordinate is QExt.mul.re and the imaginary one is QExt.mul.im.

def Q.QExt.mul_comm(d, x, y):
  match x y:
    case Q.QExt{xa, xb} Q.QExt{ya, yb}:
      Equal.trans(Q.QExt,
        Q.QExt{R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))),
               R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))},
        Q.QExt{R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb))),
               R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))},
        Q.QExt{R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb))),
               R.Rat.add(R.Rat.mul(ya, xb), R.Rat.mul(yb, xa))},
        qext.re(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)),
          R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))),
          R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb))),
          QExt.mul.re(d, xa, xb, ya, yb)),
        qext.im(R.Rat.add(R.Rat.mul(ya, xa), R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, xb))),
          R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)),
          R.Rat.add(R.Rat.mul(ya, xb), R.Rat.mul(yb, xa)),
          QExt.mul.im(xa, xb, ya, yb)))

# QExt.sub_eq_add_neg: definitional -- QExt.sub is QExt.add(x, QExt.neg(y)).

def Q.QExt.sub_eq_add_neg(x, y):
  {==}

# QExt.add_assoc: addition is componentwise, so this is one Rat.add_assoc.arb
# per coordinate -- one qext.re step and one qext.im step, with no arithmetic of
# its own. The two matches are what makes the operations reduce and what puts the
# law's hypotheses at the coefficient spelling the Rat-level law wants: both
# `QExt.re(x)` and `Rat.denof(xa)` are the same term once x is the constructor.
# The six hypotheses are spent as they are (the re step takes the three real
# ones, the im step the three imaginary ones), and nothing is rewritten but a
# whole coordinate.

def Q.QExt.add_assoc(x, y, z, gx, hx, gy, hy, gz, hz):
  match x y z:
    case Q.QExt{xa, xb} Q.QExt{ya, yb} Q.QExt{za, zb}:
      Equal.trans(Q.QExt,
        Q.QExt{R.Rat.add(R.Rat.add(xa, ya), za), R.Rat.add(R.Rat.add(xb, yb), zb)},
        Q.QExt{R.Rat.add(xa, R.Rat.add(ya, za)), R.Rat.add(R.Rat.add(xb, yb), zb)},
        Q.QExt{R.Rat.add(xa, R.Rat.add(ya, za)), R.Rat.add(xb, R.Rat.add(yb, zb))},
        qext.re(R.Rat.add(R.Rat.add(xb, yb), zb),
          R.Rat.add(R.Rat.add(xa, ya), za), R.Rat.add(xa, R.Rat.add(ya, za)),
          R.Rat.add_assoc.arb(xa, ya, za, gx, gy, gz)),
        qext.im(R.Rat.add(xa, R.Rat.add(ya, za)),
          R.Rat.add(R.Rat.add(xb, yb), zb), R.Rat.add(xb, R.Rat.add(yb, zb)),
          R.Rat.add_assoc.arb(xb, yb, zb, hx, hy, hz)))

# QExt.neg_neg: negation is componentwise and does not touch a denominator, so
# this is Rat.neg_neg once per coordinate -- one qext.re step and one qext.im
# step. The Rat-level work (the negation of a canonical value coming back
# mk-headed, the swapped magnitude's gcd, the two mk.fixed applications) is
# rat_proofs.bend's fill, called here at the law's own telescope: the comparison
# is the literal Nat.cmp of the coordinate and the evidence for it is `{==}`,
# exactly as rat_proofs.bend passes them for its own inner mk.fixed. Nothing
# here cases on anything.

def Q.QExt.neg_neg(np, nn, dp, g, mq, mn, dq, h):
  Equal.trans(Q.QExt,
    Q.QExt{R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(np, nn), 1n+dp})),
           R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(mq, mn), 1n+dq}))},
    Q.QExt{R.Rat{R.Rat.num(np, nn), 1n+dp},
           R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(mq, mn), 1n+dq}))},
    Q.QExt{R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat{R.Rat.num(mq, mn), 1n+dq}},
    qext.re(R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(mq, mn), 1n+dq})),
      R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(np, nn), 1n+dp})),
      R.Rat{R.Rat.num(np, nn), 1n+dp},
      R.Rat.neg_neg(Nat.cmp(np, nn), np, nn, dp, {==}, g)),
    qext.im(R.Rat{R.Rat.num(np, nn), 1n+dp},
      R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(mq, mn), 1n+dq})),
      R.Rat{R.Rat.num(mq, mn), 1n+dq},
      R.Rat.neg_neg(Nat.cmp(mq, mn), mq, mn, dq, {==}, h)))
