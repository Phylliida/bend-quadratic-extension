import Base
import ./int.bend as I
import ./nat.bend as N
import ./int_proofs.bend as IP
import ./nat_proofs.bend as NP
import ./qrat_rat.bend as R
import ./qrat.bend as Q


# QExt over Rat: proofs
# =====================
#
# Fills every law of qrat.bend. The Rat laws the fills call are *filled here*
# too (`def R.Rat.<name>` below), because a proofs file cannot be imported: a
# third file that imports rat_proofs.bend dies on the proof-only helper defs as
# the checker reads them from another namespace ("expected : a defined name /
# observed : R.Rat.add.piece"), which PROVING.md records. A fill of a law
# declared in an *imported* file does attach from here and stays usable from
# here -- that is what this file's own Rat block is.
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

# --- the Rat facts this layer consumes ---

# Rat.add_comm: both sides are mk of the same denominator (Nat.mul commutes),
# so the numerator's Int.add commutation goes through mk's numerator with one
# cong and the denominator's commutation with a second.
def R.Rat.add_comm(x, y):
  match x y:
    case R.Rat{+xn, +xd} R.Rat{+yn, +yd}:
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.add(I.Int.mul(xn, I.Int{yd, 0n}), I.Int.mul(yn, I.Int{xd, 0n})),
                 Nat.mul(xd, yd)),
        R.Rat.mk(I.Int.add(I.Int.mul(yn, I.Int{xd, 0n}), I.Int.mul(xn, I.Int{yd, 0n})),
                 Nat.mul(xd, yd)),
        R.Rat.mk(I.Int.add(I.Int.mul(yn, I.Int{xd, 0n}), I.Int.mul(xn, I.Int{yd, 0n})),
                 Nat.mul(yd, xd)),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(xd, yd)),
          I.Int.add(I.Int.mul(xn, I.Int{yd, 0n}), I.Int.mul(yn, I.Int{xd, 0n})),
          I.Int.add(I.Int.mul(yn, I.Int{xd, 0n}), I.Int.mul(xn, I.Int{yd, 0n})),
          I.Int.add_comm(I.Int.mul(xn, I.Int{yd, 0n}), I.Int.mul(yn, I.Int{xd, 0n}))),
        Equal.cong(Nat, R.Rat,
          u => R.Rat.mk(I.Int.add(I.Int.mul(yn, I.Int{xd, 0n}), I.Int.mul(xn, I.Int{yd, 0n})), u),
          Nat.mul(xd, yd), Nat.mul(yd, xd), N.mul_comm(xd, yd)))

# Rat.mul_comm: the numerator's two products commute and the denominator's two
# factors commute, each carried through mk by its own cong.
def R.Rat.mul_comm(x, y):
  match x y:
    case R.Rat{+xn, +xd} R.Rat{+yn, +yd}:
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.mul(xn, yn), Nat.mul(xd, yd)),
        R.Rat.mk(I.Int.mul(yn, xn), Nat.mul(xd, yd)),
        R.Rat.mk(I.Int.mul(yn, xn), Nat.mul(yd, xd)),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(xd, yd)),
          I.Int.mul(xn, yn), I.Int.mul(yn, xn), I.Int.mul_comm(xn, yn)),
        Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int.mul(yn, xn), u),
          Nat.mul(xd, yd), Nat.mul(yd, xd), N.mul_comm(xd, yd)))

# Rat.mk.canon: the gcd mk cancels is 1, so each of its three divisions is a
# div-by-1 and the difference pair comes back unchanged. The coprime hypothesis
# is about the *same* expression mk.go computes -- mk.go's divisor is
# Rat.g(np, nn, 1+dp), i.e. that gcd -- so only the divisor itself moves, once,
# and then div_one three times.
def R.Rat.mk.canon(np, nn, dp, g1):
  Equal.trans(R.Rat,
    R.Rat.mk.go(np, nn, 1n+dp),
    R.Rat{I.Int{Nat.div(Nat.sub(np, nn), 1n), Nat.div(Nat.sub(nn, np), 1n)},
          Nat.div(1n+dp, 1n)},
    R.Rat{R.Rat.num(np, nn), 1n+dp},
    Equal.cong(Nat, R.Rat,
      u => R.Rat{I.Int{Nat.div(Nat.sub(np, nn), u), Nat.div(Nat.sub(nn, np), u)},
                 Nat.div(1n+dp, u)},
      R.Rat.g(np, nn, 1n+dp), 1n, g1),
    Equal.trans(R.Rat,
      R.Rat{I.Int{Nat.div(Nat.sub(np, nn), 1n), Nat.div(Nat.sub(nn, np), 1n)},
            Nat.div(1n+dp, 1n)},
      R.Rat{I.Int{Nat.sub(np, nn), Nat.div(Nat.sub(nn, np), 1n)}, Nat.div(1n+dp, 1n)},
      R.Rat{R.Rat.num(np, nn), 1n+dp},
      Equal.cong(Nat, R.Rat,
        u => R.Rat{I.Int{u, Nat.div(Nat.sub(nn, np), 1n)}, Nat.div(1n+dp, 1n)},
        Nat.div(Nat.sub(np, nn), 1n), Nat.sub(np, nn), N.div_one(Nat.sub(np, nn))),
      Equal.trans(R.Rat,
        R.Rat{I.Int{Nat.sub(np, nn), Nat.div(Nat.sub(nn, np), 1n)}, Nat.div(1n+dp, 1n)},
        R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, Nat.div(1n+dp, 1n)},
        R.Rat{R.Rat.num(np, nn), 1n+dp},
        Equal.cong(Nat, R.Rat,
          u => R.Rat{I.Int{Nat.sub(np, nn), u}, Nat.div(1n+dp, 1n)},
          Nat.div(Nat.sub(nn, np), 1n), Nat.sub(nn, np), N.div_one(Nat.sub(nn, np))),
        Equal.cong(Nat, R.Rat,
          u => R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, u},
          Nat.div(1n+dp, 1n), 1n+dp, N.div_one(1n+dp)))))

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

# R.QExt.mul.re: the real coordinate of QExt.mul's commutation, as its own
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
