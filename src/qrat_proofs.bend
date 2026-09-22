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

# --- the two further Rat laws this layer consumes ---

# Rat.mk.fixed: the fill is rat_proofs.bend's, transcription for transcription
# except that the names resolve through this file's aliases: `Rat.mag` is
# qrat_rat.bend's own def, and the two sub_diag instances that collapse the
# two-fold truncation are Nat laws of nat.bend called at explicit comparisons
# (the second at the flipped one, whose evidence is the flip of e -- the only
# place Cmp.flip appears, and it appears as a *lambda body*, the one spelling
# the checker accepts).
def R.Rat.mk.fixed(c, np, nn, dp, e, g1):
  %Equal.sym(Nat,
    Nat.sub(Nat.sub(np, nn), Nat.sub(nn, np)),
    Nat.sub(np, nn),
    N.sub_diag(c, np, nn, e))
    : {R.Rat{I.Int{Nat.div(_, N.Nat.gcd(Nat.add(_, Nat.sub(Nat.sub(nn, np), Nat.sub(np, nn))), 1n+dp)),
                   Nat.div(Nat.sub(Nat.sub(nn, np), Nat.sub(np, nn)),
                     N.Nat.gcd(Nat.add(_, Nat.sub(Nat.sub(nn, np), Nat.sub(np, nn))), 1n+dp))},
              Nat.div(1n+dp, N.Nat.gcd(Nat.add(_, Nat.sub(Nat.sub(nn, np), Nat.sub(np, nn))), 1n+dp))}
        == R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, 1n+dp} : R.Rat}
  %Equal.sym(Nat,
    Nat.sub(Nat.sub(nn, np), Nat.sub(np, nn)),
    Nat.sub(nn, np),
    N.sub_diag(N.Cmp.flip(c), nn, np,
      Equal.trans(Cmp, N.Cmp.flip(c), N.Cmp.flip(Nat.cmp(np, nn)), Nat.cmp(nn, np),
        Equal.cong(Cmp, Cmp, N.Cmp.flip, c, Nat.cmp(np, nn), e),
        Equal.trans(Cmp, N.Cmp.flip(Nat.cmp(np, nn)), N.Cmp.flip(N.Cmp.flip(Nat.cmp(nn, np))), Nat.cmp(nn, np),
          Equal.cong(Cmp, Cmp, N.Cmp.flip, Nat.cmp(np, nn), N.Cmp.flip(Nat.cmp(nn, np)), N.cmp_antisym(np, nn)),
          N.flip_flip(Nat.cmp(nn, np))))))
    : {R.Rat{I.Int{Nat.div(Nat.sub(np, nn), N.Nat.gcd(Nat.add(Nat.sub(np, nn), _), 1n+dp)),
                   Nat.div(_, N.Nat.gcd(Nat.add(Nat.sub(np, nn), _), 1n+dp))},
              Nat.div(1n+dp, N.Nat.gcd(Nat.add(Nat.sub(np, nn), _), 1n+dp))}
        == R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, 1n+dp} : R.Rat}
  %Equal.sym(Nat, N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp), 1n, g1)
    : {R.Rat{I.Int{Nat.div(Nat.sub(np, nn), _), Nat.div(Nat.sub(nn, np), _)}, Nat.div(1n+dp, _)}
        == R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, 1n+dp} : R.Rat}
  %Equal.sym(Nat, Nat.div(Nat.sub(np, nn), 1n), Nat.sub(np, nn), N.div_one(Nat.sub(np, nn)))
    : {R.Rat{I.Int{_, Nat.div(Nat.sub(nn, np), 1n)}, Nat.div(1n+dp, 1n)}
        == R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, 1n+dp} : R.Rat}
  %Equal.sym(Nat, Nat.div(Nat.sub(nn, np), 1n), Nat.sub(nn, np), N.div_one(Nat.sub(nn, np)))
    : {R.Rat{I.Int{Nat.sub(np, nn), _}, Nat.div(1n+dp, 1n)}
        == R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, 1n+dp} : R.Rat}
  %Equal.sym(Nat, Nat.div(1n+dp, 1n), 1n+dp, N.div_one(1n+dp))
    : {R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, _}
        == R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, 1n+dp} : R.Rat}
  {==}

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

# nat.mag.sub: Rat.mag(sub(b,a), sub(a,b)) == Rat.mag(a, b) -- the divisor
# spelling mk computes for the pair Rat.num(b,a) against the spelling Rat.mag is
# stated over. The pair (sub(b,a), sub(a,b)) *is* the truncation pair of
# (a, b) with its two sides swapped, so both of Rat.num's coordinates are
# already the two truncations: the re-spelling is the Nat identity
#
#     sub(b,a) + sub(a,b) == sub(a,b) + sub(b,a),
#
# i.e. the commutativity of the sum the magnitude is -- reached here with no
# comparison, no sub_self and no cancellation.
#
# The route the earlier round recorded as failing is the one that tries to
# *collapse* sub(sub(b,a), sub(a,b)) with `N.sub_self(Nat.sub(nn,np))`: that
# law concludes at the pair's own two sides, sub(sub(b,a), sub(b,a)), and the
# term this divisor carries has sub(a,b) in the second slot. sub_cross is the
# law that closes exactly that gap -- its conclusion is
# add(sub(X,Y), Y) == add(sub(Y,X), X), so at (X,Y) := (b-a, a-b) the left side
# is add(sub(sub(b,a),sub(a,b)), sub(a,b)), which is one add_comm away from
# add(sub(a,b), sub(sub(b,a),sub(a,b))) and hence one `cong` plus one `trans`
# away from the goal. The measurements that pin this: sub_self's conclusion is
# too narrow for the second slot (checked, the message is `expected :
# {Nat.sub(nn, np) == 0n} / observed : {Nat.sub(Nat.sub(nn, np),
# Nat.sub(nn, np)) == 0n}`), and add_cancel does not reach either, because
# `Nat.add` matches on its first argument and the padding sub(a,b) sits on the
# right of both products rather than as a shared leading summand.
#
# The `Nat.cmp(sub(b,a), sub(a,b))` with `{==}` is the comparison sub_cross
# demands (it matches on it, and a computed Nat.cmp is not a legal scrutinee);
# nothing is cased on anywhere in the fill.
# nat.mag.sym: the sum the magnitude is does not depend on the order of the two
# truncations -- Nat.add commutes, and the two truncations are the same pair
# with its sides swapped. Rat.neg_neg's own fill makes this re-spelling
# (rat_proofs.bend, `g1s`); it is restated here because a fill attached in a
# *_proofs.bend file is callable where it is declared and not from another file.
def N.nat.mag.sym(+p: Nat, +q: Nat)
  -> {R.Rat.mag(q, p) == R.Rat.mag(p, q) : Nat}:
  N.add_comm(Nat.sub(q, p), Nat.sub(p, q))

# nat.sub.min: (a-b) - min(a,b) = (a-b) -- the truncation of a truncation by
# the *other* truncation is the truncation. This is the identity the divisor of
# the negated coordinate needs one level up, and it is where the sign
# information finally has to be read: which of the two truncations is the
# surviving difference is exactly what Nat.cmp(a,b) decides, so this helper
# cases on it (three branches, all of them live -- nothing here is impossible).
#
#   GT: a - b is the difference, and b - a is 0, so the outer truncation is
#       sub(a-b, 0) = a-b. (sub_of_lt gives b-a = 0 at the flipped comparison,
#       sub_zero collapses the outer one, and the two are related by cmp_gt_sub_add
#       -- the lemma that says exactly "a-b is the difference of a and b".)
#   EQ: a = b and everything is 0.
#   LT: a - b = 0, so the identity is 0 - x = 0 (sub_zero_left).
#
# The comparison's evidence is the branch's own constant: a match on a *variable*
# (the parameter c) does not reduce, so the branch's {==} evidence stands for
# `c == LT{}` and the discriminations above are not needed.
def N.nat.sub.min(+a: Nat, +b: Nat, +c: Cmp, +e: {c == Nat.cmp(a, b) : Cmp})
  -> {Nat.sub(Nat.sub(a, b), Nat.sub(b, a)) == Nat.sub(a, b) : Nat}:
  match c:
    case GT{}:
      Equal.trans(Nat, Nat.sub(Nat.sub(a, b), Nat.sub(b, a)), Nat.sub(Nat.sub(a, b), 0n),
        Nat.sub(a, b),
        Equal.cong(Nat, Nat, u => Nat.sub(Nat.sub(a, b), u), Nat.sub(b, a), 0n,
          N.sub_of_lt(b, a, N.cmp_lt_of_gt(a, b, Equal.sym(Cmp, GT{}, Nat.cmp(a, b), e)))),
        N.sub_zero(Nat.sub(a, b)))
    case EQ{}:
      +z = N.cmp_eq(a, b, Equal.sym(Cmp, EQ{}, Nat.cmp(a, b), e))
      Equal.trans(Nat, Nat.sub(Nat.sub(a, b), Nat.sub(b, a)), Nat.sub(Nat.sub(b, b), Nat.sub(b, b)),
        Nat.sub(a, b),
        Equal.trans(Nat, Nat.sub(Nat.sub(a, b), Nat.sub(b, a)),
          Nat.sub(Nat.sub(b, b), Nat.sub(b, a)), Nat.sub(Nat.sub(b, b), Nat.sub(b, b)),
          Equal.cong(Nat, Nat, u => Nat.sub(u, Nat.sub(b, a)), Nat.sub(a, b), Nat.sub(b, b),
            Equal.cong(Nat, Nat, u => Nat.sub(u, b), a, b, z)),
          Equal.cong(Nat, Nat, u => Nat.sub(Nat.sub(b, b), u), Nat.sub(b, a), Nat.sub(b, b),
            Equal.cong(Nat, Nat, u => Nat.sub(b, u), a, b, z))),
        Equal.trans(Nat, Nat.sub(Nat.sub(b, b), Nat.sub(b, b)), 0n, Nat.sub(a, b),
          N.sub_self(Nat.sub(b, b)),
          Equal.sym(Nat, Nat.sub(a, b), 0n,
            Equal.trans(Nat, Nat.sub(a, b), Nat.sub(b, b), 0n,
              Equal.cong(Nat, Nat, u => Nat.sub(u, b), a, b, z),
              N.sub_self(b)))))
    case LT{}:
      Equal.trans(Nat, Nat.sub(Nat.sub(a, b), Nat.sub(b, a)), Nat.sub(0n, Nat.sub(b, a)),
        Nat.sub(a, b),
        Equal.cong(Nat, Nat, u => Nat.sub(u, Nat.sub(b, a)), Nat.sub(a, b), 0n,
          N.sub_of_lt(a, b, Equal.sym(Cmp, LT{}, Nat.cmp(a, b), e))),
        Equal.trans(Nat, Nat.sub(0n, Nat.sub(b, a)), 0n, Nat.sub(a, b),
          N.sub_zero_left(Nat.sub(b, a)),
          Equal.sym(Nat, Nat.sub(a, b), 0n,
            N.sub_of_lt(a, b, Equal.sym(Cmp, LT{}, Nat.cmp(a, b), e)))))

# nat.mag.sub: Rat.mag(sub(b,a), sub(a,b)) == Rat.mag(a, b) -- the divisor
# spelling mk computes for the pair Rat.num(b,a) against the spelling Rat.mag is
# stated over.
#
# The pair (sub(b,a), sub(a,b)) is the truncation pair of (a,b), so mk reads its
# magnitude as sub(sub(b,a),sub(a,b)) + sub(a,b): the *first* truncation is
# nested one level deeper than Rat.mag's own, and the bridge between them is
# nat.sub.min -- the fact that a truncation of a truncation by the other
# truncation changes nothing. With it the two summands are sub(b,a) and
# sub(a,b), i.e. Rat.mag(a,b) by definition, and the one remaining step is
# add_comm.
#
# Both named failures of the earlier round are avoided here. `sub_self` is not
# the tool (its conclusion sub(X,X) = 0 needs the two arguments to be the same
# *term*, while this collapse is a sign-dependent fact -- measured, the message
# is `expected : {Nat.sub(nn, np) == 0n} / observed : {Nat.sub(Nat.sub(nn, np),
# Nat.sub(nn, np)) == 0n}`); and neither is sub_cross plus add_cancel: at
# (X,Y) := (b-a, a-b) sub_cross relates add(sub(b-a,a-b), a-b) to
# add(sub(a-b,b-a), b-a), which is an equation about the two *padded*
# quantities rather than about the nested truncation, and add_cancel needs the
# padding as a shared leading summand, which `Nat.add` (it matches on its first
# argument) does not give it. The sign has to be read, and nat.sub.min reads it.
def N.nat.mag.sub(+a: Nat, +b: Nat)
  -> {Nat.add(Nat.sub(Nat.sub(b, a), Nat.sub(a, b)), Nat.sub(a, b))
      == R.Rat.mag(a, b) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.sub(Nat.sub(b, a), Nat.sub(a, b)), Nat.sub(a, b)),
    Nat.add(Nat.sub(b, a), Nat.sub(a, b)),
    R.Rat.mag(a, b),
    Equal.cong(Nat, Nat, u => Nat.add(u, Nat.sub(a, b)),
      Nat.sub(Nat.sub(b, a), Nat.sub(a, b)), Nat.sub(b, a),
      N.nat.sub.min(b, a, Nat.cmp(b, a), {==})),
    Equal.trans(Nat,
      Nat.add(Nat.sub(b, a), Nat.sub(a, b)),
      Nat.add(Nat.sub(a, b), Nat.sub(b, a)),
      R.Rat.mag(a, b),
      N.add_comm(Nat.sub(b, a), Nat.sub(a, b)),
      {==}))

# --- the coprime hypothesis mk.fixed wants on the negated coordinate ---

# Rat.mk.fixed at the *negated* coordinate: mk(Rat.num(b,a), d) is the
# constructor Rat{Rat.num(b,a), d} -- the coprime hypothesis stated at
# Rat.mag(a,b) re-spelled to the divisor mk computes. The comparison
# Nat.cmp(b, a) is the one mk.fixed threads into its own e; nothing is cased on
# here, and the only step is the `cong` that carries the re-spelling through the
# gcd.
def rat.mk.fixed.neg(+a: Nat, +b: Nat, +dp: Nat,
                     +g: {N.Nat.gcd(R.Rat.mag(a, b), 1n+dp) == 1n : Nat})
  -> {R.Rat.mk(R.Rat.num(b, a), 1n+dp) == R.Rat{R.Rat.num(b, a), 1n+dp} : R.Rat}:
  +gn = Equal.trans(Nat,
    N.Nat.gcd(R.Rat.mag(b, a), 1n+dp),
    N.Nat.gcd(R.Rat.mag(a, b), 1n+dp),
    1n,
    Equal.cong(Nat, Nat, u => N.Nat.gcd(u, 1n+dp), R.Rat.mag(b, a), R.Rat.mag(a, b),
      N.nat.mag.sym(a, b)),
    g)
  R.Rat.mk.fixed(Nat.cmp(b, a), b, a, dp, {==}, gn)

# Rat.neg_neg at the pair (np, nn): the coordinate-wise law QExt.neg_neg is made
# of, at the same spelling Rat.neg_neg is stated in -- Rat{Rat.num(np,nn), 1+dp}
# with the negation's own coprime hypothesis derived from the one in hand. Every
# write here is a qrat_rat.bend name, which is the copy a fill in this file can
# call (a fill attached in rat_proofs.bend is callable where it is declared and
# not from here).
#
# Two mk.fixed applications around one congruence: the first turns the inner
# mk into the constructor (its coprime hypothesis is rat.mk.fixed.neg's bridge),
# and the second turns the outer one into the goal's own value. `{==}` carries
# the step that is not a rewrite but a reduction: Rat.neg of a constructor is
# mk(Int.neg(Rat.num(np,nn)), 1+dp) and Int.neg of the difference pair
# I.Int{sub(np,nn), sub(nn,np)} reduces to I.Int{sub(nn,np), sub(np,nn)}, which
# *is* Rat.num(nn,np) -- no motive over that pair is needed, the two terms are
# the same term.
def rat.neg.neg(+np: Nat, +nn: Nat, +dp: Nat,
                +g: {N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp) == 1n : Nat})
  -> {R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(np, nn), 1n+dp})) == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}:
  Equal.trans(R.Rat,
    R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(np, nn), 1n+dp})),
    R.Rat.neg(R.Rat{R.Rat.num(nn, np), 1n+dp}),
    R.Rat{R.Rat.num(np, nn), 1n+dp},
    Equal.cong(R.Rat, R.Rat, u => R.Rat.neg(u),
      R.Rat.mk(I.Int.neg(R.Rat.num(np, nn)), 1n+dp),
      R.Rat{R.Rat.num(nn, np), 1n+dp},
      rat.mk.fixed.neg(np, nn, dp, g)),
    Equal.trans(R.Rat,
      R.Rat.neg(R.Rat{R.Rat.num(nn, np), 1n+dp}),
      R.Rat.mk(R.Rat.num(np, nn), 1n+dp),
      R.Rat{R.Rat.num(np, nn), 1n+dp},
      {==},
      R.Rat.mk.fixed(Nat.cmp(np, nn), np, nn, dp, {==}, g)))

def R.Rat.neg_neg(c, np, nn, dp, e, g1):
  rat.neg.neg(np, nn, dp, g1)

# QExt.neg_neg: negation is componentwise and does not touch a denominator, so
# this is Rat.neg_neg once per coordinate -- one qext.re step and one qext.im
# step, plus the two coordinate witnesses' own Rat-level machinery above (the
# helper rat.neg.neg, which is where the coprime hypothesis of the *negated*
# coordinate is manufactured). Nothing here cases on anything.
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
      rat.neg.neg(np, nn, dp, g)),
    qext.im(R.Rat{R.Rat.num(np, nn), 1n+dp},
      R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(mq, mn), 1n+dq})),
      R.Rat{R.Rat.num(mq, mn), 1n+dq},
      rat.neg.neg(mq, mn, dq, h)))
