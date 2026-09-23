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
# One checker limitation was recorded here by an earlier round and is now
# *stale*, measured again this round: lambda congs were said to be unusable
# except as a whole coordinate rewrite (qext.re/qext.im below). They are usable
# -- as a def body, as an argument of Equal.trans, and nested under another cong
# -- in a third file that imports rat.bend and rat_proofs.bend, which is what
# QExt.mul_assoc.re/.im below are built out of. The earlier measurements were
# symptoms of the alias-prefixed helper names this file's header describes, not
# of the lambda: with those renamed bare, all three placements check.

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

# qext.nat.mul_zero: QExt.nat(d) * 0 = 0 -- the one product in QExt.mul's real
# coordinate that Rat.mul_zero cannot reach.
#
# Rat.mul_zero is stated at the spelling Rat{n, 1n+dp}, because that is what
# makes mk's denominator a successor and lets Rat.mk.zero close the fill. The
# radicand coefficient is QExt.nat(d) = Rat{Rat.num(d,0), 1}, a denominator of
# base 1, so no dp instantiates it. The chain is Rat.mul_zero's own with the
# last step free: the numerator becomes a literal zero and the denominator
# Nat.mul(1n,1n) reduces, so mk(0,1) is already 0/1 by computation -- measured,
# it is the `{==}` below and needs no Rat.mk.zero.
def qext.nat.mul_zero(+d: Nat)
  -> {R.Rat.mul(Q.QExt.nat(d), R.Rat.zero()) == R.Rat.zero() : R.Rat}:
  %Equal.sym(I.Int, I.Int.mul(R.Rat.num(d, 0n), I.Int.zero()), I.Int.zero(),
      I.Int.mul_zero(R.Rat.num(d, 0n)))
    : {R.Rat.mk(_, Nat.mul(1n, 1n)) == R.Rat.zero() : R.Rat}
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

# --- QExt.mul_assoc ---

# QExt.mul_assoc.re: the real coordinate of the associativity law, as its own
# Rat-level chain. Both sides are expanded to the same flat sum of four products
# by the rung-2 laws, and the two groupings are reconciled with
# Rat.add_assoc.arb and Rat.add_comm.
#
# With A,B = x's coefficients, C,E = y's, F,G = z's and D = QExt.nat(d):
#
#   (A*C + D*(B*E))*F + D*((A*E + B*C)*G)
#     -> (A*C)*F + (D*(B*E))*F + ...         Rat.mul_add_left.arb
#     -> A*(C*F) + D*(B*(E*F)) + ...         Rat.mul_assoc.arb, three times
#     -> A*(C*F) + D*(B*(E*F))
#          + (D*(A*(E*G)) + D*(B*(C*G)))     the same laws inside D*(...)
#   A*(C*F + D*(E*G)) + D*(B*(C*G + E*F))
#     -> A*(C*F) + A*(D*(E*G)) + ...         Rat.mul_distrib.arb
#     -> A*(C*F) + D*(A*(E*G)) + ...         associativity and commutativity
#                                            around the D factor
#     -> A*(C*F) + D*(A*(E*G))
#          + (D*(B*(C*G)) + D*(B*(E*F)))     Rat.mul_distrib.arb twice
#
# Every law's positivity slot is a Rat.mul.den.pos or Rat.add.den.pos at the
# compound term it names; D's own is `{==}`, since QExt.nat(d) is
# Rat{Rat.num(d,0), 1} and its denominator is 1 by computation.
def QExt.mul_assoc.re(+d: Nat, +xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat,
                      +za: R.Rat, +zb: R.Rat,
                      +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                      +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                      +gy: {Nat.cmp(0n, R.Rat.denof(ya)) == LT{} : Cmp},
                      +hy: {Nat.cmp(0n, R.Rat.denof(yb)) == LT{} : Cmp},
                      +gz: {Nat.cmp(0n, R.Rat.denof(za)) == LT{} : Cmp},
                      +hz: {Nat.cmp(0n, R.Rat.denof(zb)) == LT{} : Cmp})
  -> {R.Rat.add(
        R.Rat.mul(R.Rat.add(R.Rat.mul(xa, ya),
                            R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))), za),
        R.Rat.mul(Q.QExt.nat(d),
          R.Rat.mul(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)), zb)))
      == R.Rat.add(
        R.Rat.mul(xa, R.Rat.add(R.Rat.mul(ya, za),
                                R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, zb)))),
        R.Rat.mul(Q.QExt.nat(d),
          R.Rat.mul(xb, R.Rat.add(R.Rat.mul(ya, zb), R.Rat.mul(yb, za))))) : R.Rat}:
  +A = xa
  +B = xb
  +C = ya
  +E = yb
  +F = za
  +G = zb
  +D = Q.QExt.nat(d)
  +AC = R.Rat.mul(A, C)
  +BE = R.Rat.mul(B, E)
  +DBE = R.Rat.mul(D, BE)
  +AE = R.Rat.mul(A, E)
  +BC = R.Rat.mul(B, C)
  +CF = R.Rat.mul(C, F)
  +EG = R.Rat.mul(E, G)
  +DEG = R.Rat.mul(D, EG)
  +CG = R.Rat.mul(C, G)
  +EF = R.Rat.mul(E, F)
  +BEF = R.Rat.mul(B, EF)
  +AEG = R.Rat.mul(A, EG)
  +BCG = R.Rat.mul(B, CG)
  +X = R.Rat.mul(A, CF)
  +Y = R.Rat.mul(D, BEF)
  +Z = R.Rat.mul(D, AEG)
  +W = R.Rat.mul(D, BCG)
  +pAC = R.Rat.mul.den.pos(A, C, gx, gy)
  +pBE = R.Rat.mul.den.pos(B, E, hx, hy)
  +pDBE = R.Rat.mul.den.pos(D, BE, {==}, pBE)
  +pAE = R.Rat.mul.den.pos(A, E, gx, hy)
  +pBC = R.Rat.mul.den.pos(B, C, hx, gy)
  +pCF = R.Rat.mul.den.pos(C, F, gy, gz)
  +pEG = R.Rat.mul.den.pos(E, G, hy, hz)
  +pDEG = R.Rat.mul.den.pos(D, EG, {==}, pEG)
  +pCG = R.Rat.mul.den.pos(C, G, gy, hz)
  +pEF = R.Rat.mul.den.pos(E, F, hy, gz)
  +pAEG = R.Rat.mul.den.pos(A, EG, gx, pEG)
  +pBCG = R.Rat.mul.den.pos(B, CG, hx, pCG)
  +pBEF = R.Rat.mul.den.pos(B, EF, hx, pEF)
  +pX = R.Rat.mul.den.pos(A, CF, gx, pCF)
  +pY = R.Rat.mul.den.pos(D, BEF, {==}, pBEF)
  +pZ = R.Rat.mul.den.pos(D, AEG, {==}, pAEG)
  +pW = R.Rat.mul.den.pos(D, BCG, {==}, pBCG)
  +pWY = R.Rat.add.den.pos(W, Y, pW, pY)
  +pZW = R.Rat.add.den.pos(Z, W, pZ, pW)
  +S0 = R.Rat.add(R.Rat.mul(R.Rat.add(AC, DBE), F),
                  R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G)))
  +S1 = R.Rat.add(R.Rat.add(R.Rat.mul(AC, F), R.Rat.mul(DBE, F)),
                  R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G)))
  +S2 = R.Rat.add(R.Rat.add(X, R.Rat.mul(DBE, F)),
                  R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G)))
  +S3 = R.Rat.add(R.Rat.add(X, R.Rat.mul(D, R.Rat.mul(BE, F))),
                  R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G)))
  +S4 = R.Rat.add(R.Rat.add(X, Y), R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G)))
  +S5 = R.Rat.add(R.Rat.add(X, Y), R.Rat.mul(D, R.Rat.add(R.Rat.mul(AE, G), R.Rat.mul(BC, G))))
  +S6 = R.Rat.add(R.Rat.add(X, Y), R.Rat.mul(D, R.Rat.add(AEG, BCG)))
  +S7 = R.Rat.add(R.Rat.add(X, Y), R.Rat.add(Z, W))
  +l1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G))),
    R.Rat.mul(R.Rat.add(AC, DBE), F),
    R.Rat.add(R.Rat.mul(AC, F), R.Rat.mul(DBE, F)),
    R.Rat.mul_add_left.arb(AC, DBE, F, pAC, pDBE, gz))
  +l2 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(u, R.Rat.mul(DBE, F)),
                   R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G))),
    R.Rat.mul(AC, F), X,
    R.Rat.mul_assoc.arb(A, C, F, gx, gy, gz))
  +l3 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, u),
                   R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G))),
    R.Rat.mul(DBE, F), R.Rat.mul(D, R.Rat.mul(BE, F)),
    R.Rat.mul_assoc.arb(D, BE, F, {==}, pBE, gz))
  +l4 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, R.Rat.mul(D, u)),
                   R.Rat.mul(D, R.Rat.mul(R.Rat.add(AE, BC), G))),
    R.Rat.mul(BE, F), BEF,
    R.Rat.mul_assoc.arb(B, E, F, hx, hy, gz))
  +l5 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Y), R.Rat.mul(D, u)),
    R.Rat.mul(R.Rat.add(AE, BC), G),
    R.Rat.add(R.Rat.mul(AE, G), R.Rat.mul(BC, G)),
    R.Rat.mul_add_left.arb(AE, BC, G, pAE, pBC, hz))
  +l6 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Y), R.Rat.mul(D, u)),
    R.Rat.add(R.Rat.mul(AE, G), R.Rat.mul(BC, G)),
    R.Rat.add(AEG, BCG),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(AE, G), R.Rat.mul(BC, G)),
      R.Rat.add(AEG, R.Rat.mul(BC, G)),
      R.Rat.add(AEG, BCG),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat.mul(BC, G)),
        R.Rat.mul(AE, G), AEG,
        R.Rat.mul_assoc.arb(A, E, G, gx, hy, hz)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AEG, u),
        R.Rat.mul(BC, G), BCG,
        R.Rat.mul_assoc.arb(B, C, G, hx, gy, hz))))
  +l7 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Y), u),
    R.Rat.mul(D, R.Rat.add(AEG, BCG)),
    R.Rat.add(Z, W),
    R.Rat.mul_distrib.arb(D, AEG, BCG, {==}, pAEG, pBCG))
  +t1 = Equal.trans(R.Rat, S0, S1, S2, l1, l2)
  +t2 = Equal.trans(R.Rat, S0, S2, S3, t1, l3)
  +t3 = Equal.trans(R.Rat, S0, S3, S4, t2, l4)
  +t4 = Equal.trans(R.Rat, S0, S4, S5, t3, l5)
  +t5 = Equal.trans(R.Rat, S0, S5, S6, t4, l6)
  +eL = Equal.trans(R.Rat, S0, S6, S7, t5, l7)
  +R0 = R.Rat.add(R.Rat.mul(A, R.Rat.add(CF, DEG)),
                  R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(CG, EF))))
  +R1 = R.Rat.add(R.Rat.add(X, R.Rat.mul(A, DEG)),
                  R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(CG, EF))))
  +R2 = R.Rat.add(R.Rat.add(X, Z),
                  R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(CG, EF))))
  +R3 = R.Rat.add(R.Rat.add(X, Z),
                  R.Rat.mul(D, R.Rat.add(R.Rat.mul(B, CG), R.Rat.mul(B, EF))))
  +R4 = R.Rat.add(R.Rat.add(X, Z), R.Rat.add(W, Y))
  +r1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(CG, EF)))),
    R.Rat.mul(A, R.Rat.add(CF, DEG)),
    R.Rat.add(X, R.Rat.mul(A, DEG)),
    R.Rat.mul_distrib.arb(A, CF, DEG, gx, pCF, pDEG))
  +r2 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, u),
                   R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(CG, EF)))),
    R.Rat.mul(A, DEG), Z,
    Equal.trans(R.Rat,
      R.Rat.mul(A, DEG),
      R.Rat.mul(R.Rat.mul(A, D), EG),
      Z,
      Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(A, D), EG), R.Rat.mul(A, DEG),
        R.Rat.mul_assoc.arb(A, D, EG, gx, {==}, pEG)),
      Equal.trans(R.Rat,
        R.Rat.mul(R.Rat.mul(A, D), EG),
        R.Rat.mul(R.Rat.mul(D, A), EG),
        Z,
        Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(u, EG),
          R.Rat.mul(A, D), R.Rat.mul(D, A), R.Rat.mul_comm(A, D)),
        R.Rat.mul_assoc.arb(D, A, EG, {==}, gx, pEG))))
  +r3 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Z), R.Rat.mul(D, u)),
    R.Rat.mul(B, R.Rat.add(CG, EF)),
    R.Rat.add(R.Rat.mul(B, CG), R.Rat.mul(B, EF)),
    R.Rat.mul_distrib.arb(B, CG, EF, hx, pCG, pEF))
  +r4 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Z), u),
    R.Rat.mul(D, R.Rat.add(R.Rat.mul(B, CG), R.Rat.mul(B, EF))),
    R.Rat.add(W, Y),
    R.Rat.mul_distrib.arb(D, R.Rat.mul(B, CG), R.Rat.mul(B, EF), {==}, pBCG, pBEF))
  +r5 = Equal.trans(R.Rat,
    R4,
    R.Rat.add(X, R.Rat.add(R.Rat.add(Z, W), Y)),
    S7,
    Equal.trans(R.Rat,
      R4,
      R.Rat.add(X, R.Rat.add(Z, R.Rat.add(W, Y))),
      R.Rat.add(X, R.Rat.add(R.Rat.add(Z, W), Y)),
      R.Rat.add_assoc.arb(X, Z, R.Rat.add(W, Y), pX, pZ, pWY),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(X, u),
        R.Rat.add(Z, R.Rat.add(W, Y)), R.Rat.add(R.Rat.add(Z, W), Y),
        Equal.sym(R.Rat, R.Rat.add(R.Rat.add(Z, W), Y), R.Rat.add(Z, R.Rat.add(W, Y)),
          R.Rat.add_assoc.arb(Z, W, Y, pZ, pW, pY)))),
    Equal.trans(R.Rat,
      R.Rat.add(X, R.Rat.add(R.Rat.add(Z, W), Y)),
      R.Rat.add(X, R.Rat.add(Y, R.Rat.add(Z, W))),
      S7,
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(X, u),
        R.Rat.add(R.Rat.add(Z, W), Y), R.Rat.add(Y, R.Rat.add(Z, W)),
        R.Rat.add_comm(R.Rat.add(Z, W), Y)),
      Equal.sym(R.Rat, S7, R.Rat.add(X, R.Rat.add(Y, R.Rat.add(Z, W))),
        R.Rat.add_assoc.arb(X, Y, R.Rat.add(Z, W), pX, pY, pZW))))
  +s1 = Equal.trans(R.Rat, R0, R1, R2, r1, r2)
  +s2 = Equal.trans(R.Rat, R0, R2, R3, s1, r3)
  +s3 = Equal.trans(R.Rat, R0, R3, R4, s2, r4)
  +eR = Equal.trans(R.Rat, R0, R4, S7, s3, r5)
  Equal.trans(R.Rat, S0, S7, R0, eL, Equal.sym(R.Rat, R0, S7, eR))

# QExt.mul_assoc.im: the imaginary coordinate, the same shape as the real one --
# both sides expand to the flat sum (A*(C*G) + D*(B*(E*G))) + (A*(E*F) + B*(C*F))
# and the two groupings are reconciled the same way. The only new step is the D
# factor moving across B in the right-hand side's second summand (associativity,
# commutativity, associativity), exactly as it moves across A in the real one.
def QExt.mul_assoc.im(+d: Nat, +xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat,
                      +za: R.Rat, +zb: R.Rat,
                      +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                      +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                      +gy: {Nat.cmp(0n, R.Rat.denof(ya)) == LT{} : Cmp},
                      +hy: {Nat.cmp(0n, R.Rat.denof(yb)) == LT{} : Cmp},
                      +gz: {Nat.cmp(0n, R.Rat.denof(za)) == LT{} : Cmp},
                      +hz: {Nat.cmp(0n, R.Rat.denof(zb)) == LT{} : Cmp})
  -> {R.Rat.add(
        R.Rat.mul(R.Rat.add(R.Rat.mul(xa, ya),
                            R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))), zb),
        R.Rat.mul(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)), za))
      == R.Rat.add(
        R.Rat.mul(xa, R.Rat.add(R.Rat.mul(ya, zb), R.Rat.mul(yb, za))),
        R.Rat.mul(xb, R.Rat.add(R.Rat.mul(ya, za),
                                R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(yb, zb))))) : R.Rat}:
  +A = xa
  +B = xb
  +C = ya
  +E = yb
  +F = za
  +G = zb
  +D = Q.QExt.nat(d)
  +AC = R.Rat.mul(A, C)
  +BE = R.Rat.mul(B, E)
  +DBE = R.Rat.mul(D, BE)
  +AE = R.Rat.mul(A, E)
  +BC = R.Rat.mul(B, C)
  +CF = R.Rat.mul(C, F)
  +EG = R.Rat.mul(E, G)
  +DEG = R.Rat.mul(D, EG)
  +CG = R.Rat.mul(C, G)
  +EF = R.Rat.mul(E, F)
  +X = R.Rat.mul(A, CG)
  +Y = R.Rat.mul(D, R.Rat.mul(B, EG))
  +Z = R.Rat.mul(A, EF)
  +W = R.Rat.mul(B, CF)
  +pAC = R.Rat.mul.den.pos(A, C, gx, gy)
  +pBE = R.Rat.mul.den.pos(B, E, hx, hy)
  +pDBE = R.Rat.mul.den.pos(D, BE, {==}, pBE)
  +pAE = R.Rat.mul.den.pos(A, E, gx, hy)
  +pBC = R.Rat.mul.den.pos(B, C, hx, gy)
  +pCF = R.Rat.mul.den.pos(C, F, gy, gz)
  +pEG = R.Rat.mul.den.pos(E, G, hy, hz)
  +pDEG = R.Rat.mul.den.pos(D, EG, {==}, pEG)
  +pCG = R.Rat.mul.den.pos(C, G, gy, hz)
  +pEF = R.Rat.mul.den.pos(E, F, hy, gz)
  +pBEG = R.Rat.mul.den.pos(B, EG, hx, pEG)
  +pX = R.Rat.mul.den.pos(A, CG, gx, pCG)
  +pY = R.Rat.mul.den.pos(D, R.Rat.mul(B, EG), {==}, pBEG)
  +pZ = R.Rat.mul.den.pos(A, EF, gx, pEF)
  +pW = R.Rat.mul.den.pos(B, CF, hx, pCF)
  +pWY = R.Rat.add.den.pos(W, Y, pW, pY)
  +pZW = R.Rat.add.den.pos(Z, W, pZ, pW)
  +S0 = R.Rat.add(R.Rat.mul(R.Rat.add(AC, DBE), G), R.Rat.mul(R.Rat.add(AE, BC), F))
  +S1 = R.Rat.add(R.Rat.add(R.Rat.mul(AC, G), R.Rat.mul(DBE, G)),
                  R.Rat.mul(R.Rat.add(AE, BC), F))
  +S1b = R.Rat.add(R.Rat.add(R.Rat.mul(AC, G), R.Rat.mul(DBE, G)),
                   R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F)))
  +S2 = R.Rat.add(R.Rat.add(X, R.Rat.mul(DBE, G)),
                  R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F)))
  +S3 = R.Rat.add(R.Rat.add(X, R.Rat.mul(D, R.Rat.mul(BE, G))),
                  R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F)))
  +S4 = R.Rat.add(R.Rat.add(X, Y),
                  R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F)))
  +S5 = R.Rat.add(R.Rat.add(X, Y), R.Rat.add(Z, R.Rat.mul(BC, F)))
  +S6 = R.Rat.add(R.Rat.add(X, Y), R.Rat.add(Z, W))
  +l1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(R.Rat.add(AE, BC), F)),
    R.Rat.mul(R.Rat.add(AC, DBE), G),
    R.Rat.add(R.Rat.mul(AC, G), R.Rat.mul(DBE, G)),
    R.Rat.mul_add_left.arb(AC, DBE, G, pAC, pDBE, hz))
  +l1b = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(R.Rat.mul(AC, G), R.Rat.mul(DBE, G)), u),
    R.Rat.mul(R.Rat.add(AE, BC), F),
    R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F)),
    R.Rat.mul_add_left.arb(AE, BC, F, pAE, pBC, gz))
  +l2 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(u, R.Rat.mul(DBE, G)),
                   R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F))),
    R.Rat.mul(AC, G), X,
    R.Rat.mul_assoc.arb(A, C, G, gx, gy, hz))
  +l3 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, u),
                   R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F))),
    R.Rat.mul(DBE, G), R.Rat.mul(D, R.Rat.mul(BE, G)),
    R.Rat.mul_assoc.arb(D, BE, G, {==}, pBE, hz))
  +l4 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, R.Rat.mul(D, u)),
                   R.Rat.add(R.Rat.mul(AE, F), R.Rat.mul(BC, F))),
    R.Rat.mul(BE, G), R.Rat.mul(B, EG),
    R.Rat.mul_assoc.arb(B, E, G, hx, hy, hz))
  +l5 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Y), R.Rat.add(u, R.Rat.mul(BC, F))),
    R.Rat.mul(AE, F), Z,
    R.Rat.mul_assoc.arb(A, E, F, gx, hy, gz))
  +l6 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Y), R.Rat.add(Z, u)),
    R.Rat.mul(BC, F), W,
    R.Rat.mul_assoc.arb(B, C, F, hx, gy, gz))
  +t0 = Equal.trans(R.Rat, S0, S1, S1b, l1, l1b)
  +t1 = Equal.trans(R.Rat, S0, S1b, S2, t0, l2)
  +t2 = Equal.trans(R.Rat, S0, S2, S3, t1, l3)
  +t3 = Equal.trans(R.Rat, S0, S3, S4, t2, l4)
  +t4 = Equal.trans(R.Rat, S0, S4, S5, t3, l5)
  +eL = Equal.trans(R.Rat, S0, S5, S6, t4, l6)
  +R0 = R.Rat.add(R.Rat.mul(A, R.Rat.add(CG, EF)),
                  R.Rat.mul(B, R.Rat.add(CF, DEG)))
  +R1 = R.Rat.add(R.Rat.add(X, Z),
                  R.Rat.mul(B, R.Rat.add(CF, DEG)))
  +R2 = R.Rat.add(R.Rat.add(X, Z),
                  R.Rat.add(R.Rat.mul(B, CF), R.Rat.mul(B, DEG)))
  +R3 = R.Rat.add(R.Rat.add(X, Z), R.Rat.add(W, Y))
  +r1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(B, R.Rat.add(CF, DEG))),
    R.Rat.mul(A, R.Rat.add(CG, EF)),
    R.Rat.add(X, Z),
    R.Rat.mul_distrib.arb(A, CG, EF, gx, pCG, pEF))
  +r2 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Z), u),
    R.Rat.mul(B, R.Rat.add(CF, DEG)),
    R.Rat.add(R.Rat.mul(B, CF), R.Rat.mul(B, DEG)),
    R.Rat.mul_distrib.arb(B, CF, DEG, hx, pCF, pDEG))
  +r3 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(X, Z), R.Rat.add(W, u)),
    R.Rat.mul(B, DEG), Y,
    Equal.trans(R.Rat,
      R.Rat.mul(B, DEG),
      R.Rat.mul(R.Rat.mul(B, D), EG),
      Y,
      Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(B, D), EG), R.Rat.mul(B, DEG),
        R.Rat.mul_assoc.arb(B, D, EG, hx, {==}, pEG)),
      Equal.trans(R.Rat,
        R.Rat.mul(R.Rat.mul(B, D), EG),
        R.Rat.mul(R.Rat.mul(D, B), EG),
        Y,
        Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(u, EG),
          R.Rat.mul(B, D), R.Rat.mul(D, B), R.Rat.mul_comm(B, D)),
        R.Rat.mul_assoc.arb(D, B, EG, {==}, hx, pEG))))
  +r4 = Equal.trans(R.Rat,
    R3,
    R.Rat.add(X, R.Rat.add(R.Rat.add(Z, W), Y)),
    S6,
    Equal.trans(R.Rat,
      R3,
      R.Rat.add(X, R.Rat.add(Z, R.Rat.add(W, Y))),
      R.Rat.add(X, R.Rat.add(R.Rat.add(Z, W), Y)),
      R.Rat.add_assoc.arb(X, Z, R.Rat.add(W, Y), pX, pZ, pWY),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(X, u),
        R.Rat.add(Z, R.Rat.add(W, Y)), R.Rat.add(R.Rat.add(Z, W), Y),
        Equal.sym(R.Rat, R.Rat.add(R.Rat.add(Z, W), Y), R.Rat.add(Z, R.Rat.add(W, Y)),
          R.Rat.add_assoc.arb(Z, W, Y, pZ, pW, pY)))),
    Equal.trans(R.Rat,
      R.Rat.add(X, R.Rat.add(R.Rat.add(Z, W), Y)),
      R.Rat.add(X, R.Rat.add(Y, R.Rat.add(Z, W))),
      S6,
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(X, u),
        R.Rat.add(R.Rat.add(Z, W), Y), R.Rat.add(Y, R.Rat.add(Z, W)),
        R.Rat.add_comm(R.Rat.add(Z, W), Y)),
      Equal.sym(R.Rat, S6, R.Rat.add(X, R.Rat.add(Y, R.Rat.add(Z, W))),
        R.Rat.add_assoc.arb(X, Y, R.Rat.add(Z, W), pX, pY, pZW))))
  +s1 = Equal.trans(R.Rat, R0, R1, R2, r1, r2)
  +s2 = Equal.trans(R.Rat, R0, R2, R3, s1, r3)
  +eR = Equal.trans(R.Rat, R0, R3, S6, s2, r4)
  Equal.trans(R.Rat, S0, S6, R0, eL, Equal.sym(R.Rat, R0, S6, eR))
# QExt.mul_assoc: two coordinate steps and nothing else -- the Rat-level work is
# the two chains above, each of which is the law's whole coordinate equation.
# The matches put the hypotheses at the coefficient spelling the chains want, as
# in QExt.add_assoc: QExt.re(x) and xa are the same term once x is a constructor.
def Q.QExt.mul_assoc(d, x, y, z, gx, hx, gy, hy, gz, hz):
  match x y z:
    case Q.QExt{xa, xb} Q.QExt{ya, yb} Q.QExt{za, zb}:
      +D = Q.QExt.nat(d)
      +P = R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(D, R.Rat.mul(xb, yb)))
      +Q = R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))
      +S = R.Rat.add(R.Rat.mul(ya, za), R.Rat.mul(D, R.Rat.mul(yb, zb)))
      +T = R.Rat.add(R.Rat.mul(ya, zb), R.Rat.mul(yb, za))
      +Lr = R.Rat.add(R.Rat.mul(P, za), R.Rat.mul(D, R.Rat.mul(Q, zb)))
      +Li = R.Rat.add(R.Rat.mul(P, zb), R.Rat.mul(Q, za))
      +Rr = R.Rat.add(R.Rat.mul(xa, S), R.Rat.mul(D, R.Rat.mul(xb, T)))
      +Ri = R.Rat.add(R.Rat.mul(xa, T), R.Rat.mul(xb, S))
      Equal.trans(Q.QExt,
        Q.QExt{Lr, Li},
        Q.QExt{Rr, Li},
        Q.QExt{Rr, Ri},
        qext.re(Li, Lr, Rr,
          QExt.mul_assoc.re(d, xa, xb, ya, yb, za, zb, gx, hx, gy, hy, gz, hz)),
        qext.im(Rr, Li, Ri,
          QExt.mul_assoc.im(d, xa, xb, ya, yb, za, zb, gx, hx, gy, hy, gz, hz)))

# --- QExt.mul_distrib ---

# QExt.mul_distrib.re: with A,B = x's coefficients, C,E = y's, F,G = z's and
# D = QExt.nat(d), both sides are
#
#   (A*C + A*F) + (D*(B*E) + D*(B*G))
#
# up to the order of the four summands: three Rat.mul_distrib.arb calls expand
# the two products of sums, and one five-step rearrangement (Rat.add_assoc.arb
# and Rat.add_comm, exactly the shape the rung-2 distributive fill uses) puts the
# two groupings in step.
def QExt.mul_distrib.re(+d: Nat, +xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat,
                        +za: R.Rat, +zb: R.Rat,
                        +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                        +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                        +gy: {Nat.cmp(0n, R.Rat.denof(ya)) == LT{} : Cmp},
                        +hy: {Nat.cmp(0n, R.Rat.denof(yb)) == LT{} : Cmp},
                        +gz: {Nat.cmp(0n, R.Rat.denof(za)) == LT{} : Cmp},
                        +hz: {Nat.cmp(0n, R.Rat.denof(zb)) == LT{} : Cmp})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.add(ya, za)),
                R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, R.Rat.add(yb, zb))))
      == R.Rat.add(R.Rat.add(R.Rat.mul(xa, ya),
                             R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))),
                   R.Rat.add(R.Rat.mul(xa, za),
                             R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, zb)))) : R.Rat}:
  +A = xa
  +B = xb
  +C = ya
  +E = yb
  +F = za
  +G = zb
  +D = Q.QExt.nat(d)
  +AC = R.Rat.mul(A, C)
  +AF = R.Rat.mul(A, F)
  +BE = R.Rat.mul(B, E)
  +BG = R.Rat.mul(B, G)
  +Y = R.Rat.mul(D, BE)
  +W = R.Rat.mul(D, BG)
  +pAC = R.Rat.mul.den.pos(A, C, gx, gy)
  +pAF = R.Rat.mul.den.pos(A, F, gx, gz)
  +pBE = R.Rat.mul.den.pos(B, E, hx, hy)
  +pBG = R.Rat.mul.den.pos(B, G, hx, hz)
  +pY = R.Rat.mul.den.pos(D, BE, {==}, pBE)
  +pW = R.Rat.mul.den.pos(D, BG, {==}, pBG)
  +pYW = R.Rat.add.den.pos(Y, W, pY, pW)
  +pZY = R.Rat.add.den.pos(AF, Y, pAF, pY)
  +pYZ = R.Rat.add.den.pos(Y, AF, pY, pAF)
  +pZW = R.Rat.add.den.pos(AF, W, pAF, pW)
  +S1 = R.Rat.add(R.Rat.add(AC, AF), R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(E, G))))
  +S2 = R.Rat.add(R.Rat.add(AC, AF), R.Rat.add(Y, W))
  +l1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(E, G)))),
    R.Rat.mul(A, R.Rat.add(C, F)),
    R.Rat.add(AC, AF),
    R.Rat.mul_distrib.arb(A, C, F, gx, gy, gz))
  +l2 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(AC, AF), u),
    R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(E, G))),
    R.Rat.add(Y, W),
    Equal.trans(R.Rat,
      R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(E, G))),
      R.Rat.mul(D, R.Rat.add(BE, BG)),
      R.Rat.add(Y, W),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(D, u),
        R.Rat.mul(B, R.Rat.add(E, G)), R.Rat.add(BE, BG),
        R.Rat.mul_distrib.arb(B, E, G, hx, hy, hz)),
      R.Rat.mul_distrib.arb(D, BE, BG, {==}, pBE, pBG)))
  +l3 = Equal.trans(R.Rat,
    S2,
    R.Rat.add(AC, R.Rat.add(AF, R.Rat.add(Y, W))),
    R.Rat.add(R.Rat.add(AC, Y), R.Rat.add(AF, W)),
    R.Rat.add_assoc.arb(AC, AF, R.Rat.add(Y, W), pAC, pAF, pYW),
    Equal.trans(R.Rat,
      R.Rat.add(AC, R.Rat.add(AF, R.Rat.add(Y, W))),
      R.Rat.add(AC, R.Rat.add(R.Rat.add(AF, Y), W)),
      R.Rat.add(R.Rat.add(AC, Y), R.Rat.add(AF, W)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AC, u),
        R.Rat.add(AF, R.Rat.add(Y, W)), R.Rat.add(R.Rat.add(AF, Y), W),
        Equal.sym(R.Rat, R.Rat.add(R.Rat.add(AF, Y), W), R.Rat.add(AF, R.Rat.add(Y, W)),
          R.Rat.add_assoc.arb(AF, Y, W, pAF, pY, pW))),
      Equal.trans(R.Rat,
        R.Rat.add(AC, R.Rat.add(R.Rat.add(AF, Y), W)),
        R.Rat.add(AC, R.Rat.add(R.Rat.add(Y, AF), W)),
        R.Rat.add(R.Rat.add(AC, Y), R.Rat.add(AF, W)),
        Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AC, u),
          R.Rat.add(R.Rat.add(AF, Y), W), R.Rat.add(R.Rat.add(Y, AF), W),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, W),
            R.Rat.add(AF, Y), R.Rat.add(Y, AF), R.Rat.add_comm(AF, Y))),
        Equal.trans(R.Rat,
          R.Rat.add(AC, R.Rat.add(R.Rat.add(Y, AF), W)),
          R.Rat.add(AC, R.Rat.add(Y, R.Rat.add(AF, W))),
          R.Rat.add(R.Rat.add(AC, Y), R.Rat.add(AF, W)),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AC, u),
            R.Rat.add(R.Rat.add(Y, AF), W), R.Rat.add(Y, R.Rat.add(AF, W)),
            R.Rat.add_assoc.arb(Y, AF, W, pY, pAF, pW)),
          Equal.sym(R.Rat, R.Rat.add(R.Rat.add(AC, Y), R.Rat.add(AF, W)),
            R.Rat.add(AC, R.Rat.add(Y, R.Rat.add(AF, W))),
            R.Rat.add_assoc.arb(AC, Y, R.Rat.add(AF, W), pAC, pY, pZW))))))
  +t1 = Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(A, R.Rat.add(C, F)),
              R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(E, G)))),
    S1, S2, l1, l2)
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(A, R.Rat.add(C, F)),
              R.Rat.mul(D, R.Rat.mul(B, R.Rat.add(E, G)))),
    S2,
    R.Rat.add(R.Rat.add(AC, Y), R.Rat.add(AF, W)),
    t1, l3)

# QExt.mul_distrib.im: the imaginary coordinate is the same shape with two
# products of sums instead of three -- A*(E + G) + B*(C + F) against
# (A*E + B*C) + (A*G + B*F) -- so it is Rat.mul_distrib.arb twice and the same
# five-step rearrangement.
def QExt.mul_distrib.im(+d: Nat, +xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat,
                        +za: R.Rat, +zb: R.Rat,
                        +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                        +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                        +gy: {Nat.cmp(0n, R.Rat.denof(ya)) == LT{} : Cmp},
                        +hy: {Nat.cmp(0n, R.Rat.denof(yb)) == LT{} : Cmp},
                        +gz: {Nat.cmp(0n, R.Rat.denof(za)) == LT{} : Cmp},
                        +hz: {Nat.cmp(0n, R.Rat.denof(zb)) == LT{} : Cmp})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.add(yb, zb)),
                R.Rat.mul(xb, R.Rat.add(ya, za)))
      == R.Rat.add(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)),
                   R.Rat.add(R.Rat.mul(xa, zb), R.Rat.mul(xb, za))) : R.Rat}:
  +A = xa
  +B = xb
  +C = ya
  +E = yb
  +F = za
  +G = zb
  +AE = R.Rat.mul(A, E)
  +AG = R.Rat.mul(A, G)
  +BC = R.Rat.mul(B, C)
  +BF = R.Rat.mul(B, F)
  +pAE = R.Rat.mul.den.pos(A, E, gx, hy)
  +pAG = R.Rat.mul.den.pos(A, G, gx, hz)
  +pBC = R.Rat.mul.den.pos(B, C, hx, gy)
  +pBF = R.Rat.mul.den.pos(B, F, hx, gz)
  +pAGBC = R.Rat.add.den.pos(AG, BC, pAG, pBC)
  +pBCAG = R.Rat.add.den.pos(BC, AG, pBC, pAG)
  +pAGBF = R.Rat.add.den.pos(AG, BF, pAG, pBF)
  +pBCBF = R.Rat.add.den.pos(BC, BF, pBC, pBF)
  +S1 = R.Rat.add(R.Rat.add(AE, AG), R.Rat.mul(B, R.Rat.add(C, F)))
  +S2 = R.Rat.add(R.Rat.add(AE, AG), R.Rat.add(BC, BF))
  +l1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(B, R.Rat.add(C, F))),
    R.Rat.mul(A, R.Rat.add(E, G)),
    R.Rat.add(AE, AG),
    R.Rat.mul_distrib.arb(A, E, G, gx, hy, hz))
  +l2 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(R.Rat.add(AE, AG), u),
    R.Rat.mul(B, R.Rat.add(C, F)),
    R.Rat.add(BC, BF),
    R.Rat.mul_distrib.arb(B, C, F, hx, gy, gz))
  +l3 = Equal.trans(R.Rat,
    S2,
    R.Rat.add(AE, R.Rat.add(AG, R.Rat.add(BC, BF))),
    R.Rat.add(R.Rat.add(AE, BC), R.Rat.add(AG, BF)),
    R.Rat.add_assoc.arb(AE, AG, R.Rat.add(BC, BF), pAE, pAG, pBCBF),
    Equal.trans(R.Rat,
      R.Rat.add(AE, R.Rat.add(AG, R.Rat.add(BC, BF))),
      R.Rat.add(AE, R.Rat.add(R.Rat.add(AG, BC), BF)),
      R.Rat.add(R.Rat.add(AE, BC), R.Rat.add(AG, BF)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AE, u),
        R.Rat.add(AG, R.Rat.add(BC, BF)), R.Rat.add(R.Rat.add(AG, BC), BF),
        Equal.sym(R.Rat, R.Rat.add(R.Rat.add(AG, BC), BF), R.Rat.add(AG, R.Rat.add(BC, BF)),
          R.Rat.add_assoc.arb(AG, BC, BF, pAG, pBC, pBF))),
      Equal.trans(R.Rat,
        R.Rat.add(AE, R.Rat.add(R.Rat.add(AG, BC), BF)),
        R.Rat.add(AE, R.Rat.add(R.Rat.add(BC, AG), BF)),
        R.Rat.add(R.Rat.add(AE, BC), R.Rat.add(AG, BF)),
        Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AE, u),
          R.Rat.add(R.Rat.add(AG, BC), BF), R.Rat.add(R.Rat.add(BC, AG), BF),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, BF),
            R.Rat.add(AG, BC), R.Rat.add(BC, AG), R.Rat.add_comm(AG, BC))),
        Equal.trans(R.Rat,
          R.Rat.add(AE, R.Rat.add(R.Rat.add(BC, AG), BF)),
          R.Rat.add(AE, R.Rat.add(BC, R.Rat.add(AG, BF))),
          R.Rat.add(R.Rat.add(AE, BC), R.Rat.add(AG, BF)),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(AE, u),
            R.Rat.add(R.Rat.add(BC, AG), BF), R.Rat.add(BC, R.Rat.add(AG, BF)),
            R.Rat.add_assoc.arb(BC, AG, BF, pBC, pAG, pBF)),
          Equal.sym(R.Rat, R.Rat.add(R.Rat.add(AE, BC), R.Rat.add(AG, BF)),
            R.Rat.add(AE, R.Rat.add(BC, R.Rat.add(AG, BF))),
            R.Rat.add_assoc.arb(AE, BC, R.Rat.add(AG, BF), pAE, pBC, pAGBF))))))
  +t1 = Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(A, R.Rat.add(E, G)), R.Rat.mul(B, R.Rat.add(C, F))),
    S1, S2, l1, l2)
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(A, R.Rat.add(E, G)), R.Rat.mul(B, R.Rat.add(C, F))),
    S2,
    R.Rat.add(R.Rat.add(AE, BC), R.Rat.add(AG, BF)),
    t1, l3)

# QExt.mul_distrib: two coordinate steps, as QExt.mul_assoc.
def Q.QExt.mul_distrib(d, x, y, z, gx, hx, gy, hy, gz, hz):
  match x y z:
    case Q.QExt{xa, xb} Q.QExt{ya, yb} Q.QExt{za, zb}:
      +D = Q.QExt.nat(d)
      +Lr = R.Rat.add(R.Rat.mul(xa, R.Rat.add(ya, za)),
                      R.Rat.mul(D, R.Rat.mul(xb, R.Rat.add(yb, zb))))
      +Li = R.Rat.add(R.Rat.mul(xa, R.Rat.add(yb, zb)),
                      R.Rat.mul(xb, R.Rat.add(ya, za)))
      +Rr = R.Rat.add(R.Rat.add(R.Rat.mul(xa, ya), R.Rat.mul(D, R.Rat.mul(xb, yb))),
                      R.Rat.add(R.Rat.mul(xa, za), R.Rat.mul(D, R.Rat.mul(xb, zb))))
      +Ri = R.Rat.add(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya)),
                      R.Rat.add(R.Rat.mul(xa, zb), R.Rat.mul(xb, za)))
      Equal.trans(Q.QExt,
        Q.QExt{Lr, Li},
        Q.QExt{Rr, Li},
        Q.QExt{Rr, Ri},
        qext.re(Li, Lr, Rr,
          QExt.mul_distrib.re(d, xa, xb, ya, yb, za, zb, gx, hx, gy, hy, gz, hz)),
        qext.im(Rr, Li, Ri,
          QExt.mul_distrib.im(d, xa, xb, ya, yb, za, zb, gx, hx, gy, hy, gz, hz)))

# QExt.mul_conj
# =============
#
# The rationalization, division-free: the two coordinates of x*conj(x) are now
# ordinary Rat chains over the two coefficients, and every step in them is a law
# that landed with the negation block.
#
# The real coordinate starts at xa*xa + D*(xb*(-xb)) and ends at
# Rat.sub(xa*xa, D*(xb*xb)) = xa*xa + (-(D*(xb*xb))): Rat.mul_neg at (xb,xb)
# under the radicand cong, then Rat.mul_neg at (D, xb*xb) to pull the negation
# out of the product, and the last step is `{==}`, since Rat.sub *is*
# Rat.add with a negated second summand.
#
# The imaginary coordinate is xa*(-xb) + xb*xa: Rat.mul_neg at (xa,xb) makes the
# first summand -(xa*xb), Rat.mul_comm makes the second one xa*xb, Rat.add_comm
# puts the sum in the order Rat.add_neg wants, and Rat.add_neg closes it at
# zero.
#
# The positivity the three Rat laws ask for is the two hypotheses plus the two
# derived facts: Rat.mul.den.pos for xb*xb (the radicand product's second
# factor) and for xa*xb (the value the additive law is applied to).

def QExt.mul_conj.re(+d: Nat, +xa: R.Rat, +xb: R.Rat,
                     +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp})
  -> {R.Rat.add(R.Rat.mul(xa, xa),
                R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, R.Rat.neg(xb))))
      == R.Rat.sub(R.Rat.mul(xa, xa),
                   R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, xb))) : R.Rat}:
  +D = Q.QExt.nat(d)
  +E = R.Rat.mul(xb, xb)
  +e1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(xa, xa), R.Rat.mul(D, u)),
    R.Rat.mul(xb, R.Rat.neg(xb)), R.Rat.neg(R.Rat.mul(xb, xb)),
    R.Rat.mul_neg(xb, xb, hx, hx))
  +e2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(xa, xa), u),
    R.Rat.mul(D, R.Rat.neg(E)), R.Rat.neg(R.Rat.mul(D, E)),
    R.Rat.mul_neg(D, E, {==}, R.Rat.mul.den.pos(xb, xb, hx, hx)))
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, xa), R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(xb)))),
    R.Rat.add(R.Rat.mul(xa, xa), R.Rat.mul(D, R.Rat.neg(E))),
    R.Rat.sub(R.Rat.mul(xa, xa), R.Rat.mul(D, E)),
    e1,
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(xa, xa), R.Rat.mul(D, R.Rat.neg(E))),
      R.Rat.add(R.Rat.mul(xa, xa), R.Rat.neg(R.Rat.mul(D, E))),
      R.Rat.sub(R.Rat.mul(xa, xa), R.Rat.mul(D, E)),
      e2,
      {==}))

def QExt.mul_conj.im(+xa: R.Rat, +xb: R.Rat,
                     +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                     +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.neg(xb)), R.Rat.mul(xb, xa))
      == R.Rat.zero() : R.Rat}:
  +U = R.Rat.mul(xa, xb)
  +e1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat.mul(xb, xa)),
    R.Rat.mul(xa, R.Rat.neg(xb)), R.Rat.neg(R.Rat.mul(xa, xb)),
    R.Rat.mul_neg(xa, xb, gx, hx))
  +e2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(U), u),
    R.Rat.mul(xb, xa), R.Rat.mul(xa, xb), R.Rat.mul_comm(xb, xa))
  +e3 = R.Rat.add_comm(R.Rat.neg(U), U)
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.neg(xb)), R.Rat.mul(xb, xa)),
    R.Rat.add(R.Rat.neg(U), U),
    R.Rat.zero(),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(xa, R.Rat.neg(xb)), R.Rat.mul(xb, xa)),
      R.Rat.add(R.Rat.neg(U), R.Rat.mul(xb, xa)),
      R.Rat.add(R.Rat.neg(U), U),
      e1, e2),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.neg(U), U),
      R.Rat.add(U, R.Rat.neg(U)),
      R.Rat.zero(),
      e3,
      R.Rat.add_neg(U, R.Rat.mul.den.pos(xa, xb, gx, hx))))

def Q.QExt.mul_conj(d, x, gx, hx):
  match x:
    case Q.QExt{xa, xb}:
      +D = Q.QExt.nat(d)
      +Lr = R.Rat.add(R.Rat.mul(xa, xa),
                      R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(xb))))
      +Li = R.Rat.add(R.Rat.mul(xa, R.Rat.neg(xb)), R.Rat.mul(xb, xa))
      +Rr = R.Rat.sub(R.Rat.mul(xa, xa), R.Rat.mul(D, R.Rat.mul(xb, xb)))
      Equal.trans(Q.QExt,
        Q.QExt{Lr, Li},
        Q.QExt{Rr, Li},
        Q.QExt{Rr, R.Rat.zero()},
        qext.re(Li, Lr, Rr, QExt.mul_conj.re(d, xa, xb, hx)),
        qext.im(Rr, Li, R.Rat.zero(), QExt.mul_conj.im(xa, xb, gx, hx)))

# QExt.mul_one
# ============
#
# The identity at the canonical presentation. Each coordinate is a sum of two
# products against Rat.one() and Rat.zero(), and every step is one of the four
# Rat identity laws spent at the spelling the coordinate already carries:
# Rat.mul_zero for the two imaginary products, Rat.mul_one and one of
# Rat.add_zero / Rat.zero_add for the sum. The only term with no law behind it
# is the real coordinate's QExt.nat(d) * 0, which qext.nat.mul_zero supplies.
#
# The intermediate terms are written unreduced, as everywhere in this file: the
# coordinate witness holds the other coordinate, so both steps of the composing
# fill have to meet at the same spelling of the coordinate that is not being
# touched.

def QExt.mul_one.re(+d: Nat, +np: Nat, +nn: Nat, +dp: Nat,
                    +mq: Nat, +mn: Nat, +dq: Nat,
                    +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                          == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat})
  -> {R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat.one()),
                R.Rat.mul(Q.QExt.nat(d),
                  R.Rat.mul(R.Rat{R.Rat.num(mq, mn), 1n+dq}, R.Rat.zero())))
      == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}:
  +D = Q.QExt.nat(d)
  +XA = R.Rat.of(np, nn, dp)
  +XB = R.Rat.of(mq, mn, dq)
  +A1 = R.Rat.add(R.Rat.mul(XA, R.Rat.one()), R.Rat.mul(D, R.Rat.mul(XB, R.Rat.zero())))
  +A2 = R.Rat.add(R.Rat.mul(XA, R.Rat.one()), R.Rat.mul(D, R.Rat.zero()))
  +A3 = R.Rat.add(R.Rat.mul(XA, R.Rat.one()), R.Rat.zero())
  +A4 = R.Rat.add(XA, R.Rat.zero())
  +e1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(XA, R.Rat.one()), u),
    R.Rat.mul(D, R.Rat.mul(XB, R.Rat.zero())), R.Rat.mul(D, R.Rat.zero()),
    Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(D, u),
      R.Rat.mul(XB, R.Rat.zero()), R.Rat.zero(),
      R.Rat.mul_zero(R.Rat.num(mq, mn), dq)))
  +e2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(XA, R.Rat.one()), u),
    R.Rat.mul(D, R.Rat.zero()), R.Rat.zero(), qext.nat.mul_zero(d))
  +e3 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat.zero()),
    R.Rat.mul(XA, R.Rat.one()), XA,
    R.Rat.mul_one(R.Rat.num(np, nn), 1n+dp, f1))
  +e4 = R.Rat.add_zero(R.Rat.num(np, nn), 1n+dp, f1)
  Equal.trans(R.Rat, A1, A3, XA,
    Equal.trans(R.Rat, A1, A2, A3, e1, e2),
    Equal.trans(R.Rat, A3, A4, XA, e3, e4))

def QExt.mul_one.im(+np: Nat, +nn: Nat, +dp: Nat,
                    +mq: Nat, +mn: Nat, +dq: Nat,
                    +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                          == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat})
  -> {R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat.zero()),
                R.Rat.mul(R.Rat{R.Rat.num(mq, mn), 1n+dq}, R.Rat.one()))
      == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}:
  +XA = R.Rat.of(np, nn, dp)
  +XB = R.Rat.of(mq, mn, dq)
  +B1 = R.Rat.add(R.Rat.mul(XA, R.Rat.zero()), R.Rat.mul(XB, R.Rat.one()))
  +B2 = R.Rat.add(R.Rat.zero(), R.Rat.mul(XB, R.Rat.one()))
  +B3 = R.Rat.add(R.Rat.zero(), XB)
  +e1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat.mul(XB, R.Rat.one())),
    R.Rat.mul(XA, R.Rat.zero()), R.Rat.zero(),
    R.Rat.mul_zero(R.Rat.num(np, nn), dp))
  +e2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.zero(), u),
    R.Rat.mul(XB, R.Rat.one()), XB,
    R.Rat.mul_one(R.Rat.num(mq, mn), 1n+dq, f2))
  Equal.trans(R.Rat, B1, B3, XB,
    Equal.trans(R.Rat, B1, B2, B3, e1, e2),
    R.Rat.zero_add(R.Rat.num(mq, mn), 1n+dq, f2))

def Q.QExt.mul_one(d, np, nn, dp, mq, mn, dq, f1, f2):
  +D = Q.QExt.nat(d)
  +XA = R.Rat.of(np, nn, dp)
  +XB = R.Rat.of(mq, mn, dq)
  +A1 = R.Rat.add(R.Rat.mul(XA, R.Rat.one()), R.Rat.mul(D, R.Rat.mul(XB, R.Rat.zero())))
  +B1 = R.Rat.add(R.Rat.mul(XA, R.Rat.zero()), R.Rat.mul(XB, R.Rat.one()))
  Equal.trans(Q.QExt,
    Q.QExt.mul(d, Q.QExt.of(np, nn, dp, mq, mn, dq), Q.QExt.one()),
    Q.QExt{XA, B1},
    Q.QExt{XA, XB},
    qext.re(B1, A1, XA, QExt.mul_one.re(d, np, nn, dp, mq, mn, dq, f1)),
    qext.im(XA, B1, XB, QExt.mul_one.im(np, nn, dp, mq, mn, dq, f2)))

# QExt.add_zero / QExt.zero_add / QExt.add_neg
# ===========================================
#
# The additive identity and inverse. The first two are one Rat.add_zero /
# Rat.zero_add call per coordinate with nothing in between: QExt.add is
# componentwise, so once the coordinates are read the goal *is* the Rat law's
# statement, and the composing fill needs no chain -- just the two coordinate
# witnesses, at the same spelling mul_one's compose uses.
#
# add_neg is at arbitrary values and gets nothing from the spelling: Rat.add_neg
# takes a coefficient and its denominator's positivity, and its conclusion is
# Rat.zero() on the nose, so each coordinate is one call. QExt.neg is
# componentwise too, so the two sides of the coordinate equation are both
# compositions and == compares them directly -- no canonical presentation, no
# bridges, no trans chain beyond the two-coordinate compose.

def QExt.add_zero.re(+np: Nat, +nn: Nat, +dp: Nat,
                     +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                           == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat})
  -> {R.Rat.add(R.Rat{R.Rat.num(np, nn), 1n+dp}, R.Rat.zero())
      == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}:
  R.Rat.add_zero(R.Rat.num(np, nn), 1n+dp, f1)

def QExt.add_zero.im(+mq: Nat, +mn: Nat, +dq: Nat,
                     +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                           == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat})
  -> {R.Rat.add(R.Rat{R.Rat.num(mq, mn), 1n+dq}, R.Rat.zero())
      == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}:
  R.Rat.add_zero(R.Rat.num(mq, mn), 1n+dq, f2)

def Q.QExt.add_zero(np, nn, dp, mq, mn, dq, f1, f2):
  +XA = R.Rat.of(np, nn, dp)
  +XB = R.Rat.of(mq, mn, dq)
  +A1 = R.Rat.add(XA, R.Rat.zero())
  +B1 = R.Rat.add(XB, R.Rat.zero())
  Equal.trans(Q.QExt,
    Q.QExt.add(Q.QExt.of(np, nn, dp, mq, mn, dq), Q.QExt.zero()),
    Q.QExt{XA, B1},
    Q.QExt{XA, XB},
    qext.re(B1, A1, XA, QExt.add_zero.re(np, nn, dp, f1)),
    qext.im(XA, B1, XB, QExt.add_zero.im(mq, mn, dq, f2)))

def QExt.zero_add.re(+np: Nat, +nn: Nat, +dp: Nat,
                     +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                           == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat})
  -> {R.Rat.add(R.Rat.zero(), R.Rat{R.Rat.num(np, nn), 1n+dp})
      == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}:
  R.Rat.zero_add(R.Rat.num(np, nn), 1n+dp, f1)

def QExt.zero_add.im(+mq: Nat, +mn: Nat, +dq: Nat,
                     +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                           == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat})
  -> {R.Rat.add(R.Rat.zero(), R.Rat{R.Rat.num(mq, mn), 1n+dq})
      == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat}:
  R.Rat.zero_add(R.Rat.num(mq, mn), 1n+dq, f2)

def Q.QExt.zero_add(np, nn, dp, mq, mn, dq, f1, f2):
  +XA = R.Rat.of(np, nn, dp)
  +XB = R.Rat.of(mq, mn, dq)
  +A1 = R.Rat.add(R.Rat.zero(), XA)
  +B1 = R.Rat.add(R.Rat.zero(), XB)
  Equal.trans(Q.QExt,
    Q.QExt.add(Q.QExt.zero(), Q.QExt.of(np, nn, dp, mq, mn, dq)),
    Q.QExt{XA, B1},
    Q.QExt{XA, XB},
    qext.re(B1, A1, XA, QExt.zero_add.re(np, nn, dp, f1)),
    qext.im(XA, B1, XB, QExt.zero_add.im(mq, mn, dq, f2)))

def Q.QExt.add_neg(x, gx, hx):
  match x:
    case Q.QExt{+xa, +xb}:
      +A1 = R.Rat.add(xa, R.Rat.neg(xa))
      +B1 = R.Rat.add(xb, R.Rat.neg(xb))
      Equal.trans(Q.QExt,
        Q.QExt.add(Q.QExt{xa, xb}, Q.QExt.neg(Q.QExt{xa, xb})),
        Q.QExt{R.Rat.zero(), B1},
        Q.QExt.zero(),
        qext.re(B1, A1, R.Rat.zero(), R.Rat.add_neg(xa, gx)),
        qext.im(R.Rat.zero(), B1, R.Rat.zero(), R.Rat.add_neg(xb, hx)))

# QExt.neg_add / QExt.mul_neg / QExt.neg_mul
# ==========================================
#
# The negation laws, all three over arbitrary values: the QExt twins of
# Rat.neg_add.arb, Rat.mul_neg and Rat.neg_mul, and the reason this unit added a
# Rat law rather than a bridge. Every coordinate of these laws is a sum of two
# *operation outputs* (products, or products of products), which is exactly the
# shape the canonical Rat.neg_add cannot take -- so the Rat-level rung-2 form
# Rat.neg_add.arb is what carries the negation across the sums here, and each
# coordinate's products are then negated one factor at a time by Rat.mul_neg.
#
# QExt.neg_add is two calls, one per coordinate, composed at the real coordinate
# and then at the imaginary one -- the same two-step shape QExt.add_neg uses.
def Q.QExt.neg_add(x, y, gx, gy, hx, hy):
  match x:
    case Q.QExt{+xa, +xb}:
      match y:
        case Q.QExt{+ya, +yb}:
          +R1 = R.Rat.add(R.Rat.neg(xa), R.Rat.neg(ya))
          +I0 = R.Rat.neg(R.Rat.add(xb, yb))
          Equal.trans(Q.QExt,
            Q.QExt.neg(Q.QExt.add(Q.QExt{xa, xb}, Q.QExt{ya, yb})),
            Q.QExt{R1, I0},
            Q.QExt.add(Q.QExt.neg(Q.QExt{xa, xb}), Q.QExt.neg(Q.QExt{ya, yb})),
            qext.re(I0, R.Rat.neg(R.Rat.add(xa, ya)), R1,
              R.Rat.neg_add.arb(xa, ya, gx, gy)),
            qext.im(R1, I0, R.Rat.add(R.Rat.neg(xb), R.Rat.neg(yb)),
              R.Rat.neg_add.arb(xb, yb, hx, hy)))

# QExt.mul_neg's real coordinate: the negation travels from the second factor's
# two coefficients to the product. xa*(-ya) -> -(xa*ya) is Rat.mul_neg; the
# radicand term xb*(-yb) gets the same law under a congruence to become
# d*(-(xb*yb)), and then one more Rat.mul_neg -- at the *product* rather than at a
# coefficient -- pulls d inside the negation. The two negations are then merged
# into the negation of the sum by Rat.neg_add.arb, read backwards.
def QExt.mul_neg.re(+d: Nat, +xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat,
                    +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                    +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                    +gy: {Nat.cmp(0n, R.Rat.denof(ya)) == LT{} : Cmp},
                    +hy: {Nat.cmp(0n, R.Rat.denof(yb)) == LT{} : Cmp})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.neg(ya)),
                R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, R.Rat.neg(yb))))
      == R.Rat.neg(R.Rat.add(R.Rat.mul(xa, ya),
                             R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb)))) : R.Rat}:
  +D = Q.QExt.nat(d)
  +P = R.Rat.mul(xa, ya)
  +E = R.Rat.mul(xb, yb)
  +Q = R.Rat.mul(D, E)
  +pE = R.Rat.mul.den.pos(xb, yb, hx, hy)
  +e1 = Equal.cong(R.Rat, R.Rat,
    u => R.Rat.add(u, R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(yb)))),
    R.Rat.mul(xa, R.Rat.neg(ya)), R.Rat.neg(P), R.Rat.mul_neg(xa, ya, gx, gy))
  +e2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(P), u),
    R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(yb))), R.Rat.neg(Q),
    Equal.trans(R.Rat,
      R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(yb))),
      R.Rat.mul(D, R.Rat.neg(E)),
      R.Rat.neg(Q),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(D, u),
        R.Rat.mul(xb, R.Rat.neg(yb)), R.Rat.neg(E),
        R.Rat.mul_neg(xb, yb, hx, hy)),
      R.Rat.mul_neg(D, E, {==}, pE)))
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.neg(ya)),
              R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(yb)))),
    R.Rat.add(R.Rat.neg(P), R.Rat.neg(Q)),
    R.Rat.neg(R.Rat.add(P, Q)),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(xa, R.Rat.neg(ya)),
                R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(yb)))),
      R.Rat.add(R.Rat.neg(P), R.Rat.mul(D, R.Rat.mul(xb, R.Rat.neg(yb)))),
      R.Rat.add(R.Rat.neg(P), R.Rat.neg(Q)),
      e1, e2),
    Equal.sym(R.Rat, R.Rat.neg(R.Rat.add(P, Q)),
      R.Rat.add(R.Rat.neg(P), R.Rat.neg(Q)),
      R.Rat.neg_add.arb(P, Q, R.Rat.mul.den.pos(xa, ya, gx, gy),
        R.Rat.mul.den.pos(D, E, {==}, pE))))

# QExt.mul_neg's imaginary coordinate: the same three steps with no radicand in
# sight -- xa*(-yb) -> -(xa*yb) and xb*(-ya) -> -(xb*ya) by Rat.mul_neg, merged
# into the negation of the sum by Rat.neg_add.arb read backwards.
def QExt.mul_neg.im(+xa: R.Rat, +xb: R.Rat, +ya: R.Rat, +yb: R.Rat,
                    +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                    +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                    +gy: {Nat.cmp(0n, R.Rat.denof(ya)) == LT{} : Cmp},
                    +hy: {Nat.cmp(0n, R.Rat.denof(yb)) == LT{} : Cmp})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.neg(yb)), R.Rat.mul(xb, R.Rat.neg(ya)))
      == R.Rat.neg(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))) : R.Rat}:
  +P = R.Rat.mul(xa, yb)
  +Q = R.Rat.mul(xb, ya)
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.neg(yb)), R.Rat.mul(xb, R.Rat.neg(ya))),
    R.Rat.add(R.Rat.neg(P), R.Rat.neg(Q)),
    R.Rat.neg(R.Rat.add(P, Q)),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(xa, R.Rat.neg(yb)), R.Rat.mul(xb, R.Rat.neg(ya))),
      R.Rat.add(R.Rat.neg(P), R.Rat.mul(xb, R.Rat.neg(ya))),
      R.Rat.add(R.Rat.neg(P), R.Rat.neg(Q)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat.mul(xb, R.Rat.neg(ya))),
        R.Rat.mul(xa, R.Rat.neg(yb)), R.Rat.neg(P),
        R.Rat.mul_neg(xa, yb, gx, hy)),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(P), u),
        R.Rat.mul(xb, R.Rat.neg(ya)), R.Rat.neg(Q),
        R.Rat.mul_neg(xb, ya, hx, gy))),
    Equal.sym(R.Rat, R.Rat.neg(R.Rat.add(P, Q)),
      R.Rat.add(R.Rat.neg(P), R.Rat.neg(Q)),
      R.Rat.neg_add.arb(P, Q, R.Rat.mul.den.pos(xa, yb, gx, hy),
        R.Rat.mul.den.pos(xb, ya, hx, gy))))

def Q.QExt.mul_neg(d, x, y, gx, hx, gy, hy):
  match x:
    case Q.QExt{xa, xb}:
      match y:
        case Q.QExt{ya, yb}:
          +Lr = R.Rat.add(R.Rat.mul(xa, R.Rat.neg(ya)),
                          R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, R.Rat.neg(yb))))
          +Li = R.Rat.add(R.Rat.mul(xa, R.Rat.neg(yb)),
                          R.Rat.mul(xb, R.Rat.neg(ya)))
          +Rr = R.Rat.neg(R.Rat.add(R.Rat.mul(xa, ya),
                                    R.Rat.mul(Q.QExt.nat(d), R.Rat.mul(xb, yb))))
          Equal.trans(Q.QExt,
            Q.QExt.mul(d, Q.QExt{xa, xb}, Q.QExt.neg(Q.QExt{ya, yb})),
            Q.QExt{Rr, Li},
            Q.QExt.neg(Q.QExt.mul(d, Q.QExt{xa, xb}, Q.QExt{ya, yb})),
            qext.re(Li, Lr, Rr,
              QExt.mul_neg.re(d, xa, xb, ya, yb, gx, hx, gy, hy)),
            qext.im(Rr, Li,
              R.Rat.neg(R.Rat.add(R.Rat.mul(xa, yb), R.Rat.mul(xb, ya))),
              QExt.mul_neg.im(xa, xb, ya, yb, gx, hx, gy, hy)))

# QExt.neg_mul is QExt.mul_neg with the factors swapped: commutativity moves the
# negation into the second slot, the law above spends it, and commutativity moves
# the factors back. Three steps and no coordinate of its own -- which is also why
# this law is the mirror of QExt.mul_neg's statement rather than a second
# derivation of it.
def Q.QExt.neg_mul(d, x, y, gx, hx, gy, hy):
  Equal.trans(Q.QExt,
    Q.QExt.mul(d, Q.QExt.neg(x), y),
    Q.QExt.mul(d, y, Q.QExt.neg(x)),
    Q.QExt.neg(Q.QExt.mul(d, x, y)),
    Q.QExt.mul_comm(d, Q.QExt.neg(x), y),
    Equal.trans(Q.QExt,
      Q.QExt.mul(d, y, Q.QExt.neg(x)),
      Q.QExt.neg(Q.QExt.mul(d, y, x)),
      Q.QExt.neg(Q.QExt.mul(d, x, y)),
      Q.QExt.mul_neg(d, y, x, gy, hy, gx, hx),
      Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.neg(u),
        Q.QExt.mul(d, y, x), Q.QExt.mul(d, x, y), Q.QExt.mul_comm(d, y, x))))

# QExt.conj_add / QExt.conj_conj
# ==============================
#
# The conjugate: additive, and an involution. QExt.conj negates the imaginary
# coefficient alone, so additivity is one Rat.neg_add.arb at the imaginary
# coordinate and nothing at the real one -- that coordinate is the same term on
# both sides, which is why this law's hypotheses are the imaginary coefficients'
# only.
def Q.QExt.conj_add(x, y, hx, hy):
  match x:
    case Q.QExt{+xa, +xb}:
      match y:
        case Q.QExt{+ya, +yb}:
          qext.im(R.Rat.add(xa, ya), R.Rat.neg(R.Rat.add(xb, yb)),
            R.Rat.add(R.Rat.neg(xb), R.Rat.neg(yb)),
            R.Rat.neg_add.arb(xb, yb, hx, hy))

# The involution is one Rat.neg_neg at the imaginary coordinate: conj(conj(x)) has
# re(x) unchanged and neg(neg(im x)) where x has im x, so the real coordinate
# needs no step at all. Rat.neg_neg is called at the law's own telescope -- its
# comparison is the literal Nat.cmp of the coordinate and its evidence `{==}`,
# exactly as QExt.neg_neg above calls it.
def Q.QExt.conj_conj(np, nn, dp, mq, mn, dq, h):
  +RE = R.Rat.of(np, nn, dp)
  +IM = R.Rat.of(mq, mn, dq)
  qext.im(RE, R.Rat.neg(R.Rat.neg(IM)), IM,
    R.Rat.neg_neg(Nat.cmp(mq, mn), mq, mn, dq, {==}, h))

# Q.QExt.conj_mul
# ===============
#
# Two Rat lanes, composed by the two-step idiom the other QExt fills use: the
# real lane runs first, with the imaginary coordinate still spelled the way the
# left side has it, and then the imaginary lane runs against the already-rewritten
# real one -- which is why the first witness keeps neg(L0) as its other
# coordinate rather than the lane's own end.
#
# Real: the bracket mul(neg xi, neg yi) -> mul(xi, yi) is one call to
# Rat.mul.neg_neg.reduced under the congruence that puts it back inside the
# radicand product. Nothing else moves, because mul(xr,yr) is a variable here: no
# normalization is in play, so both sides spell the first summand identically.
#
# Imaginary: the left side's neg(add(mul(xr,yi), mul(xi,yr))) is split by
# Rat.neg_add.arb -- whose two summands are *products*, which is exactly why that
# rung-2 law was added this unit -- and each half is then negated one factor at a
# time by Rat.mul_neg and Rat.neg_mul. Both of those are cited through Equal.sym:
# mul_neg states mul(x, neg y) = neg(mul(x, y)) and neg_mul its mirror
# mul(neg x, y) = neg(mul(x, y)), while both legs here run from the negated
# product back to the negated factor. Every positivity hypothesis in the lane is
# `{==}`: a QExt.of coefficient has a successor denominator, and the products
# Rat.mul.den.pos is asked about are built from those.
def Q.QExt.conj_mul(d, np, nn, dp, mq, mn, dq, rp, rn, dr, sp, sn, ds, h1, h2):
  +p = Q.QExt.nat(d)
  +X = Q.QExt.of(np, nn, dp, mq, mn, dq)
  +Y = Q.QExt.of(rp, rn, dr, sp, sn, ds)
  +xr = R.Rat.of(np, nn, dp)
  +xi = R.Rat.of(mq, mn, dq)
  +yr = R.Rat.of(rp, rn, dr)
  +yi = R.Rat.of(sp, sn, ds)
  +P = R.Rat.mul(xr, yr)
  +Q = R.Rat.mul(p, R.Rat.mul(xi, yi))
  +QN = R.Rat.mul(p, R.Rat.mul(R.Rat.neg(xi), R.Rat.neg(yi)))
  +L0 = R.Rat.add(R.Rat.mul(xr, yi), R.Rat.mul(xi, yr))
  +NXY = R.Rat.neg(R.Rat.mul(xr, yi))
  +NYX = R.Rat.neg(R.Rat.mul(xi, yr))
  +IM1 = R.Rat.add(R.Rat.mul(xr, R.Rat.neg(yi)), R.Rat.mul(R.Rat.neg(xi), yr))
  +reL = Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xr, yr), Q),
    R.Rat.add(P, Q),
    R.Rat.add(P, QN),
    {==},
    Equal.cong(R.Rat, R.Rat, u => R.Rat.add(P, u), Q, QN,
      Equal.cong(R.Rat, R.Rat, v => R.Rat.mul(p, v),
        R.Rat.mul(xi, yi), R.Rat.mul(R.Rat.neg(xi), R.Rat.neg(yi)),
        Equal.sym(R.Rat, R.Rat.mul(R.Rat.neg(xi), R.Rat.neg(yi)),
          R.Rat.mul(xi, yi),
          R.Rat.mul.neg_neg.reduced(mq, mn, dq, sp, sn, ds, h1, h2)))))
  +imL = Equal.trans(R.Rat,
    R.Rat.neg(L0),
    R.Rat.add(NXY, NYX),
    IM1,
    R.Rat.neg_add.arb(R.Rat.mul(xr, yi), R.Rat.mul(xi, yr),
      R.Rat.mul.den.pos(xr, yi, {==}, {==}),
      R.Rat.mul.den.pos(xi, yr, {==}, {==})),
    Equal.trans(R.Rat,
      R.Rat.add(NXY, NYX),
      R.Rat.add(R.Rat.mul(xr, R.Rat.neg(yi)), NYX),
      IM1,
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, NYX), NXY,
        R.Rat.mul(xr, R.Rat.neg(yi)),
        Equal.sym(R.Rat, R.Rat.mul(xr, R.Rat.neg(yi)), NXY,
          R.Rat.mul_neg(xr, yi, {==}, {==}))),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(xr, R.Rat.neg(yi)), u),
        NYX, R.Rat.mul(R.Rat.neg(xi), yr),
        Equal.sym(R.Rat, R.Rat.mul(R.Rat.neg(xi), yr), NYX,
          R.Rat.neg_mul(xi, yr, {==}, {==})))))
  Equal.trans(Q.QExt,
    Q.QExt.conj(Q.QExt.mul(d, X, Y)),
    Q.QExt{R.Rat.add(P, QN), R.Rat.neg(L0)},
    Q.QExt.mul(d, Q.QExt.conj(X), Q.QExt.conj(Y)),
    qext.re(R.Rat.neg(L0), R.Rat.add(R.Rat.mul(xr, yr), Q), R.Rat.add(P, QN), reL),
    qext.im(R.Rat.add(P, QN), R.Rat.neg(L0), IM1, imL))

# The division payoff
# ===================
#
# QExt.inv.value.gt: x^-1 = conj(x)/norm(d,x), the rationalization. The left
# side of the law is QExt.mul of x by the conjugate divided by the norm, so its
# two coordinates are Rat sums of three-factor products -- and with the
# divisor's sign in the spelling, Rat.div has already unfolded to
# mul(coefficient, d/(1+ap)) by the time the fill sees it (measured: it is a
# conversion, no law involved), which is what makes this a rearrangement rather
# than a fight with a stuck Nat.cmp.
#
# The rearrangement is the one QExt.mul_conj already did, with the reciprocal
# carried along: the same b*(-b) -> -(b*b) (Rat.mul_neg) and d*(-(b*b)) ->
# -(d*(b*b)) (Rat.neg_mul, whose fill is the three-step mirror of Rat.mul_neg),
# the same pull-the-sum-apart in reverse (Rat.mul_add_left.arb), and then one
# congruence against hZ to re-spell the norm as the literal the divisor was
# written with, after which Rat.mul_inv.gt closes it. The imaginary coordinate
# is the mirror image: two products that are each other's negative plus one
# Rat.add_neg.

def QExt.inv.value.gt.re(+d: Nat, +xa: R.Rat, +xb: R.Rat,
                         +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                         +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                         +ap: Nat, +dp: Nat,
                         +hZ: {R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}
                               == Q.QExt.norm(d, Q.QExt{xa, xb}) : R.Rat})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.mul(xa, R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap})),
                 R.Rat.mul(Q.QExt.nat(d),
                   R.Rat.mul(xb, R.Rat.mul(R.Rat.neg(xb),
                                           R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap}))))
      == R.Rat.one() : R.Rat}:
  +nb = R.Rat.neg(xb)
  +D = Q.QExt.nat(d)
  +rh = R.Rat.of(1n+dp, 0n, ap)
  +Z = R.Rat.of(1n+ap, 0n, dp)
  +AA = R.Rat.mul(xa, xa)
  +BB = R.Rat.mul(xb, xb)
  +PP = R.Rat.mul(D, BB)
  +pAA = R.Rat.mul.den.pos(xa, xa, gx, gx)
  +pBB = R.Rat.mul.den.pos(xb, xb, hx, hx)
  +pPP = R.Rat.mul.den.pos(D, BB, {==}, pBB)
  +pnegPP = R.Rat.neg.den.pos(PP, pPP)
  # xa*(xa*rh) = (xa*xa)*rh, and the inner b*(nb*rh) = (b*nb)*rh
  +eA1 = Equal.sym(R.Rat, R.Rat.mul(AA, rh), R.Rat.mul(xa, R.Rat.mul(xa, rh)),
    R.Rat.mul_assoc.arb(xa, xa, rh, gx, gx, {==}))
  +eA2 = Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(xb, nb), rh),
    R.Rat.mul(xb, R.Rat.mul(nb, rh)),
    R.Rat.mul_assoc.arb(xb, nb, rh, hx, R.Rat.neg.den.pos(xb, hx), {==}))
  # xb*nb = -(xb*xb), then d*(-(b*b)*rh) = -(d*(b*b))*rh
  +eM1 = R.Rat.mul_neg(xb, xb, hx, hx)
  +eM2 = Equal.trans(R.Rat,
    R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh)),
    R.Rat.mul(D, R.Rat.neg(R.Rat.mul(BB, rh))),
    R.Rat.mul(R.Rat.neg(PP), rh),
    Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(D, u),
      R.Rat.mul(R.Rat.neg(BB), rh), R.Rat.neg(R.Rat.mul(BB, rh)),
      R.Rat.neg_mul(BB, rh, pBB, {==})),
    Equal.trans(R.Rat,
      R.Rat.mul(D, R.Rat.neg(R.Rat.mul(BB, rh))),
      R.Rat.neg(R.Rat.mul(D, R.Rat.mul(BB, rh))),
      R.Rat.mul(R.Rat.neg(PP), rh),
      R.Rat.mul_neg(D, R.Rat.mul(BB, rh), {==}, R.Rat.mul.den.pos(BB, rh, pBB, {==})),
      Equal.trans(R.Rat,
        R.Rat.neg(R.Rat.mul(D, R.Rat.mul(BB, rh))),
        R.Rat.neg(R.Rat.mul(PP, rh)),
        R.Rat.mul(R.Rat.neg(PP), rh),
        Equal.cong(R.Rat, R.Rat, u => R.Rat.neg(u),
          R.Rat.mul(D, R.Rat.mul(BB, rh)), R.Rat.mul(PP, rh),
          Equal.sym(R.Rat, R.Rat.mul(PP, rh), R.Rat.mul(D, R.Rat.mul(BB, rh)),
            R.Rat.mul_assoc.arb(D, BB, rh, {==}, pBB, {==}))),
        Equal.sym(R.Rat, R.Rat.mul(R.Rat.neg(PP), rh), R.Rat.neg(R.Rat.mul(PP, rh)),
          R.Rat.neg_mul(PP, rh, pPP, {==})))))
  # (xa*xa)*rh + (-(b*b*d))*rh = (xa*xa - b*b*d)*rh, read backwards
  +eSum = Equal.sym(R.Rat,
    R.Rat.mul(R.Rat.add(AA, R.Rat.neg(PP)), rh),
    R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(R.Rat.neg(PP), rh)),
    R.Rat.mul_add_left.arb(AA, R.Rat.neg(PP), rh, pAA, pnegPP, {==}))
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.mul(xa, rh)),
              R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
    R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
    R.Rat.one(),
    Equal.cong(R.Rat, R.Rat,
      u => R.Rat.add(u, R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
      R.Rat.mul(xa, R.Rat.mul(xa, rh)), R.Rat.mul(AA, rh), eA1),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
      R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.mul(xb, nb), rh))),
      R.Rat.one(),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, u)),
        R.Rat.mul(xb, R.Rat.mul(nb, rh)), R.Rat.mul(R.Rat.mul(xb, nb), rh), eA2),
      Equal.trans(R.Rat,
        R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.mul(xb, nb), rh))),
        R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh))),
        R.Rat.one(),
        Equal.cong(R.Rat, R.Rat,
          u => R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(u, rh))),
          R.Rat.mul(xb, nb), R.Rat.neg(BB), eM1),
        Equal.trans(R.Rat,
          R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh))),
          R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(R.Rat.neg(PP), rh)),
          R.Rat.one(),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(AA, rh), u),
            R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh)), R.Rat.mul(R.Rat.neg(PP), rh),
            eM2),
          Equal.trans(R.Rat,
            R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(R.Rat.neg(PP), rh)),
            R.Rat.mul(R.Rat.add(AA, R.Rat.neg(PP)), rh),
            R.Rat.one(),
            eSum,
            Equal.trans(R.Rat,
              R.Rat.mul(R.Rat.add(AA, R.Rat.neg(PP)), rh),
              R.Rat.mul(R.Rat.sub(AA, PP), rh),
              R.Rat.one(),
              {==},
              Equal.trans(R.Rat,
                R.Rat.mul(R.Rat.sub(AA, PP), rh),
                R.Rat.mul(Q.QExt.norm(d, Q.QExt{xa, xb}), rh),
                R.Rat.one(),
                {==},
                Equal.trans(R.Rat,
                  R.Rat.mul(Q.QExt.norm(d, Q.QExt{xa, xb}), rh),
                  R.Rat.mul(Z, rh),
                  R.Rat.one(),
                  Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(u, rh),
                    Q.QExt.norm(d, Q.QExt{xa, xb}), Z,
                    Equal.sym(R.Rat, Z, Q.QExt.norm(d, Q.QExt{xa, xb}), hZ)),
                  R.Rat.mul_inv.gt(1n+ap, 0n, dp, {==})))))))))

def QExt.inv.value.gt.im(+d: Nat, +xa: R.Rat, +xb: R.Rat,
                         +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                         +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                         +ap: Nat, +dp: Nat,
                         +hZ: {R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}
                               == Q.QExt.norm(d, Q.QExt{xa, xb}) : R.Rat})
  -> {R.Rat.add(R.Rat.mul(xa,
                   R.Rat.mul(R.Rat.neg(xb), R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap})),
                 R.Rat.mul(xb, R.Rat.mul(xa, R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap})))
      == R.Rat.zero() : R.Rat}:
  +nb = R.Rat.neg(xb)
  +rh = R.Rat.of(1n+dp, 0n, ap)
  +M = R.Rat.mul(xa, xb)
  +U = R.Rat.mul(M, rh)
  +pM = R.Rat.mul.den.pos(xa, xb, gx, hx)
  +pU = R.Rat.mul.den.pos(M, rh, pM, {==})
  +eA1 = Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(xa, nb), rh),
    R.Rat.mul(xa, R.Rat.mul(nb, rh)),
    R.Rat.mul_assoc.arb(xa, nb, rh, gx, R.Rat.neg.den.pos(xb, hx), {==}))
  +eM1 = R.Rat.mul_neg(xa, xb, gx, hx)
  +eM2 = R.Rat.neg_mul(M, rh, pM, {==})
  +eA2 = Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(xb, xa), rh),
    R.Rat.mul(xb, R.Rat.mul(xa, rh)),
    R.Rat.mul_assoc.arb(xb, xa, rh, hx, gx, {==}))
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.mul(nb, rh)),
              R.Rat.mul(xb, R.Rat.mul(xa, rh))),
    R.Rat.add(R.Rat.mul(R.Rat.mul(xa, nb), rh),
              R.Rat.mul(xb, R.Rat.mul(xa, rh))),
    R.Rat.zero(),
    Equal.cong(R.Rat, R.Rat,
      u => R.Rat.add(u, R.Rat.mul(xb, R.Rat.mul(xa, rh))),
      R.Rat.mul(xa, R.Rat.mul(nb, rh)), R.Rat.mul(R.Rat.mul(xa, nb), rh), eA1),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(R.Rat.mul(xa, nb), rh),
                R.Rat.mul(xb, R.Rat.mul(xa, rh))),
      R.Rat.add(R.Rat.mul(R.Rat.neg(M), rh), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
      R.Rat.zero(),
      Equal.cong(R.Rat, R.Rat,
        u => R.Rat.add(R.Rat.mul(u, rh), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
        R.Rat.mul(xa, nb), R.Rat.neg(M), eM1),
      Equal.trans(R.Rat,
        R.Rat.add(R.Rat.mul(R.Rat.neg(M), rh), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
        R.Rat.add(R.Rat.neg(U), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
        R.Rat.zero(),
        Equal.cong(R.Rat, R.Rat,
          u => R.Rat.add(u, R.Rat.mul(xb, R.Rat.mul(xa, rh))),
          R.Rat.mul(R.Rat.neg(M), rh), R.Rat.neg(U), eM2),
        Equal.trans(R.Rat,
          R.Rat.add(R.Rat.neg(U), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
          R.Rat.add(R.Rat.neg(U), R.Rat.mul(R.Rat.mul(xb, xa), rh)),
          R.Rat.zero(),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(U), u),
            R.Rat.mul(xb, R.Rat.mul(xa, rh)), R.Rat.mul(R.Rat.mul(xb, xa), rh), eA2),
          Equal.trans(R.Rat,
            R.Rat.add(R.Rat.neg(U), R.Rat.mul(R.Rat.mul(xb, xa), rh)),
            R.Rat.add(R.Rat.neg(U), U),
            R.Rat.zero(),
            Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(U), u),
              R.Rat.mul(R.Rat.mul(xb, xa), rh), U,
              Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(u, rh),
                R.Rat.mul(xb, xa), M, R.Rat.mul_comm(xb, xa))),
            Equal.trans(R.Rat,
              R.Rat.add(R.Rat.neg(U), U),
              R.Rat.add(U, R.Rat.neg(U)),
              R.Rat.zero(),
              R.Rat.add_comm(R.Rat.neg(U), U),
              R.Rat.add_neg(U, pU)))))))

def Q.QExt.inv.value.gt(d, x, gx, hx, ap, dp, hZ):
  match x:
    case Q.QExt{xa, xb}:
      +Z = R.Rat.of(1n+ap, 0n, dp)
      +Lr = R.Rat.add(R.Rat.mul(xa, R.Rat.div(xa, Z)),
                      R.Rat.mul(Q.QExt.nat(d),
                                R.Rat.mul(xb, R.Rat.div(R.Rat.neg(xb), Z))))
      +Li = R.Rat.add(R.Rat.mul(xa, R.Rat.div(R.Rat.neg(xb), Z)),
                      R.Rat.mul(xb, R.Rat.div(xa, Z)))
      Equal.trans(Q.QExt,
        Q.QExt{Lr, Li},
        Q.QExt{R.Rat.one(), Li},
        Q.QExt{R.Rat.one(), R.Rat.zero()},
        qext.re(Li, Lr, R.Rat.one(),
          QExt.inv.value.gt.re(d, xa, xb, gx, hx, ap, dp, hZ)),
        qext.im(R.Rat.one(), Li, R.Rat.zero(),
          QExt.inv.value.gt.im(d, xa, xb, gx, hx, ap, dp, hZ)))

# --- the LT twin ---
#
# QExt.inv.value.lt is the GT fill with the divisor's spelling swapped for round
# four's negative one and nothing else touched: every step in both coordinate
# chains is the same -- the same Rat.neg_mul, the same backwards
# Rat.mul_add_left.arb, the same congruence against hZ -- because the only thing
# the sign of the norm changes is which rational the reciprocal is written as.
# The reciprocal of Rat{Rat.num(0n, 1n+bp), 1n+dp} is Rat{Rat.num(0n, 1n+dp),
# 1n+bp} (round four measured that it is *not* the GT reciprocal with a
# coordinate flipped), and Rat.mul_inv.lt closes the same final product.

def QExt.inv.value.lt.re(+d: Nat, +xa: R.Rat, +xb: R.Rat,
                         +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                         +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                         +bp: Nat, +dp: Nat,
                         +hZ: {R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}
                               == Q.QExt.norm(d, Q.QExt{xa, xb}) : R.Rat})
  -> {R.Rat.add(R.Rat.mul(xa, R.Rat.mul(xa, R.Rat{R.Rat.num(0n, 1n+dp), 1n+bp})),
                 R.Rat.mul(Q.QExt.nat(d),
                   R.Rat.mul(xb, R.Rat.mul(R.Rat.neg(xb),
                                           R.Rat{R.Rat.num(0n, 1n+dp), 1n+bp}))))
      == R.Rat.one() : R.Rat}:
  +nb = R.Rat.neg(xb)
  +D = Q.QExt.nat(d)
  +rh = R.Rat.of(0n, 1n+dp, bp)
  +Z = R.Rat.of(0n, 1n+bp, dp)
  +AA = R.Rat.mul(xa, xa)
  +BB = R.Rat.mul(xb, xb)
  +PP = R.Rat.mul(D, BB)
  +pAA = R.Rat.mul.den.pos(xa, xa, gx, gx)
  +pBB = R.Rat.mul.den.pos(xb, xb, hx, hx)
  +pPP = R.Rat.mul.den.pos(D, BB, {==}, pBB)
  +pnegPP = R.Rat.neg.den.pos(PP, pPP)
  # xa*(xa*rh) = (xa*xa)*rh, and the inner b*(nb*rh) = (b*nb)*rh
  +eA1 = Equal.sym(R.Rat, R.Rat.mul(AA, rh), R.Rat.mul(xa, R.Rat.mul(xa, rh)),
    R.Rat.mul_assoc.arb(xa, xa, rh, gx, gx, {==}))
  +eA2 = Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(xb, nb), rh),
    R.Rat.mul(xb, R.Rat.mul(nb, rh)),
    R.Rat.mul_assoc.arb(xb, nb, rh, hx, R.Rat.neg.den.pos(xb, hx), {==}))
  # xb*nb = -(xb*xb), then d*(-(b*b)*rh) = -(d*(b*b))*rh
  +eM1 = R.Rat.mul_neg(xb, xb, hx, hx)
  +eM2 = Equal.trans(R.Rat,
    R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh)),
    R.Rat.mul(D, R.Rat.neg(R.Rat.mul(BB, rh))),
    R.Rat.mul(R.Rat.neg(PP), rh),
    Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(D, u),
      R.Rat.mul(R.Rat.neg(BB), rh), R.Rat.neg(R.Rat.mul(BB, rh)),
      R.Rat.neg_mul(BB, rh, pBB, {==})),
    Equal.trans(R.Rat,
      R.Rat.mul(D, R.Rat.neg(R.Rat.mul(BB, rh))),
      R.Rat.neg(R.Rat.mul(D, R.Rat.mul(BB, rh))),
      R.Rat.mul(R.Rat.neg(PP), rh),
      R.Rat.mul_neg(D, R.Rat.mul(BB, rh), {==}, R.Rat.mul.den.pos(BB, rh, pBB, {==})),
      Equal.trans(R.Rat,
        R.Rat.neg(R.Rat.mul(D, R.Rat.mul(BB, rh))),
        R.Rat.neg(R.Rat.mul(PP, rh)),
        R.Rat.mul(R.Rat.neg(PP), rh),
        Equal.cong(R.Rat, R.Rat, u => R.Rat.neg(u),
          R.Rat.mul(D, R.Rat.mul(BB, rh)), R.Rat.mul(PP, rh),
          Equal.sym(R.Rat, R.Rat.mul(PP, rh), R.Rat.mul(D, R.Rat.mul(BB, rh)),
            R.Rat.mul_assoc.arb(D, BB, rh, {==}, pBB, {==}))),
        Equal.sym(R.Rat, R.Rat.mul(R.Rat.neg(PP), rh), R.Rat.neg(R.Rat.mul(PP, rh)),
          R.Rat.neg_mul(PP, rh, pPP, {==})))))
  # (xa*xa)*rh + (-(b*b*d))*rh = (xa*xa - b*b*d)*rh, read backwards
  +eSum = Equal.sym(R.Rat,
    R.Rat.mul(R.Rat.add(AA, R.Rat.neg(PP)), rh),
    R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(R.Rat.neg(PP), rh)),
    R.Rat.mul_add_left.arb(AA, R.Rat.neg(PP), rh, pAA, pnegPP, {==}))
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.mul(xa, rh)),
              R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
    R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
    R.Rat.one(),
    Equal.cong(R.Rat, R.Rat,
      u => R.Rat.add(u, R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
      R.Rat.mul(xa, R.Rat.mul(xa, rh)), R.Rat.mul(AA, rh), eA1),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(xb, R.Rat.mul(nb, rh)))),
      R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.mul(xb, nb), rh))),
      R.Rat.one(),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, u)),
        R.Rat.mul(xb, R.Rat.mul(nb, rh)), R.Rat.mul(R.Rat.mul(xb, nb), rh), eA2),
      Equal.trans(R.Rat,
        R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.mul(xb, nb), rh))),
        R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh))),
        R.Rat.one(),
        Equal.cong(R.Rat, R.Rat,
          u => R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(u, rh))),
          R.Rat.mul(xb, nb), R.Rat.neg(BB), eM1),
        Equal.trans(R.Rat,
          R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh))),
          R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(R.Rat.neg(PP), rh)),
          R.Rat.one(),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mul(AA, rh), u),
            R.Rat.mul(D, R.Rat.mul(R.Rat.neg(BB), rh)), R.Rat.mul(R.Rat.neg(PP), rh),
            eM2),
          Equal.trans(R.Rat,
            R.Rat.add(R.Rat.mul(AA, rh), R.Rat.mul(R.Rat.neg(PP), rh)),
            R.Rat.mul(R.Rat.add(AA, R.Rat.neg(PP)), rh),
            R.Rat.one(),
            eSum,
            Equal.trans(R.Rat,
              R.Rat.mul(R.Rat.add(AA, R.Rat.neg(PP)), rh),
              R.Rat.mul(R.Rat.sub(AA, PP), rh),
              R.Rat.one(),
              {==},
              Equal.trans(R.Rat,
                R.Rat.mul(R.Rat.sub(AA, PP), rh),
                R.Rat.mul(Q.QExt.norm(d, Q.QExt{xa, xb}), rh),
                R.Rat.one(),
                {==},
                Equal.trans(R.Rat,
                  R.Rat.mul(Q.QExt.norm(d, Q.QExt{xa, xb}), rh),
                  R.Rat.mul(Z, rh),
                  R.Rat.one(),
                  Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(u, rh),
                    Q.QExt.norm(d, Q.QExt{xa, xb}), Z,
                    Equal.sym(R.Rat, Z, Q.QExt.norm(d, Q.QExt{xa, xb}), hZ)),
                  R.Rat.mul_inv.lt(0n, 1n+bp, dp, {==})))))))))

def QExt.inv.value.lt.im(+d: Nat, +xa: R.Rat, +xb: R.Rat,
                         +gx: {Nat.cmp(0n, R.Rat.denof(xa)) == LT{} : Cmp},
                         +hx: {Nat.cmp(0n, R.Rat.denof(xb)) == LT{} : Cmp},
                         +bp: Nat, +dp: Nat,
                         +hZ: {R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}
                               == Q.QExt.norm(d, Q.QExt{xa, xb}) : R.Rat})
  -> {R.Rat.add(R.Rat.mul(xa,
                   R.Rat.mul(R.Rat.neg(xb), R.Rat{R.Rat.num(0n, 1n+dp), 1n+bp})),
                 R.Rat.mul(xb, R.Rat.mul(xa, R.Rat{R.Rat.num(0n, 1n+dp), 1n+bp})))
      == R.Rat.zero() : R.Rat}:
  +nb = R.Rat.neg(xb)
  +rh = R.Rat.of(0n, 1n+dp, bp)
  +M = R.Rat.mul(xa, xb)
  +U = R.Rat.mul(M, rh)
  +pM = R.Rat.mul.den.pos(xa, xb, gx, hx)
  +pU = R.Rat.mul.den.pos(M, rh, pM, {==})
  +eA1 = Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(xa, nb), rh),
    R.Rat.mul(xa, R.Rat.mul(nb, rh)),
    R.Rat.mul_assoc.arb(xa, nb, rh, gx, R.Rat.neg.den.pos(xb, hx), {==}))
  +eM1 = R.Rat.mul_neg(xa, xb, gx, hx)
  +eM2 = R.Rat.neg_mul(M, rh, pM, {==})
  +eA2 = Equal.sym(R.Rat, R.Rat.mul(R.Rat.mul(xb, xa), rh),
    R.Rat.mul(xb, R.Rat.mul(xa, rh)),
    R.Rat.mul_assoc.arb(xb, xa, rh, hx, gx, {==}))
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.mul(xa, R.Rat.mul(nb, rh)),
              R.Rat.mul(xb, R.Rat.mul(xa, rh))),
    R.Rat.add(R.Rat.mul(R.Rat.mul(xa, nb), rh),
              R.Rat.mul(xb, R.Rat.mul(xa, rh))),
    R.Rat.zero(),
    Equal.cong(R.Rat, R.Rat,
      u => R.Rat.add(u, R.Rat.mul(xb, R.Rat.mul(xa, rh))),
      R.Rat.mul(xa, R.Rat.mul(nb, rh)), R.Rat.mul(R.Rat.mul(xa, nb), rh), eA1),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mul(R.Rat.mul(xa, nb), rh),
                R.Rat.mul(xb, R.Rat.mul(xa, rh))),
      R.Rat.add(R.Rat.mul(R.Rat.neg(M), rh), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
      R.Rat.zero(),
      Equal.cong(R.Rat, R.Rat,
        u => R.Rat.add(R.Rat.mul(u, rh), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
        R.Rat.mul(xa, nb), R.Rat.neg(M), eM1),
      Equal.trans(R.Rat,
        R.Rat.add(R.Rat.mul(R.Rat.neg(M), rh), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
        R.Rat.add(R.Rat.neg(U), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
        R.Rat.zero(),
        Equal.cong(R.Rat, R.Rat,
          u => R.Rat.add(u, R.Rat.mul(xb, R.Rat.mul(xa, rh))),
          R.Rat.mul(R.Rat.neg(M), rh), R.Rat.neg(U), eM2),
        Equal.trans(R.Rat,
          R.Rat.add(R.Rat.neg(U), R.Rat.mul(xb, R.Rat.mul(xa, rh))),
          R.Rat.add(R.Rat.neg(U), R.Rat.mul(R.Rat.mul(xb, xa), rh)),
          R.Rat.zero(),
          Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(U), u),
            R.Rat.mul(xb, R.Rat.mul(xa, rh)), R.Rat.mul(R.Rat.mul(xb, xa), rh), eA2),
          Equal.trans(R.Rat,
            R.Rat.add(R.Rat.neg(U), R.Rat.mul(R.Rat.mul(xb, xa), rh)),
            R.Rat.add(R.Rat.neg(U), U),
            R.Rat.zero(),
            Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.neg(U), u),
              R.Rat.mul(R.Rat.mul(xb, xa), rh), U,
              Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(u, rh),
                R.Rat.mul(xb, xa), M, R.Rat.mul_comm(xb, xa))),
            Equal.trans(R.Rat,
              R.Rat.add(R.Rat.neg(U), U),
              R.Rat.add(U, R.Rat.neg(U)),
              R.Rat.zero(),
              R.Rat.add_comm(R.Rat.neg(U), U),
              R.Rat.add_neg(U, pU)))))))

def Q.QExt.inv.value.lt(d, x, gx, hx, bp, dp, hZ):
  match x:
    case Q.QExt{xa, xb}:
      +Z = R.Rat.of(0n, 1n+bp, dp)
      +Lr = R.Rat.add(R.Rat.mul(xa, R.Rat.div(xa, Z)),
                      R.Rat.mul(Q.QExt.nat(d),
                                R.Rat.mul(xb, R.Rat.div(R.Rat.neg(xb), Z))))
      +Li = R.Rat.add(R.Rat.mul(xa, R.Rat.div(R.Rat.neg(xb), Z)),
                      R.Rat.mul(xb, R.Rat.div(xa, Z)))
      Equal.trans(Q.QExt,
        Q.QExt{Lr, Li},
        Q.QExt{R.Rat.one(), Li},
        Q.QExt{R.Rat.one(), R.Rat.zero()},
        qext.re(Li, Lr, R.Rat.one(),
          QExt.inv.value.lt.re(d, xa, xb, gx, hx, bp, dp, hZ)),
        qext.im(R.Rat.one(), Li, R.Rat.zero(),
          QExt.inv.value.lt.im(d, xa, xb, gx, hx, bp, dp, hZ)))

# --- the inverse as an operation ---
#
# QExt.mul_inv.gt / .lt are the operation-level form of the two payoff fills
# above, and each fill is one call: QExt.inv is a def whose body is verbatim the
# payoff's divisor expression, and R.Rat.of unfolds to the constructor the payoff
# spells, so the goal *is* the payoff's conclusion by conversion. Nothing is
# re-derived -- if these two ever fail while the value pair checks, the operation
# and the spelled relation have drifted apart, which is the one thing the pair
# exists to prevent.

def Q.QExt.mul_inv.gt(d, x, gx, hx, ap, dp, hZ):
  Q.QExt.inv.value.gt(d, x, gx, hx, ap, dp, hZ)

def Q.QExt.mul_inv.lt(d, x, gx, hx, bp, dp, hZ):
  Q.QExt.inv.value.lt(d, x, gx, hx, bp, dp, hZ)

# --- division ---
#
# qext.mul_add_left: (x + y)*z = x*z + y*z, the mirror QExt.mul_distrib does not
# state. Rat has the same pair (Rat.mul_distrib.arb / Rat.mul_add_left.arb) and
# rat.bend's comment on the latter records that the mirror is not proved
# separately either: QExt.mul_comm to turn the product around -- it is
# unconditional, which is why this mirror needs nothing the stated law does not
# -- then the stated law, then QExt.mul_comm under a cong on each summand.
#
# It is a helper rather than a law because it is not itself a fact about
# division: what QExt.div_add needs is exactly this, and the two branch fills
# below share it.
def qext.mul_add_left(+d: Nat, +x: Q.QExt, +y: Q.QExt, +z: Q.QExt,
                      +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                      +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                      +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                      +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp},
                      +gz: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(z))) == LT{} : Cmp},
                      +hz: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(z))) == LT{} : Cmp})
  -> {Q.QExt.mul(d, Q.QExt.add(x, y), z)
      == Q.QExt.add(Q.QExt.mul(d, x, z), Q.QExt.mul(d, y, z)) : Q.QExt}:
  Equal.trans(Q.QExt,
    Q.QExt.mul(d, Q.QExt.add(x, y), z),
    Q.QExt.mul(d, z, Q.QExt.add(x, y)),
    Q.QExt.add(Q.QExt.mul(d, x, z), Q.QExt.mul(d, y, z)),
    Q.QExt.mul_comm(d, Q.QExt.add(x, y), z),
    Equal.trans(Q.QExt,
      Q.QExt.mul(d, z, Q.QExt.add(x, y)),
      Q.QExt.add(Q.QExt.mul(d, z, x), Q.QExt.mul(d, z, y)),
      Q.QExt.add(Q.QExt.mul(d, x, z), Q.QExt.mul(d, y, z)),
      Q.QExt.mul_distrib(d, z, x, y, gz, hz, gx, hx, gy, hy),
      Equal.trans(Q.QExt,
        Q.QExt.add(Q.QExt.mul(d, z, x), Q.QExt.mul(d, z, y)),
        Q.QExt.add(Q.QExt.mul(d, x, z), Q.QExt.mul(d, z, y)),
        Q.QExt.add(Q.QExt.mul(d, x, z), Q.QExt.mul(d, y, z)),
        Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.add(u, Q.QExt.mul(d, z, y)),
          Q.QExt.mul(d, z, x), Q.QExt.mul(d, x, z), Q.QExt.mul_comm(d, z, x)),
        Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.add(Q.QExt.mul(d, x, z), u),
          Q.QExt.mul(d, z, y), Q.QExt.mul(d, y, z), Q.QExt.mul_comm(d, z, y)))))

# QExt.div_add.gt / .lt: the quotient of a sum, one law per sign of the divisor's
# spelling.
#
# The whole fill is qext.mul_add_left at the reciprocal, because the goal and the
# helper's conclusion are the same term once QExt.div unfolds: the quotient
# x/z *is* mul(d, x, QExt.inv(z, q)), by the definition and not by a law.
#
# The two positivity hypotheses the helper needs for its right factor -- the
# quotient's own coordinates -- are built here rather than asked for: the
# reciprocal of a spelled rational is a constructor, so its denominator is
# positive by computation ({==}), and Rat.mul.den.pos lifts z's positivity
# through the division. That is the one piece of work the branch adds, and it is
# the reason the law's hypothesis list is the same six QExt.mul_distrib takes
# while nothing about reciprocals appears in its statement.

def Q.QExt.div_add.gt(d, x, y, z, gx, hx, gy, hy, gz, hz, ap, dp):
  match z:
    case Q.QExt{za, zb}:
      +q = R.Rat.of(1n+ap, 0n, dp)
      +rp = R.Rat.of(1n+dp, 0n, ap)
      +i = Q.QExt.inv(Q.QExt{za, zb}, q)
      +gi = R.Rat.mul.den.pos(za, rp, gz, {==})
      +hi = R.Rat.mul.den.pos(R.Rat.neg(zb), rp, R.Rat.neg.den.pos(zb, hz), {==})
      qext.mul_add_left(d, x, y, i, gx, hx, gy, hy, gi, hi)

def Q.QExt.div_add.lt(d, x, y, z, gx, hx, gy, hy, gz, hz, bp, dp):
  match z:
    case Q.QExt{za, zb}:
      +q = R.Rat.of(0n, 1n+bp, dp)
      +rp = R.Rat.of(0n, 1n+dp, bp)
      +i = Q.QExt.inv(Q.QExt{za, zb}, q)
      +gi = R.Rat.mul.den.pos(za, rp, gz, {==})
      +hi = R.Rat.mul.den.pos(R.Rat.neg(zb), rp, R.Rat.neg.den.pos(zb, hz), {==})
      qext.mul_add_left(d, x, y, i, gx, hx, gy, hy, gi, hi)

# QExt.div_mul_cancel.gt / .lt: the field axiom (x/y)*y = x, one law per sign of
# the norm's spelling.
#
# Four steps, and the route is the one the shape of the laws dictates:
#
#   mul_assoc      (x*inv(y))*y   -> x*(inv(y)*y)     -- arbitrary values, so the
#                                                       law is QExt.mul_assoc
#   mul_comm       under a cong on the right factor    -- unconditional
#   mul_inv        inv(y)*y = 1                        -- the spelled norm, hZ
#   mul_one        x*1 = x                             -- x's spelled bridges
#
# The positivity the chain needs for its third value -- the reciprocal's own
# coordinates -- is built here rather than asked for, exactly as QExt.div_add's
# fill builds the quotient's: the reciprocal of a spelled rational is a
# constructor, so its denominator is positive by computation ({==}), and
# Rat.mul.den.pos lifts the dividend's positivity through the product. That is
# where the canonical presentation of x pays for itself: its own two positivity
# facts are {==} too, so the law's hypothesis list carries only y's.
#
# Note the two steps at the end are a mul_comm *then* a mul_inv: QExt.mul_inv
# states y*inv(y) = 1 and the associativity has left inv(y)*y in place, so the
# product has to be turned around before the inverse law applies.

def Q.QExt.div_mul_cancel.gt(d, np, nn, dp, mq, mn, dq, f1, f2, y, gy, hy, ap, ep, hZ):
  match y:
    case Q.QExt{ya, yb}:
      +X = Q.QExt.of(np, nn, dp, mq, mn, dq)
      +q = R.Rat.of(1n+ap, 0n, ep)
      +rp = R.Rat.of(1n+ep, 0n, ap)
      +i = Q.QExt.inv(y, q)
      +gi = R.Rat.mul.den.pos(ya, rp, gy, {==})
      +hi = R.Rat.mul.den.pos(R.Rat.neg(yb), rp, R.Rat.neg.den.pos(yb, hy), {==})
      +L1 = Q.QExt.mul(d, Q.QExt.mul(d, X, i), y)
      +L2 = Q.QExt.mul(d, X, Q.QExt.mul(d, i, y))
      +L3 = Q.QExt.mul(d, X, Q.QExt.mul(d, y, i))
      Equal.trans(Q.QExt,
        L1, L3, X,
        Equal.trans(Q.QExt, L1, L2, L3,
          Q.QExt.mul_assoc(d, X, i, y, {==}, {==}, gi, hi, gy, hy),
          Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.mul(d, X, u),
            Q.QExt.mul(d, i, y), Q.QExt.mul(d, y, i), Q.QExt.mul_comm(d, i, y))),
        Equal.trans(Q.QExt, L3, Q.QExt.mul(d, X, Q.QExt.one()), X,
          Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.mul(d, X, u),
            Q.QExt.mul(d, y, i), Q.QExt.one(),
            Q.QExt.mul_inv.gt(d, y, gy, hy, ap, ep, hZ)),
          Q.QExt.mul_one(d, np, nn, dp, mq, mn, dq, f1, f2)))

def Q.QExt.div_mul_cancel.lt(d, np, nn, dp, mq, mn, dq, f1, f2, y, gy, hy, bp, ep, hZ):
  match y:
    case Q.QExt{ya, yb}:
      +X = Q.QExt.of(np, nn, dp, mq, mn, dq)
      +q = R.Rat.of(0n, 1n+bp, ep)
      +rp = R.Rat.of(0n, 1n+ep, bp)
      +i = Q.QExt.inv(y, q)
      +gi = R.Rat.mul.den.pos(ya, rp, gy, {==})
      +hi = R.Rat.mul.den.pos(R.Rat.neg(yb), rp, R.Rat.neg.den.pos(yb, hy), {==})
      +L1 = Q.QExt.mul(d, Q.QExt.mul(d, X, i), y)
      +L2 = Q.QExt.mul(d, X, Q.QExt.mul(d, i, y))
      +L3 = Q.QExt.mul(d, X, Q.QExt.mul(d, y, i))
      Equal.trans(Q.QExt,
        L1, L3, X,
        Equal.trans(Q.QExt, L1, L2, L3,
          Q.QExt.mul_assoc(d, X, i, y, {==}, {==}, gi, hi, gy, hy),
          Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.mul(d, X, u),
            Q.QExt.mul(d, i, y), Q.QExt.mul(d, y, i), Q.QExt.mul_comm(d, i, y))),
        Equal.trans(Q.QExt, L3, Q.QExt.mul(d, X, Q.QExt.one()), X,
          Equal.cong(Q.QExt, Q.QExt, u => Q.QExt.mul(d, X, u),
            Q.QExt.mul(d, y, i), Q.QExt.one(),
            Q.QExt.mul_inv.lt(d, y, gy, hy, bp, ep, hZ)),
          Q.QExt.mul_one(d, np, nn, dp, mq, mn, dq, f1, f2)))
