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
