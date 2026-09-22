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

def N.nat.mag.sym(+p: Nat, +q: Nat)
  -> {R.Rat.mag(q, p) == R.Rat.mag(p, q) : Nat}:
  N.add_comm(Nat.sub(q, p), Nat.sub(p, q))

# The ported Rat block: rat_proofs.bend's fill for each law below, and the
# helpers it calls
# ==========================================================================
#
# Rat.add_assoc over the canonical presentation is rat_proofs.bend's fill,
# carried over name for name. The law keys are the R.* ones qrat_rat.bend
# declares; the helper defs live under Rat.h.*, which is a namespace no law key
# can collide with -- a helper whose name *is* a law key is read as that law's
# fill and then demands bare parameters, which is the trap the first spelling
# of this block walked into. The helpers also sit exactly where their first
# caller needs them, in the source block's own order, because the checker reads
# a def before the body that calls it.
#
# One difference from the source, forced by the checker: a helper's parameter
# list and return type must be annotated (only a law's fill may write bare
# names), so the helpers that are also laws take their telescope from rat.bend's
# statement of that law, and the computation-only ones carry the telescope
# rat_proofs.bend already writes for them.

def R.Rat.mk.scale.num(c, np, nn, dp, kp, e):
  match c:
    case GT{}:
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)), 0n,
        N.sub_of_lt(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp),
          Equal.trans(Cmp,
            Nat.cmp(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)), Nat.cmp(nn, np), LT{},
            N.cmp_mul_right(nn, np, kp),
            N.cmp_lt_of_gt(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e)))))
        : {Nat.div(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
                   N.Nat.gcd(Nat.add(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), _),
                     Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %N.mul_sub_right(np, nn, 1n+kp, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e))
        : {Nat.div(_, N.Nat.gcd(Nat.add(_, 0n), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        Nat.add(Nat.mul(Nat.sub(np, nn), 1n+kp), 0n),
        Nat.mul(Nat.sub(np, nn), 1n+kp),
        N.add_zero(Nat.mul(Nat.sub(np, nn), 1n+kp)))
        : {Nat.div(Nat.mul(Nat.sub(np, nn), 1n+kp),
                   N.Nat.gcd(_, Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.mul(Nat.sub(np, nn), 1n+kp), Nat.mul(1n+dp, 1n+kp)),
        Nat.mul(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+kp),
        N.gcd_scale(Nat.sub(np, nn), 1n+dp, kp))
        : {Nat.div(Nat.mul(Nat.sub(np, nn), 1n+kp), _)
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), 1n+dp),
        N.Nat.gcd(Nat.sub(np, nn), 1n+dp),
        Equal.cong(Nat, Nat, w => N.Nat.gcd(w, 1n+dp),
          Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), Nat.sub(np, nn),
          Equal.trans(Nat,
            Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)),
            Nat.add(Nat.sub(np, nn), 0n),
            Nat.sub(np, nn),
            Equal.cong(Nat, Nat, u => Nat.add(Nat.sub(np, nn), u),
              Nat.sub(nn, np), 0n,
              N.sub_of_lt(nn, np, N.cmp_lt_of_gt(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e)))),
            N.add_zero(Nat.sub(np, nn)))))
        : {Nat.div(Nat.mul(Nat.sub(np, nn), 1n+kp),
                   Nat.mul(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+kp))
            == Nat.div(Nat.sub(np, nn), _) : Nat}
      N.div_scale(Nat.sub(np, nn), N.Nat.gcd(Nat.sub(np, nn), 1n+dp), kp,
        Pair.fst(N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), Nat.sub(np, nn)),
          N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+dp),
          N.gcd_divides(Nat.sub(np, nn), 1n+dp)),
        N.divides_pos_wit(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), Nat.sub(np, nn),
          Pair.fst(N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), Nat.sub(np, nn)),
            N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+dp),
            N.gcd_divides(Nat.sub(np, nn), 1n+dp)),
          Equal.trans(Cmp,
            Nat.cmp(0n, Nat.sub(np, nn)),
            Nat.cmp(0n, 1n+Nat.sub(np, 1n+nn)),
            LT{},
            Equal.cong(Nat, Cmp, u => Nat.cmp(0n, u),
              Nat.sub(np, nn), 1n+Nat.sub(np, 1n+nn),
              N.sub_pos(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e))),
            {==})))
    case EQ{}:
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), 0n,
        Equal.trans(Nat,
          Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
          Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(np, 1n+kp)),
          0n,
          Equal.cong(Nat, Nat, u => Nat.sub(Nat.mul(np, 1n+kp), u),
            Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp),
            Equal.sym(Nat, Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp),
              Equal.cong(Nat, Nat, u => Nat.mul(u, 1n+kp), np, nn,
                N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e))))),
          N.sub_self(Nat.mul(np, 1n+kp))))
        : {Nat.div(_, N.Nat.gcd(Nat.add(_, Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp))), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)), 0n,
        Equal.trans(Nat,
          Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
          Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(nn, 1n+kp)),
          0n,
          Equal.cong(Nat, Nat, u => Nat.sub(Nat.mul(nn, 1n+kp), u),
            Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp),
            Equal.cong(Nat, Nat, u => Nat.mul(u, 1n+kp), np, nn,
              N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e)))),
          N.sub_self(Nat.mul(nn, 1n+kp))))
        : {Nat.div(0n, N.Nat.gcd(Nat.add(0n, _), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat, Nat.sub(np, nn), 0n,
        Equal.trans(Nat, Nat.sub(np, nn), Nat.sub(np, np), 0n,
          Equal.cong(Nat, Nat, u => Nat.sub(np, u), nn, np,
            Equal.sym(Nat, np, nn, N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e)))),
          N.sub_self(np)))
        : {Nat.div(0n, Nat.mul(1n+dp, 1n+kp))
            == Nat.div(_, N.Nat.gcd(Nat.add(_, Nat.sub(nn, np)), 1n+dp)) : Nat}
      %Equal.sym(Nat, Nat.sub(nn, np), 0n,
        Equal.trans(Nat, Nat.sub(nn, np), Nat.sub(nn, nn), 0n,
          Equal.cong(Nat, Nat, u => Nat.sub(nn, u), np, nn,
            N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e))),
          N.sub_self(nn)))
        : {Nat.div(0n, Nat.mul(1n+dp, 1n+kp))
            == Nat.div(0n, N.Nat.gcd(Nat.add(0n, _), 1n+dp)) : Nat}
      {==}
    case LT{}:
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), 0n,
        N.sub_of_lt(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp),
          Equal.trans(Cmp,
            Nat.cmp(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), Nat.cmp(np, nn), LT{},
            N.cmp_mul_right(np, nn, kp),
            Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e))))
        : {Nat.div(_, N.Nat.gcd(Nat.add(_, Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp))), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %N.mul_sub_right(nn, np, 1n+kp, N.cmp_gt_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e)))
        : {Nat.div(0n, N.Nat.gcd(Nat.add(0n, _), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.mul(Nat.sub(nn, np), 1n+kp), Nat.mul(1n+dp, 1n+kp)),
        Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp),
        N.gcd_scale(Nat.sub(nn, np), 1n+dp, kp))
        : {Nat.div(0n, _) == Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), 1n+dp),
        N.Nat.gcd(Nat.sub(nn, np), 1n+dp),
        Equal.cong(Nat, Nat, w => N.Nat.gcd(w, 1n+dp),
          Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), Nat.sub(nn, np),
          Equal.trans(Nat,
            Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)),
            Nat.add(0n, Nat.sub(nn, np)),
            Nat.sub(nn, np),
            Equal.cong(Nat, Nat, u => Nat.add(u, Nat.sub(nn, np)),
              Nat.sub(np, nn), 0n,
              N.sub_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e))),
            {==})))
        : {Nat.div(0n, Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp))
            == Nat.div(Nat.sub(np, nn), _) : Nat}
      %Equal.sym(Nat, Nat.sub(np, nn), 0n,
        N.sub_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e)))
        : {Nat.div(0n, Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp))
            == Nat.div(_, N.Nat.gcd(Nat.sub(nn, np), 1n+dp)) : Nat}
      %Equal.sym(Nat, Nat.div(0n, N.Nat.gcd(Nat.sub(nn, np), 1n+dp)), 0n,
        N.div_zero(N.Nat.gcd(Nat.sub(nn, np), 1n+dp)))
        : {Nat.div(0n, Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp)) == _ : Nat}
      %Equal.sym(Nat, Nat.div(0n, Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp)), 0n,
        N.div_zero(Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp)))
        : {_ == 0n : Nat}
      {==}

def R.Rat.mk.scale.neg(c, np, nn, dp, kp, e):
  %Equal.sym(Nat,
    Nat.add(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
            Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp))),
    Nat.add(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
            Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp))),
    N.add_comm(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
      Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp))))
    : {Nat.div(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
               N.Nat.gcd(_, Nat.mul(1n+dp, 1n+kp)))
        == Nat.div(Nat.sub(nn, np), R.Rat.g(np, nn, 1n+dp)) : Nat}
  %Equal.sym(Nat,
    Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)),
    Nat.add(Nat.sub(nn, np), Nat.sub(np, nn)),
    N.add_comm(Nat.sub(np, nn), Nat.sub(nn, np)))
    : {Nat.div(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
               N.Nat.gcd(Nat.add(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
                                 Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp))),
                 Nat.mul(1n+dp, 1n+kp)))
        == Nat.div(Nat.sub(nn, np), N.Nat.gcd(_, 1n+dp)) : Nat}
  R.Rat.mk.scale.num(N.Cmp.flip(c), nn, np, dp, kp,
    Equal.trans(Cmp, N.Cmp.flip(c), N.Cmp.flip(Nat.cmp(np, nn)), Nat.cmp(nn, np),
      Equal.cong(Cmp, Cmp, N.Cmp.flip, c, Nat.cmp(np, nn), e),
      Equal.trans(Cmp, N.Cmp.flip(Nat.cmp(np, nn)), N.Cmp.flip(N.Cmp.flip(Nat.cmp(nn, np))), Nat.cmp(nn, np),
        Equal.cong(Cmp, Cmp, N.Cmp.flip, Nat.cmp(np, nn), N.Cmp.flip(Nat.cmp(nn, np)), N.cmp_antisym(np, nn)),
        N.flip_flip(Nat.cmp(nn, np)))))

def R.Rat.mk.scale.den(c, np, nn, dp, kp, e):
  match c:
    case GT{}:
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)), 0n,
        N.sub_of_lt(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp),
          Equal.trans(Cmp,
            Nat.cmp(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)), Nat.cmp(nn, np), LT{},
            N.cmp_mul_right(nn, np, kp),
            N.cmp_lt_of_gt(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e)))))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp),
                   N.Nat.gcd(Nat.add(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), _),
                     Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %N.mul_sub_right(np, nn, 1n+kp, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp),
                   N.Nat.gcd(Nat.add(_, 0n), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        Nat.add(Nat.mul(Nat.sub(np, nn), 1n+kp), 0n),
        Nat.mul(Nat.sub(np, nn), 1n+kp),
        N.add_zero(Nat.mul(Nat.sub(np, nn), 1n+kp)))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp),
                   N.Nat.gcd(_, Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.mul(Nat.sub(np, nn), 1n+kp), Nat.mul(1n+dp, 1n+kp)),
        Nat.mul(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+kp),
        N.gcd_scale(Nat.sub(np, nn), 1n+dp, kp))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), _)
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), 1n+dp),
        N.Nat.gcd(Nat.sub(np, nn), 1n+dp),
        Equal.cong(Nat, Nat, w => N.Nat.gcd(w, 1n+dp),
          Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), Nat.sub(np, nn),
          Equal.trans(Nat,
            Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)),
            Nat.add(Nat.sub(np, nn), 0n),
            Nat.sub(np, nn),
            Equal.cong(Nat, Nat, u => Nat.add(Nat.sub(np, nn), u),
              Nat.sub(nn, np), 0n,
              N.sub_of_lt(nn, np, N.cmp_lt_of_gt(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e)))),
            N.add_zero(Nat.sub(np, nn)))))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp),
                   Nat.mul(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+kp))
            == Nat.div(1n+dp, _) : Nat}
      N.div_scale(1n+dp, N.Nat.gcd(Nat.sub(np, nn), 1n+dp), kp,
        Pair.snd(N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), Nat.sub(np, nn)),
          N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+dp),
          N.gcd_divides(Nat.sub(np, nn), 1n+dp)),
        N.divides_pos_wit(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), Nat.sub(np, nn),
          Pair.fst(N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), Nat.sub(np, nn)),
            N.Nat.divides(N.Nat.gcd(Nat.sub(np, nn), 1n+dp), 1n+dp),
            N.gcd_divides(Nat.sub(np, nn), 1n+dp)),
          Equal.trans(Cmp,
            Nat.cmp(0n, Nat.sub(np, nn)),
            Nat.cmp(0n, 1n+Nat.sub(np, 1n+nn)),
            LT{},
            Equal.cong(Nat, Cmp, u => Nat.cmp(0n, u),
              Nat.sub(np, nn), 1n+Nat.sub(np, 1n+nn),
              N.sub_pos(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e))),
            {==})))
    case EQ{}:
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), 0n,
        Equal.trans(Nat,
          Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
          Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(np, 1n+kp)),
          0n,
          Equal.cong(Nat, Nat, u => Nat.sub(Nat.mul(np, 1n+kp), u),
            Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp),
            Equal.sym(Nat, Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp),
              Equal.cong(Nat, Nat, u => Nat.mul(u, 1n+kp), np, nn,
                N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e))))),
          N.sub_self(Nat.mul(np, 1n+kp))))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp),
                   N.Nat.gcd(Nat.add(_, Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp))),
                     Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)), 0n,
        Equal.trans(Nat,
          Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
          Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(nn, 1n+kp)),
          0n,
          Equal.cong(Nat, Nat, u => Nat.sub(Nat.mul(nn, 1n+kp), u),
            Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp),
            Equal.cong(Nat, Nat, u => Nat.mul(u, 1n+kp), np, nn,
              N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e)))),
          N.sub_self(Nat.mul(nn, 1n+kp))))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), N.Nat.gcd(Nat.add(0n, _), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat, Nat.sub(np, nn), 0n,
        Equal.trans(Nat, Nat.sub(np, nn), Nat.sub(np, np), 0n,
          Equal.cong(Nat, Nat, u => Nat.sub(np, u), nn, np,
            Equal.sym(Nat, np, nn, N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e)))),
          N.sub_self(np)))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), Nat.mul(1n+dp, 1n+kp))
            == Nat.div(1n+dp, N.Nat.gcd(Nat.add(_, Nat.sub(nn, np)), 1n+dp)) : Nat}
      %Equal.sym(Nat, Nat.sub(nn, np), 0n,
        Equal.trans(Nat, Nat.sub(nn, np), Nat.sub(nn, nn), 0n,
          Equal.cong(Nat, Nat, u => Nat.sub(nn, u), np, nn,
            N.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e))),
          N.sub_self(nn)))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), Nat.mul(1n+dp, 1n+kp))
            == Nat.div(1n+dp, N.Nat.gcd(Nat.add(0n, _), 1n+dp)) : Nat}
      %Equal.sym(Nat,
        Nat.div(1n+dp, 1n+dp), 1n,
        N.div_self(dp))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), Nat.mul(1n+dp, 1n+kp)) == _ : Nat}
      %Equal.sym(Nat,
        Nat.div(Nat.mul(1n+dp, 1n+kp), Nat.mul(1n+dp, 1n+kp)),
        1n,
        N.div_self(Nat.add(kp, Nat.mul(dp, 1n+kp))))
        : {_ == 1n : Nat}
      {==}
    case LT{}:
      %Equal.sym(Nat,
        Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), 0n,
        N.sub_of_lt(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp),
          Equal.trans(Cmp,
            Nat.cmp(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)), Nat.cmp(np, nn), LT{},
            N.cmp_mul_right(np, nn, kp),
            Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e))))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp),
                   N.Nat.gcd(Nat.add(_, Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp))),
                     Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %N.mul_sub_right(nn, np, 1n+kp, N.cmp_gt_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e)))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), N.Nat.gcd(Nat.add(0n, _), Nat.mul(1n+dp, 1n+kp)))
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.mul(Nat.sub(nn, np), 1n+kp), Nat.mul(1n+dp, 1n+kp)),
        Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp),
        N.gcd_scale(Nat.sub(nn, np), 1n+dp, kp))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), _)
            == Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)) : Nat}
      %Equal.sym(Nat,
        N.Nat.gcd(Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), 1n+dp),
        N.Nat.gcd(Nat.sub(nn, np), 1n+dp),
        Equal.cong(Nat, Nat, w => N.Nat.gcd(w, 1n+dp),
          Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)), Nat.sub(nn, np),
          Equal.trans(Nat,
            Nat.add(Nat.sub(np, nn), Nat.sub(nn, np)),
            Nat.add(0n, Nat.sub(nn, np)),
            Nat.sub(nn, np),
            Equal.cong(Nat, Nat, u => Nat.add(u, Nat.sub(nn, np)),
              Nat.sub(np, nn), 0n,
              N.sub_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e))),
            {==})))
        : {Nat.div(Nat.mul(1n+dp, 1n+kp), Nat.mul(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+kp))
            == Nat.div(1n+dp, _) : Nat}
      N.div_scale(1n+dp, N.Nat.gcd(Nat.sub(nn, np), 1n+dp), kp,
        Pair.snd(N.Nat.divides(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), Nat.sub(nn, np)),
          N.Nat.divides(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+dp),
          N.gcd_divides(Nat.sub(nn, np), 1n+dp)),
        N.divides_pos_wit(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), Nat.sub(nn, np),
          Pair.fst(N.Nat.divides(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), Nat.sub(nn, np)),
            N.Nat.divides(N.Nat.gcd(Nat.sub(nn, np), 1n+dp), 1n+dp),
            N.gcd_divides(Nat.sub(nn, np), 1n+dp)),
          Equal.trans(Cmp,
            Nat.cmp(0n, Nat.sub(nn, np)),
            Nat.cmp(0n, 1n+Nat.sub(nn, 1n+np)),
            LT{},
            Equal.cong(Nat, Cmp, u => Nat.cmp(0n, u),
              Nat.sub(nn, np), 1n+Nat.sub(nn, 1n+np),
              N.sub_pos(nn, np, N.cmp_gt_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e)))),
            {==})))

def R.Rat.mk.scale.go(c, np, nn, dp, kp, e):
  %Equal.sym(Nat,
    Nat.div(Nat.sub(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp)),
      R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp))),
    Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)),
    R.Rat.mk.scale.num(c, np, nn, dp, kp, e))
    : {R.Rat{I.Int{_, Nat.div(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
                             R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))},
              Nat.div(Nat.mul(1n+dp, 1n+kp),
                R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))}
        == R.Rat.mk.go(np, nn, 1n+dp) : R.Rat}
  %Equal.sym(Nat,
    Nat.div(Nat.sub(Nat.mul(nn, 1n+kp), Nat.mul(np, 1n+kp)),
      R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp))),
    Nat.div(Nat.sub(nn, np), R.Rat.g(np, nn, 1n+dp)),
    R.Rat.mk.scale.neg(c, np, nn, dp, kp, e))
    : {R.Rat{I.Int{Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)), _},
              Nat.div(Nat.mul(1n+dp, 1n+kp),
                R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)))}
        == R.Rat.mk.go(np, nn, 1n+dp) : R.Rat}
  %Equal.sym(Nat,
    Nat.div(Nat.mul(1n+dp, 1n+kp),
      R.Rat.g(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp))),
    Nat.div(1n+dp, R.Rat.g(np, nn, 1n+dp)),
    R.Rat.mk.scale.den(c, np, nn, dp, kp, e))
    : {R.Rat{I.Int{Nat.div(Nat.sub(np, nn), R.Rat.g(np, nn, 1n+dp)),
                   Nat.div(Nat.sub(nn, np), R.Rat.g(np, nn, 1n+dp))}, _}
        == R.Rat.mk.go(np, nn, 1n+dp) : R.Rat}
  {==}

def R.Rat.mk.scale(n, dp, kp):
  match n:
    case I.Int{np, nn}:
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.mul(I.Int{np, nn}, I.Int{1n+kp, 0n}), Nat.mul(1n+dp, 1n+kp)),
        R.Rat.mk.go(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)),
        R.Rat.mk(I.Int{np, nn}, 1n+dp),
        Equal.trans(R.Rat,
          R.Rat.mk(I.Int.mul(I.Int{np, nn}, I.Int{1n+kp, 0n}), Nat.mul(1n+dp, 1n+kp)),
          R.Rat.mk.go(Nat.add(Nat.mul(np, 1n+kp), Nat.mul(nn, 0n)),
            Nat.add(Nat.mul(np, 0n), Nat.mul(nn, 1n+kp)), Nat.mul(1n+dp, 1n+kp)),
          R.Rat.mk.go(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)),
          {==},
          Equal.trans(R.Rat,
            R.Rat.mk.go(Nat.add(Nat.mul(np, 1n+kp), Nat.mul(nn, 0n)),
              Nat.add(Nat.mul(np, 0n), Nat.mul(nn, 1n+kp)), Nat.mul(1n+dp, 1n+kp)),
            R.Rat.mk.go(Nat.mul(np, 1n+kp), Nat.add(Nat.mul(np, 0n), Nat.mul(nn, 1n+kp)),
              Nat.mul(1n+dp, 1n+kp)),
            R.Rat.mk.go(Nat.mul(np, 1n+kp), Nat.mul(nn, 1n+kp), Nat.mul(1n+dp, 1n+kp)),
            Equal.cong(Nat, R.Rat,
              u => R.Rat.mk.go(u, Nat.add(Nat.mul(np, 0n), Nat.mul(nn, 1n+kp)), Nat.mul(1n+dp, 1n+kp)),
              Nat.add(Nat.mul(np, 1n+kp), Nat.mul(nn, 0n)), Nat.mul(np, 1n+kp),
              Equal.trans(Nat,
                Nat.add(Nat.mul(np, 1n+kp), Nat.mul(nn, 0n)),
                Nat.add(Nat.mul(np, 1n+kp), 0n),
                Nat.mul(np, 1n+kp),
                Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(np, 1n+kp), u),
                  Nat.mul(nn, 0n), 0n, N.mul_zero(nn)),
                N.add_zero(Nat.mul(np, 1n+kp)))),
            Equal.cong(Nat, R.Rat,
              u => R.Rat.mk.go(Nat.mul(np, 1n+kp), u, Nat.mul(1n+dp, 1n+kp)),
              Nat.add(Nat.mul(np, 0n), Nat.mul(nn, 1n+kp)), Nat.mul(nn, 1n+kp),
              Equal.cong(Nat, Nat, u => Nat.add(u, Nat.mul(nn, 1n+kp)),
                Nat.mul(np, 0n), 0n, N.mul_zero(np))))),
        R.Rat.mk.scale.go(Nat.cmp(np, nn), np, nn, dp, kp, {==}))

def R.Rat.mk.eqv(n1, dp1, n2, dp2, e):
  Equal.trans(R.Rat,
    R.Rat.mk(n1, 1n+dp1),
    R.Rat.mk(I.Int.mul(n1, I.Int{1n+dp2, 0n}), Nat.mul(1n+dp1, 1n+dp2)),
    R.Rat.mk(n2, 1n+dp2),
    Equal.sym(R.Rat,
      R.Rat.mk(I.Int.mul(n1, I.Int{1n+dp2, 0n}), Nat.mul(1n+dp1, 1n+dp2)),
      R.Rat.mk(n1, 1n+dp1),
      R.Rat.mk.scale(n1, dp1, dp2)),
    Equal.trans(R.Rat,
      R.Rat.mk(I.Int.mul(n1, I.Int{1n+dp2, 0n}), Nat.mul(1n+dp1, 1n+dp2)),
      R.Rat.mk(I.Int.mul(n2, I.Int{1n+dp1, 0n}), Nat.mul(1n+dp1, 1n+dp2)),
      R.Rat.mk(n2, 1n+dp2),
      Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(1n+dp1, 1n+dp2)),
        I.Int.mul(n1, I.Int{1n+dp2, 0n}), I.Int.mul(n2, I.Int{1n+dp1, 0n}), e),
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.mul(n2, I.Int{1n+dp1, 0n}), Nat.mul(1n+dp1, 1n+dp2)),
        R.Rat.mk(I.Int.mul(n2, I.Int{1n+dp1, 0n}), Nat.mul(1n+dp2, 1n+dp1)),
        R.Rat.mk(n2, 1n+dp2),
        Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int.mul(n2, I.Int{1n+dp1, 0n}), u),
          Nat.mul(1n+dp1, 1n+dp2), Nat.mul(1n+dp2, 1n+dp1), N.mul_comm(1n+dp1, 1n+dp2)),
        R.Rat.mk.scale(n2, dp2, dp1))))

def R.Rat.mk.eqv.raw(n1, d1, n2, d2, p1, p2, e):
  +a1 = Nat.sub(d1, 1n)
  +a2 = Nat.sub(d2, 1n)
  Equal.trans(R.Rat,
    R.Rat.mk(n1, d1),
    R.Rat.mk(n1, 1n+a1),
    R.Rat.mk(n2, d2),
    Equal.cong(Nat, R.Rat, w => R.Rat.mk(n1, w), d1, 1n+a1, N.pos_witness(d1, p1)),
    Equal.trans(R.Rat,
      R.Rat.mk(n1, 1n+a1),
      R.Rat.mk(n2, 1n+a2),
      R.Rat.mk(n2, d2),
      R.Rat.mk.eqv(n1, a1, n2, a2,
        Equal.trans(I.Int,
          I.Int.mul(n1, I.Int{1n+a2, 0n}),
          I.Int.mul(n1, I.Int{d2, 0n}),
          I.Int.mul(n2, I.Int{1n+a1, 0n}),
          Equal.cong(I.Int, I.Int, w => I.Int.mul(n1, w), I.Int{1n+a2, 0n}, I.Int{d2, 0n},
            Equal.cong(Nat, I.Int, w => I.Int{w, 0n}, 1n+a2, d2,
              Equal.sym(Nat, d2, 1n+a2, N.pos_witness(d2, p2)))),
          Equal.trans(I.Int,
            I.Int.mul(n1, I.Int{d2, 0n}),
            I.Int.mul(n2, I.Int{d1, 0n}),
            I.Int.mul(n2, I.Int{1n+a1, 0n}),
            e,
            Equal.cong(I.Int, I.Int, w => I.Int.mul(n2, w), I.Int{d1, 0n}, I.Int{1n+a1, 0n},
              Equal.cong(Nat, I.Int, w => I.Int{w, 0n}, d1, 1n+a1, N.pos_witness(d1, p1)))))),
      Equal.cong(Nat, R.Rat, w => R.Rat.mk(n2, w), 1n+a2, d2,
        Equal.sym(Nat, d2, 1n+a2, N.pos_witness(d2, p2)))))

def R.Rat.mk.value.go(c, np, nn, d, e, pd, wm, wd):
  match c:
    case GT{}:
      N.Div{mq, mwe} = wm
      N.Div{dr, dwe} = wd
      +G = R.Rat.g(np, nn, d)
      +P = Nat.sub(np, nn)
      +Q = Nat.sub(nn, np)
      +A = Nat.div(P, G)
      +B = Nat.div(Q, G)
      +Rr = Nat.div(d, G)
      +M = R.Rat.mag(np, nn)
      +pg = N.divides_pos_wit(G, d, N.Div{dr, dwe}, pd)
      +gte = Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e)
      +qe = N.sub_of_lt(nn, np, N.cmp_lt_of_gt(np, nn, gte))
      +mm = Equal.trans(Nat, M, Nat.add(P, 0n), P,
        Equal.cong(Nat, Nat, u => Nat.add(P, u), Q, 0n, qe), N.add_zero(P))
      +e1 = Equal.trans(Nat, P, M, Nat.mul(G, mq), Equal.sym(Nat, M, P, mm), mwe)
      +e1z = Equal.trans(Nat, Q, 0n, Nat.mul(G, 0n), qe,
        Equal.sym(Nat, Nat.mul(G, 0n), 0n, N.mul_zero(G)))
      Equal.trans(I.Int,
        I.Int{Nat.mul(A, d), Nat.mul(B, d)},
        I.Int{Nat.mul(P, Rr), Nat.mul(B, d)},
        I.Int{Nat.mul(P, Rr), Nat.mul(Q, Rr)},
        Equal.cong(Nat, I.Int, u => I.Int{u, Nat.mul(B, d)}, Nat.mul(A, d), Nat.mul(P, Rr),
          N.div_cross(P, G, mq, d, dr, pg, e1, dwe)),
        Equal.cong(Nat, I.Int, u => I.Int{Nat.mul(P, Rr), u}, Nat.mul(B, d), Nat.mul(Q, Rr),
          N.div_cross(Q, G, 0n, d, dr, pg, e1z, dwe)))
    case LT{}:
      N.Div{mq, mwe} = wm
      N.Div{dr, dwe} = wd
      +G = R.Rat.g(np, nn, d)
      +P = Nat.sub(np, nn)
      +Q = Nat.sub(nn, np)
      +A = Nat.div(P, G)
      +B = Nat.div(Q, G)
      +Rr = Nat.div(d, G)
      +M = R.Rat.mag(np, nn)
      +pg = N.divides_pos_wit(G, d, N.Div{dr, dwe}, pd)
      +lte = Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e)
      +pe = N.sub_of_lt(np, nn, lte)
      +mm = Equal.cong(Nat, Nat, u => Nat.add(u, Q), P, 0n, pe)
      +e1 = Equal.trans(Nat, Q, M, Nat.mul(G, mq), Equal.sym(Nat, M, Q, mm), mwe)
      +e1z = Equal.trans(Nat, P, 0n, Nat.mul(G, 0n), pe,
        Equal.sym(Nat, Nat.mul(G, 0n), 0n, N.mul_zero(G)))
      Equal.trans(I.Int,
        I.Int{Nat.mul(A, d), Nat.mul(B, d)},
        I.Int{Nat.mul(P, Rr), Nat.mul(B, d)},
        I.Int{Nat.mul(P, Rr), Nat.mul(Q, Rr)},
        Equal.cong(Nat, I.Int, u => I.Int{u, Nat.mul(B, d)}, Nat.mul(A, d), Nat.mul(P, Rr),
          N.div_cross(P, G, 0n, d, dr, pg, e1z, dwe)),
        Equal.cong(Nat, I.Int, u => I.Int{Nat.mul(P, Rr), u}, Nat.mul(B, d), Nat.mul(Q, Rr),
          N.div_cross(Q, G, mq, d, dr, pg, e1, dwe)))
    case EQ{}:
      N.Div{dr, dwe} = wd
      +G = R.Rat.g(np, nn, d)
      +P = Nat.sub(np, nn)
      +Q = Nat.sub(nn, np)
      +A = Nat.div(P, G)
      +B = Nat.div(Q, G)
      +Rr = Nat.div(d, G)
      +pg = N.divides_pos_wit(G, d, N.Div{dr, dwe}, pd)
      +eqe = Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e)
      +pe = Equal.trans(Nat, P, Nat.sub(np, np), 0n,
        Equal.cong(Nat, Nat, u => Nat.sub(np, u), nn, np,
          Equal.sym(Nat, np, nn, N.cmp_eq(np, nn, eqe))),
        N.sub_self(np))
      +qe = Equal.trans(Nat, Q, Nat.sub(nn, nn), 0n,
        Equal.cong(Nat, Nat, u => Nat.sub(nn, u), np, nn, N.cmp_eq(np, nn, eqe)),
        N.sub_self(nn))
      +e1 = Equal.trans(Nat, P, 0n, Nat.mul(G, 0n), pe,
        Equal.sym(Nat, Nat.mul(G, 0n), 0n, N.mul_zero(G)))
      +e1z = Equal.trans(Nat, Q, 0n, Nat.mul(G, 0n), qe,
        Equal.sym(Nat, Nat.mul(G, 0n), 0n, N.mul_zero(G)))
      Equal.trans(I.Int,
        I.Int{Nat.mul(A, d), Nat.mul(B, d)},
        I.Int{Nat.mul(P, Rr), Nat.mul(B, d)},
        I.Int{Nat.mul(P, Rr), Nat.mul(Q, Rr)},
        Equal.cong(Nat, I.Int, u => I.Int{u, Nat.mul(B, d)}, Nat.mul(A, d), Nat.mul(P, Rr),
          N.div_cross(P, G, 0n, d, dr, pg, e1, dwe)),
        Equal.cong(Nat, I.Int, u => I.Int{Nat.mul(P, Rr), u}, Nat.mul(B, d), Nat.mul(Q, Rr),
          N.div_cross(Q, G, 0n, d, dr, pg, e1z, dwe)))

def R.Rat.mk.value(c, np, nn, d, e, pd):
  +G = R.Rat.g(np, nn, d)
  +P = Nat.sub(np, nn)
  +Q = Nat.sub(nn, np)
  +A = Nat.div(P, G)
  +B = Nat.div(Q, G)
  +Rr = Nat.div(d, G)
  +M = R.Rat.mag(np, nn)
  Equal.trans(I.Int,
    I.Int.mul(R.Rat.numof(R.Rat.mk(I.Int{np, nn}, d)), I.Int{d, 0n}),
    I.Int{Nat.mul(A, d), Nat.mul(B, d)},
    I.Int.mul(R.Rat.num(np, nn), I.Int{R.Rat.denof(R.Rat.mk(I.Int{np, nn}, d)), 0n}),
    I.Int.mul_scale(A, B, d),
    Equal.trans(I.Int,
      I.Int{Nat.mul(A, d), Nat.mul(B, d)},
      I.Int{Nat.mul(P, Rr), Nat.mul(Q, Rr)},
      I.Int.mul(R.Rat.num(np, nn), I.Int{R.Rat.denof(R.Rat.mk(I.Int{np, nn}, d)), 0n}),
      R.Rat.mk.value.go(c, np, nn, d, e, pd,
        Pair.fst(N.Nat.divides(G, M), N.Nat.divides(G, d), N.gcd_divides(M, d)),
        Pair.snd(N.Nat.divides(G, M), N.Nat.divides(G, d), N.gcd_divides(M, d))),
      Equal.sym(I.Int,
        I.Int.mul(R.Rat.num(np, nn), I.Int{R.Rat.denof(R.Rat.mk(I.Int{np, nn}, d)), 0n}),
        I.Int{Nat.mul(P, Rr), Nat.mul(Q, Rr)},
        I.Int.mul_scale(P, Q, Rr))))

def R.Rat.mk.rep(U, V, d):
  +P = Nat.sub(U, V)
  +Q = Nat.sub(V, U)
  +G1 = R.Rat.g(P, Q, d)
  +G2 = R.Rat.g(U, V, d)
  +A = Nat.div(Nat.sub(P, Q), G1)
  +B = Nat.div(Nat.sub(Q, P), G1)
  +Rr = Nat.div(d, G1)
  +A2 = Nat.div(P, G2)
  +B2 = Nat.div(Q, G2)
  +Rr2 = Nat.div(d, G2)
  +ePQ = N.sub_diag(Nat.cmp(U, V), U, V, {==})
  +eQP = N.sub_diag(Nat.cmp(V, U), V, U, {==})
  +eg = Equal.cong(Nat, Nat, u => N.Nat.gcd(u, d),
    Nat.add(Nat.sub(P, Q), Nat.sub(Q, P)),
    Nat.add(P, Q),
    Equal.trans(Nat,
      Nat.add(Nat.sub(P, Q), Nat.sub(Q, P)),
      Nat.add(P, Nat.sub(Q, P)),
      Nat.add(P, Q),
      Equal.cong(Nat, Nat, u => Nat.add(u, Nat.sub(Q, P)), Nat.sub(P, Q), P, ePQ),
      Equal.cong(Nat, Nat, u => Nat.add(P, u), Nat.sub(Q, P), Q, eQP)))
  +E1 = Equal.trans(Nat, A, Nat.div(P, G1), A2,
    Equal.cong(Nat, Nat, u => Nat.div(u, G1), Nat.sub(P, Q), P, ePQ),
    Equal.cong(Nat, Nat, u => Nat.div(P, u), G1, G2, eg))
  +E2 = Equal.trans(Nat, B, Nat.div(Q, G1), B2,
    Equal.cong(Nat, Nat, u => Nat.div(u, G1), Nat.sub(Q, P), Q, eQP),
    Equal.cong(Nat, Nat, u => Nat.div(Q, u), G1, G2, eg))
  +E3 = Equal.cong(Nat, Nat, u => Nat.div(d, u), G1, G2, eg)
  +En = Equal.trans(I.Int, I.Int{A, B}, I.Int{A2, B}, I.Int{A2, B2},
    Equal.cong(Nat, I.Int, u => I.Int{u, B}, A, A2, E1),
    Equal.cong(Nat, I.Int, u => I.Int{A2, u}, B, B2, E2))
  Equal.trans(R.Rat,
    R.Rat{I.Int{A, B}, Rr},
    R.Rat{I.Int{A2, B2}, Rr},
    R.Rat{I.Int{A2, B2}, Rr2},
    Equal.cong(I.Int, R.Rat, u => R.Rat{u, Rr}, I.Int{A, B}, I.Int{A2, B2}, En),
    Equal.cong(Nat, R.Rat, u => R.Rat{I.Int{A2, B2}, u}, Rr, Rr2, E3))

def R.Rat.mk.trunc(U, V, d):
  +P = Nat.sub(U, V)
  +Q = Nat.sub(V, U)
  +G1 = R.Rat.g(U, V, d)
  +G2 = R.Rat.g(Nat.sub(P, Q), Nat.sub(Q, P), d)
  +A1 = Nat.div(P, G1)
  +B1 = Nat.div(Q, G1)
  +R1 = Nat.div(d, G1)
  +A2 = Nat.div(Nat.sub(Nat.sub(P, Q), Nat.sub(Q, P)), G2)
  +B2 = Nat.div(Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q)), G2)
  +R2 = Nat.div(d, G2)
  +eP = Equal.trans(Nat, Nat.sub(Nat.sub(P, Q), Nat.sub(Q, P)), Nat.sub(P, Q), P,
    N.sub_diag(Nat.cmp(P, Q), P, Q, {==}),
    N.sub_diag(Nat.cmp(U, V), U, V, {==}))
  +eQ = Equal.trans(Nat, Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q)), Nat.sub(Q, P), Q,
    N.sub_diag(Nat.cmp(Q, P), Q, P, {==}),
    N.sub_diag(Nat.cmp(V, U), V, U, {==}))
  +eg0 = Equal.trans(Nat,
    Nat.add(Nat.sub(Nat.sub(P, Q), Nat.sub(Q, P)), Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q))),
    Nat.add(P, Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q))),
    Nat.add(P, Q),
    Equal.cong(Nat, Nat, u => Nat.add(u, Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q))),
      Nat.sub(Nat.sub(P, Q), Nat.sub(Q, P)), P, eP),
    Equal.cong(Nat, Nat, u => Nat.add(P, u),
      Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q)), Q, eQ))
  +eg = Equal.trans(Nat, G2, N.Nat.gcd(Nat.add(P, Q), d), G1,
    Equal.cong(Nat, Nat, u => N.Nat.gcd(u, d),
      Nat.add(Nat.sub(Nat.sub(P, Q), Nat.sub(Q, P)), Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q))),
      Nat.add(P, Q), eg0),
    {==})
  +E1 = Equal.trans(Nat, A2, Nat.div(P, G2), A1,
    Equal.cong(Nat, Nat, u => Nat.div(u, G2), Nat.sub(Nat.sub(P, Q), Nat.sub(Q, P)), P, eP),
    Equal.cong(Nat, Nat, u => Nat.div(P, u), G2, G1, eg))
  +E2 = Equal.trans(Nat, B2, Nat.div(Q, G2), B1,
    Equal.cong(Nat, Nat, u => Nat.div(u, G2), Nat.sub(Nat.sub(Q, P), Nat.sub(P, Q)), Q, eQ),
    Equal.cong(Nat, Nat, u => Nat.div(Q, u), G2, G1, eg))
  +E3 = Equal.cong(Nat, Nat, u => Nat.div(d, u), G2, G1, eg)
  +En = Equal.trans(I.Int, I.Int{A2, B2}, I.Int{A1, B2}, I.Int{A1, B1},
    Equal.cong(Nat, I.Int, u => I.Int{u, B2}, A2, A1, E1),
    Equal.cong(Nat, I.Int, u => I.Int{A1, u}, B2, B1, E2))
  Equal.trans(R.Rat,
    R.Rat{I.Int{A1, B1}, R1},
    R.Rat{I.Int{A1, B1}, R2},
    R.Rat{I.Int{A2, B2}, R2},
    Equal.cong(Nat, R.Rat, u => R.Rat{I.Int{A1, B1}, u}, R1, R2, Equal.sym(Nat, R2, R1, E3)),
    Equal.cong(I.Int, R.Rat, u => R.Rat{u, R2}, I.Int{A1, B1}, I.Int{A2, B2},
      Equal.sym(I.Int, I.Int{A2, B2}, I.Int{A1, B1}, En)))

def R.Rat.mk.canon.go(c, xp, xn, d, e):
  match c:
    case EQ{}:
      +eeq = Equal.sym(Nat, xp, xn,
        N.cmp_eq(xp, xn, Equal.sym(Cmp, EQ{}, Nat.cmp(xp, xn), e)))
      +exz = Equal.trans(Nat, Nat.sub(xp, xn), Nat.sub(xp, xp), 0n,
        Equal.cong(Nat, Nat, u => Nat.sub(xp, u), xn, xp, eeq),
        N.sub_self(xp))
      +ezx = Equal.trans(Nat, Nat.sub(xn, xp), Nat.sub(xp, xp), 0n,
        Equal.cong(Nat, Nat, u => Nat.sub(u, xp), xn, xp, eeq),
        N.sub_self(xp))
      +ev = Equal.trans(I.Int, R.Rat.num(xp, xn), I.Int{0n, Nat.sub(xn, xp)}, I.Int{0n, 0n},
        Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(xn, xp)}, Nat.sub(xp, xn), 0n, exz),
        Equal.cong(Nat, I.Int, u => I.Int{0n, u}, Nat.sub(xn, xp), 0n, ezx))
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int{xp, xn}, d),
        R.Rat.mk(R.Rat.num(xp, xn), d),
        R.Rat.mk(I.Int{0n, 0n}, d),
        Equal.sym(R.Rat, R.Rat.mk(R.Rat.num(xp, xn), d), R.Rat.mk(I.Int{xp, xn}, d),
          R.Rat.mk.rep(xp, xn, d)),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, d), R.Rat.num(xp, xn), I.Int{0n, 0n}, ev))
    case GT{}:
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int{xp, xn}, d),
        R.Rat.mk(R.Rat.num(xp, xn), d),
        R.Rat.mk(I.Int{Nat.sub(xp, xn), 0n}, d),
        Equal.sym(R.Rat, R.Rat.mk(R.Rat.num(xp, xn), d), R.Rat.mk(I.Int{xp, xn}, d),
          R.Rat.mk.rep(xp, xn, d)),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, d), R.Rat.num(xp, xn), I.Int{Nat.sub(xp, xn), 0n},
          Equal.cong(Nat, I.Int, u => I.Int{Nat.sub(xp, xn), u}, Nat.sub(xn, xp), 0n,
            N.sub_of_lt(xn, xp, N.cmp_lt_of_gt(xp, xn, Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e))))))
    case LT{}:
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int{xp, xn}, d),
        R.Rat.mk(R.Rat.num(xp, xn), d),
        R.Rat.mk(I.Int{0n, Nat.sub(xn, xp)}, d),
        Equal.sym(R.Rat, R.Rat.mk(R.Rat.num(xp, xn), d), R.Rat.mk(I.Int{xp, xn}, d),
          R.Rat.mk.rep(xp, xn, d)),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, d), R.Rat.num(xp, xn), I.Int{0n, Nat.sub(xn, xp)},
          Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(xn, xp)}, Nat.sub(xp, xn), 0n,
            N.sub_of_lt(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e)))))

def R.Rat.mk.eqv.val(xp, xn, d1, p1, yp, yn, d2, p2, e):
  +a = Nat.sub(d1, 1n)
  +b = Nat.sub(d2, 1n)
  +da = Nat.add(1n, a)
  +db = Nat.add(1n, b)
  +D = Nat.mul(da, db)
  +D2 = Nat.mul(db, da)
  +cx = Nat.cmp(Nat.mul(xp, db), Nat.mul(xn, db))
  +cy = Nat.cmp(Nat.mul(yp, da), Nat.mul(yn, da))
  +eL = Nat.add(Nat.mul(xp, d2), Nat.mul(yn, d1))
  +mL = Nat.add(Nat.mul(xp, db), Nat.mul(yn, d1))
  +mL2 = Nat.add(Nat.mul(xp, db), Nat.mul(yn, da))
  +eR = Nat.add(Nat.mul(yp, d1), Nat.mul(xn, d2))
  +mR = Nat.add(Nat.mul(yp, da), Nat.mul(xn, d2))
  +mR2 = Nat.add(Nat.mul(yp, da), Nat.mul(xn, db))
  +sL = Equal.trans(Nat, eL, mL, mL2,
    Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(xp, u), Nat.mul(yn, d1)), d2, db, N.pos_witness(d2, p2)),
    Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(xp, db), Nat.mul(yn, u)), d1, da, N.pos_witness(d1, p1)))
  +sR = Equal.trans(Nat, eR, mR, mR2,
    Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(yp, u), Nat.mul(xn, d2)), d1, da, N.pos_witness(d1, p1)),
    Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(yp, da), Nat.mul(xn, u)), d2, db, N.pos_witness(d2, p2)))
  +ecross = Equal.trans(Nat, mL2, eL, mR2,
    Equal.sym(Nat, eL, mL2, sL),
    Equal.trans(Nat, eL, eR, mR2, e, sR))
  +ecan = I.Int.canon.eqv.bwd(cx, Nat.mul(xp, db), Nat.mul(xn, db), cy, Nat.mul(yp, da), Nat.mul(yn, da),
    {==}, {==}, ecross)
  +chainL = Equal.trans(R.Rat,
    R.Rat.mk(I.Int{xp, xn}, d1),
    R.Rat.mk(I.Int{xp, xn}, da),
    R.Rat.mk(I.Int.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db)), D),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int{xp, xn}, u), d1, da, N.pos_witness(d1, p1)),
    Equal.trans(R.Rat,
      R.Rat.mk(I.Int{xp, xn}, da),
      R.Rat.mk(I.Int.mul(I.Int{xp, xn}, I.Int.unit(db)), D),
      R.Rat.mk(I.Int.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db)), D),
      Equal.sym(R.Rat, R.Rat.mk(I.Int.mul(I.Int{xp, xn}, I.Int.unit(db)), D),
        R.Rat.mk(I.Int{xp, xn}, da), R.Rat.mk.scale(I.Int{xp, xn}, a, b)),
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.mul(I.Int{xp, xn}, I.Int.unit(db)), D),
        R.Rat.mk(I.Int{Nat.mul(xp, db), Nat.mul(xn, db)}, D),
        R.Rat.mk(I.Int.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db)), D),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, D),
          I.Int.mul(I.Int{xp, xn}, I.Int.unit(db)), I.Int{Nat.mul(xp, db), Nat.mul(xn, db)},
          I.Int.mul_scale(xp, xn, db)),
        R.Rat.mk.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db), D, {==}))))
  +chainR = Equal.trans(R.Rat,
    R.Rat.mk(I.Int{yp, yn}, d2),
    R.Rat.mk(I.Int{yp, yn}, db),
    R.Rat.mk(I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), D),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int{yp, yn}, u), d2, db, N.pos_witness(d2, p2)),
    Equal.trans(R.Rat,
      R.Rat.mk(I.Int{yp, yn}, db),
      R.Rat.mk(I.Int.mul(I.Int{yp, yn}, I.Int.unit(da)), D2),
      R.Rat.mk(I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), D),
      Equal.sym(R.Rat, R.Rat.mk(I.Int.mul(I.Int{yp, yn}, I.Int.unit(da)), D2),
        R.Rat.mk(I.Int{yp, yn}, db), R.Rat.mk.scale(I.Int{yp, yn}, b, a)),
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.mul(I.Int{yp, yn}, I.Int.unit(da)), D2),
        R.Rat.mk(I.Int{Nat.mul(yp, da), Nat.mul(yn, da)}, D2),
        R.Rat.mk(I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), D),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, D2),
          I.Int.mul(I.Int{yp, yn}, I.Int.unit(da)), I.Int{Nat.mul(yp, da), Nat.mul(yn, da)},
          I.Int.mul_scale(yp, yn, da)),
        Equal.trans(R.Rat,
          R.Rat.mk(I.Int{Nat.mul(yp, da), Nat.mul(yn, da)}, D2),
          R.Rat.mk(I.Int{Nat.mul(yp, da), Nat.mul(yn, da)}, D),
          R.Rat.mk(I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), D),
          Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int{Nat.mul(yp, da), Nat.mul(yn, da)}, u),
            D2, D, N.mul_comm(db, da)),
          R.Rat.mk.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da), D, {==})))))
  Equal.trans(R.Rat,
    R.Rat.mk(I.Int{xp, xn}, d1),
    R.Rat.mk(I.Int.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db)), D),
    R.Rat.mk(I.Int{yp, yn}, d2),
    chainL,
    Equal.trans(R.Rat,
      R.Rat.mk(I.Int.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db)), D),
      R.Rat.mk(I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), D),
      R.Rat.mk(I.Int{yp, yn}, d2),
      Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, D),
        I.Int.canon.go(cx, Nat.mul(xp, db), Nat.mul(xn, db)),
        I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), ecan),
      Equal.sym(R.Rat, R.Rat.mk(I.Int{yp, yn}, d2),
        R.Rat.mk(I.Int.canon.go(cy, Nat.mul(yp, da), Nat.mul(yn, da)), D), chainR)))

def Rat.h.add.piece(+A: I.Int, +r: I.Int, +u: I.Int, +e: Nat, +f: Nat, +g: Nat, +h: Nat,
             v: {I.Int.mul(A, I.Int.unit(e)) == I.Int.mul(r, I.Int.unit(h)) : I.Int},
             s: {r == u : I.Int})
  -> {I.Int.mul(I.Int.mul(A, I.Int.unit(g)), I.Int.unit(Nat.mul(e, f)))
      == I.Int.mul(I.Int.mul(u, I.Int.unit(f)), I.Int.unit(Nat.mul(h, g))) : I.Int}:
  +G = I.Int.unit(g)
  +E = I.Int.unit(e)
  +F = I.Int.unit(f)
  +H = I.Int.unit(h)
  +EF = I.Int.unit(Nat.mul(e, f))
  +HG = I.Int.unit(Nat.mul(h, g))
  %Equal.sym(I.Int, EF, I.Int.mul(E, F), I.Int.scale.pair(e, f))
    : {I.Int.mul(I.Int.mul(A, G), _) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(A, G), I.Int.mul(E, F)), I.Int.mul(A, I.Int.mul(G, I.Int.mul(E, F))),
      I.Int.mul_assoc(A, G, I.Int.mul(E, F)))
    : {_ == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %I.Int.mul_assoc(G, E, F)
    : {I.Int.mul(A, _) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(G, E), I.Int.mul(E, G), I.Int.mul_comm(G, E))
    : {I.Int.mul(A, I.Int.mul(_, F)) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(E, G), F), I.Int.mul(E, I.Int.mul(G, F)), I.Int.mul_assoc(E, G, F))
    : {I.Int.mul(A, _) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %I.Int.mul_assoc(A, E, I.Int.mul(G, F))
    : {_ == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(A, E), I.Int.mul(r, H), v)
    : {I.Int.mul(_, I.Int.mul(G, F)) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(r, H), I.Int.mul(u, H),
      Equal.cong(I.Int, I.Int, w => I.Int.mul(w, H), r, u, s))
    : {I.Int.mul(_, I.Int.mul(G, F)) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(u, H), I.Int.mul(G, F)), I.Int.mul(I.Int.mul(u, I.Int.mul(G, F)), H),
      I.Int.mul_swap(u, H, I.Int.mul(G, F)))
    : {_ == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %I.Int.mul_assoc(u, G, F)
    : {I.Int.mul(_, H) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(u, G), F), I.Int.mul(I.Int.mul(u, F), G), I.Int.mul_swap(u, G, F))
    : {I.Int.mul(_, H) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(u, F), G), H), I.Int.mul(I.Int.mul(u, F), I.Int.mul(G, H)),
      I.Int.mul_assoc(I.Int.mul(u, F), G, H))
    : {_ == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(G, H), I.Int.mul(H, G), I.Int.mul_comm(G, H))
    : {I.Int.mul(I.Int.mul(u, F), _) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  %I.Int.scale.pair(h, g)
    : {I.Int.mul(I.Int.mul(u, F), _) == I.Int.mul(I.Int.mul(u, F), HG) : I.Int}
  {==}

def Rat.h.add.cross(+A: I.Int, +B: I.Int, +r1: I.Int, +u1: I.Int, +r2: I.Int, +u2: I.Int,
             +xd: Nat, +yd: Nat, +k1: Nat, +k2: Nat,
             v1: {I.Int.mul(A, I.Int.unit(xd)) == I.Int.mul(r1, I.Int.unit(k1)) : I.Int},
             v2: {I.Int.mul(B, I.Int.unit(yd)) == I.Int.mul(r2, I.Int.unit(k2)) : I.Int},
             s1: {r1 == u1 : I.Int},
             s2: {r2 == u2 : I.Int})
  -> {I.Int.mul(I.Int.add(I.Int.mul(A, I.Int.unit(k2)), I.Int.mul(B, I.Int.unit(k1))), I.Int.unit(Nat.mul(xd, yd)))
      == I.Int.mul(I.Int.add(I.Int.mul(u1, I.Int.unit(yd)), I.Int.mul(u2, I.Int.unit(xd))), I.Int.unit(Nat.mul(k1, k2))) : I.Int}:
  +D = I.Int.unit(Nat.mul(xd, yd))
  +K = I.Int.unit(Nat.mul(k1, k2))
  +AK = I.Int.mul(A, I.Int.unit(k2))
  +BK = I.Int.mul(B, I.Int.unit(k1))
  +U1 = I.Int.mul(u1, I.Int.unit(yd))
  +U2 = I.Int.mul(u2, I.Int.unit(xd))
  %Equal.sym(I.Int, I.Int.mul(I.Int.add(AK, BK), D), I.Int.add(I.Int.mul(AK, D), I.Int.mul(BK, D)),
      I.Int.mul_add_left(AK, BK, D))
    : {_ == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(AK, D), I.Int.mul(U1, K), Rat.h.add.piece(A, r1, u1, xd, yd, k2, k1, v1, s1))
    : {I.Int.add(_, I.Int.mul(BK, D)) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, D, I.Int.unit(Nat.mul(yd, xd)),
      Equal.cong(Nat, I.Int, w => I.Int.unit(w), Nat.mul(xd, yd), Nat.mul(yd, xd), N.mul_comm(xd, yd)))
    : {I.Int.add(I.Int.mul(U1, K), I.Int.mul(BK, _)) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(BK, I.Int.unit(Nat.mul(yd, xd))), I.Int.mul(U2, I.Int.unit(Nat.mul(k2, k1))),
      Rat.h.add.piece(B, r2, u2, yd, xd, k1, k2, v2, s2))
    : {I.Int.add(I.Int.mul(U1, K), _) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, I.Int.unit(Nat.mul(k2, k1)), K,
      Equal.cong(Nat, I.Int, w => I.Int.unit(w), Nat.mul(k2, k1), Nat.mul(k1, k2), N.mul_comm(k2, k1)))
    : {I.Int.add(I.Int.mul(U1, K), I.Int.mul(U2, _)) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %I.Int.mul_add_left(U1, U2, K)
    : {_ == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  {==}

def Rat.h.add.mixed.cross(+A: I.Int, +R: I.Int, +C: I.Int, +d: Nat, +Yd: Nat, +k1: Nat,
             v: {I.Int.mul(A, I.Int.unit(d)) == I.Int.mul(R, I.Int.unit(k1)) : I.Int})
  -> {I.Int.mul(I.Int.add(I.Int.mul(A, I.Int.unit(Yd)), I.Int.mul(C, I.Int.unit(k1))),
               I.Int.unit(Nat.mul(d, Yd)))
      == I.Int.mul(I.Int.add(I.Int.mul(R, I.Int.unit(Yd)), I.Int.mul(C, I.Int.unit(d))),
                   I.Int.unit(Nat.mul(k1, Yd))) : I.Int}:
  +YY = Nat.mul(Yd, Yd)
  +DYY = Nat.mul(d, YY)
  +KYY = Nat.mul(k1, YY)
  +KDY = Nat.mul(k1, Nat.mul(d, Yd))
  +DKY = Nat.mul(d, Nat.mul(k1, Yd))
  +Yu = I.Int.unit(Yd)
  +Ku = I.Int.unit(k1)
  +du = I.Int.unit(d)
  +Duu = I.Int.unit(Nat.mul(d, Yd))
  +Kuu = I.Int.unit(Nat.mul(k1, Yd))
  +AY = I.Int.mul(A, Yu)
  +CK = I.Int.mul(C, Ku)
  +RY = I.Int.mul(R, Yu)
  +Cd = I.Int.mul(C, du)
  +LX1 = I.Int.add(I.Int.mul(AY, Duu), I.Int.mul(CK, Duu))
  +LX2 = I.Int.add(I.Int.mul(A, I.Int.mul(Yu, Duu)), I.Int.mul(C, I.Int.mul(Ku, Duu)))
  +LX3 = I.Int.add(I.Int.mul(A, I.Int.unit(DYY)), I.Int.mul(C, I.Int.unit(KDY)))
  +LX4 = I.Int.add(I.Int.mul(R, I.Int.unit(KYY)), I.Int.mul(C, I.Int.unit(KDY)))
  +RX1 = I.Int.add(I.Int.mul(RY, Kuu), I.Int.mul(Cd, Kuu))
  +RX2 = I.Int.add(I.Int.mul(R, I.Int.mul(Yu, Kuu)), I.Int.mul(C, I.Int.mul(du, Kuu)))
  +RX3 = I.Int.add(I.Int.mul(R, I.Int.unit(KYY)), I.Int.mul(C, I.Int.unit(DKY)))
  +n1 = Equal.trans(Nat, Nat.mul(Yd, Nat.mul(d, Yd)), Nat.mul(Nat.mul(Yd, d), Yd), DYY,
    Equal.sym(Nat, Nat.mul(Nat.mul(Yd, d), Yd), Nat.mul(Yd, Nat.mul(d, Yd)), N.mul_assoc(Yd, d, Yd)),
    Equal.trans(Nat, Nat.mul(Nat.mul(Yd, d), Yd), Nat.mul(Nat.mul(d, Yd), Yd), DYY,
      Equal.cong(Nat, Nat, u => Nat.mul(u, Yd), Nat.mul(Yd, d), Nat.mul(d, Yd), N.mul_comm(Yd, d)),
      N.mul_assoc(d, Yd, Yd)))
  +n2 = Equal.trans(Nat, Nat.mul(Yd, Nat.mul(k1, Yd)), Nat.mul(Nat.mul(Yd, k1), Yd), KYY,
    Equal.sym(Nat, Nat.mul(Nat.mul(Yd, k1), Yd), Nat.mul(Yd, Nat.mul(k1, Yd)), N.mul_assoc(Yd, k1, Yd)),
    Equal.trans(Nat, Nat.mul(Nat.mul(Yd, k1), Yd), Nat.mul(Nat.mul(k1, Yd), Yd), KYY,
      Equal.cong(Nat, Nat, u => Nat.mul(u, Yd), Nat.mul(Yd, k1), Nat.mul(k1, Yd), N.mul_comm(Yd, k1)),
      N.mul_assoc(k1, Yd, Yd)))
  +n3 = Equal.trans(Nat, KDY, Nat.mul(Nat.mul(k1, d), Yd), DKY,
    Equal.sym(Nat, Nat.mul(Nat.mul(k1, d), Yd), KDY, N.mul_assoc(k1, d, Yd)),
    Equal.trans(Nat, Nat.mul(Nat.mul(k1, d), Yd), Nat.mul(Nat.mul(d, k1), Yd), DKY,
      Equal.cong(Nat, Nat, u => Nat.mul(u, Yd), Nat.mul(k1, d), Nat.mul(d, k1), N.mul_comm(k1, d)),
      N.mul_assoc(d, k1, Yd)))
  +e_u1 = Equal.trans(I.Int, I.Int.mul(Yu, Duu), I.Int.unit(Nat.mul(Yd, Nat.mul(d, Yd))), I.Int.unit(DYY),
    Equal.sym(I.Int, I.Int.unit(Nat.mul(Yd, Nat.mul(d, Yd))), I.Int.mul(Yu, Duu),
      I.Int.scale.pair(Yd, Nat.mul(d, Yd))),
    Equal.cong(Nat, I.Int, u => I.Int.unit(u), Nat.mul(Yd, Nat.mul(d, Yd)), DYY, n1))
  +e_u2 = Equal.sym(I.Int, I.Int.unit(KDY), I.Int.mul(Ku, Duu), I.Int.scale.pair(k1, Nat.mul(d, Yd)))
  +e_u3 = Equal.trans(I.Int, I.Int.mul(Yu, Kuu), I.Int.unit(Nat.mul(Yd, Nat.mul(k1, Yd))), I.Int.unit(KYY),
    Equal.sym(I.Int, I.Int.unit(Nat.mul(Yd, Nat.mul(k1, Yd))), I.Int.mul(Yu, Kuu),
      I.Int.scale.pair(Yd, Nat.mul(k1, Yd))),
    Equal.cong(Nat, I.Int, u => I.Int.unit(u), Nat.mul(Yd, Nat.mul(k1, Yd)), KYY, n2))
  +e_u4 = Equal.sym(I.Int, I.Int.unit(DKY), I.Int.mul(du, Kuu), I.Int.scale.pair(d, Nat.mul(k1, Yd)))
  +e_sv = Equal.trans(I.Int, I.Int.mul(A, I.Int.unit(DYY)), I.Int.mul(I.Int.mul(A, du), I.Int.unit(YY)),
    I.Int.mul(R, I.Int.unit(KYY)),
    Equal.trans(I.Int, I.Int.mul(A, I.Int.unit(DYY)), I.Int.mul(A, I.Int.mul(du, I.Int.unit(YY))),
      I.Int.mul(I.Int.mul(A, du), I.Int.unit(YY)),
      Equal.cong(I.Int, I.Int, u => I.Int.mul(A, u), I.Int.unit(DYY), I.Int.mul(du, I.Int.unit(YY)),
        I.Int.scale.pair(d, YY)),
      Equal.sym(I.Int, I.Int.mul(I.Int.mul(A, du), I.Int.unit(YY)),
        I.Int.mul(A, I.Int.mul(du, I.Int.unit(YY))), I.Int.mul_assoc(A, du, I.Int.unit(YY)))),
    Equal.trans(I.Int, I.Int.mul(I.Int.mul(A, du), I.Int.unit(YY)),
      I.Int.mul(I.Int.mul(R, Ku), I.Int.unit(YY)), I.Int.mul(R, I.Int.unit(KYY)),
      Equal.cong(I.Int, I.Int, u => I.Int.mul(u, I.Int.unit(YY)), I.Int.mul(A, du), I.Int.mul(R, Ku), v),
      Equal.trans(I.Int, I.Int.mul(I.Int.mul(R, Ku), I.Int.unit(YY)), I.Int.mul(R, I.Int.mul(Ku, I.Int.unit(YY))),
        I.Int.mul(R, I.Int.unit(KYY)),
        I.Int.mul_assoc(R, Ku, I.Int.unit(YY)),
        Equal.cong(I.Int, I.Int, u => I.Int.mul(R, u), I.Int.mul(Ku, I.Int.unit(YY)), I.Int.unit(KYY),
          Equal.sym(I.Int, I.Int.unit(KYY), I.Int.mul(Ku, I.Int.unit(YY)), I.Int.scale.pair(k1, YY))))))
  Equal.trans(I.Int,
    I.Int.mul(I.Int.add(AY, CK), Duu),
    LX1,
    I.Int.mul(I.Int.add(RY, Cd), Kuu),
    I.Int.mul_add_left(AY, CK, Duu),
    Equal.trans(I.Int, LX1, LX2, I.Int.mul(I.Int.add(RY, Cd), Kuu),
      Equal.trans(I.Int, LX1, I.Int.add(I.Int.mul(A, I.Int.mul(Yu, Duu)), I.Int.mul(CK, Duu)), LX2,
        Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(CK, Duu)), I.Int.mul(AY, Duu),
          I.Int.mul(A, I.Int.mul(Yu, Duu)), I.Int.mul_assoc(A, Yu, Duu)),
        Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(A, I.Int.mul(Yu, Duu)), u), I.Int.mul(CK, Duu),
          I.Int.mul(C, I.Int.mul(Ku, Duu)), I.Int.mul_assoc(C, Ku, Duu))),
      Equal.trans(I.Int, LX2, LX3, I.Int.mul(I.Int.add(RY, Cd), Kuu),
        Equal.trans(I.Int, LX2, I.Int.add(I.Int.mul(A, I.Int.unit(DYY)), I.Int.mul(C, I.Int.mul(Ku, Duu))), LX3,
          Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(C, I.Int.mul(Ku, Duu))),
            I.Int.mul(A, I.Int.mul(Yu, Duu)), I.Int.mul(A, I.Int.unit(DYY)),
            Equal.cong(I.Int, I.Int, u => I.Int.mul(A, u), I.Int.mul(Yu, Duu), I.Int.unit(DYY), e_u1)),
          Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(A, I.Int.unit(DYY)), u),
            I.Int.mul(C, I.Int.mul(Ku, Duu)), I.Int.mul(C, I.Int.unit(KDY)),
            Equal.cong(I.Int, I.Int, u => I.Int.mul(C, u), I.Int.mul(Ku, Duu), I.Int.unit(KDY), e_u2))),
        Equal.trans(I.Int, LX3, LX4, I.Int.mul(I.Int.add(RY, Cd), Kuu),
          Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(C, I.Int.unit(KDY))),
            I.Int.mul(A, I.Int.unit(DYY)), I.Int.mul(R, I.Int.unit(KYY)), e_sv),
          Equal.trans(I.Int, LX4, RX3, I.Int.mul(I.Int.add(RY, Cd), Kuu),
            Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(R, I.Int.unit(KYY)), u),
              I.Int.mul(C, I.Int.unit(KDY)), I.Int.mul(C, I.Int.unit(DKY)),
              Equal.cong(I.Int, I.Int, u => I.Int.mul(C, u), I.Int.unit(KDY), I.Int.unit(DKY),
                Equal.cong(Nat, I.Int, u => I.Int.unit(u), KDY, DKY, n3))),
            Equal.trans(I.Int, RX3, RX2, I.Int.mul(I.Int.add(RY, Cd), Kuu),
            Equal.sym(I.Int, RX2, RX3,
              Equal.trans(I.Int, RX2, I.Int.add(I.Int.mul(R, I.Int.unit(KYY)), I.Int.mul(C, I.Int.mul(du, Kuu))), RX3,
                Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(C, I.Int.mul(du, Kuu))),
                  I.Int.mul(R, I.Int.mul(Yu, Kuu)), I.Int.mul(R, I.Int.unit(KYY)),
                  Equal.cong(I.Int, I.Int, u => I.Int.mul(R, u), I.Int.mul(Yu, Kuu), I.Int.unit(KYY), e_u3)),
                Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(R, I.Int.unit(KYY)), u),
                  I.Int.mul(C, I.Int.mul(du, Kuu)), I.Int.mul(C, I.Int.unit(DKY)),
                  Equal.cong(I.Int, I.Int, u => I.Int.mul(C, u), I.Int.mul(du, Kuu), I.Int.unit(DKY), e_u4)))),
            Equal.trans(I.Int, RX2, RX1, I.Int.mul(I.Int.add(RY, Cd), Kuu),
            Equal.sym(I.Int, RX1, RX2,
              Equal.trans(I.Int, RX1, I.Int.add(I.Int.mul(R, I.Int.mul(Yu, Kuu)), I.Int.mul(Cd, Kuu)), RX2,
                Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(Cd, Kuu)), I.Int.mul(RY, Kuu),
                  I.Int.mul(R, I.Int.mul(Yu, Kuu)), I.Int.mul_assoc(R, Yu, Kuu)),
                Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(R, I.Int.mul(Yu, Kuu)), u), I.Int.mul(Cd, Kuu),
                  I.Int.mul(C, I.Int.mul(du, Kuu)), I.Int.mul_assoc(C, du, Kuu)))),
            Equal.sym(I.Int, I.Int.mul(I.Int.add(RY, Cd), Kuu), RX1,
              I.Int.mul_add_left(RY, Cd, Kuu)))))))))

def R.Rat.add.value.mixed(np1, nn1, d, pd, pq, np2, nn2, dp2):
  +Yd = Nat.add(1n, dp2)
  +P1 = Nat.sub(np1, nn1)
  +Q1 = Nat.sub(nn1, np1)
  +P2 = Nat.sub(np2, nn2)
  +Q2 = Nat.sub(nn2, np2)
  +M1 = R.Rat.mk(I.Int{P1, Q1}, d)
  +A = R.Rat.numof(M1)
  +k1 = R.Rat.denof(M1)
  +nL = I.Int.add(I.Int.mul(A, I.Int.unit(Yd)), I.Int.mul(I.Int{P2, Q2}, I.Int.unit(k1)))
  +dL = Nat.mul(k1, Yd)
  +T = I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(Yd)), I.Int.mul(I.Int{P2, Q2}, I.Int.unit(d)))
  +dT = Nat.mul(d, Yd)
  +ev = Equal.trans(I.Int,
    R.Rat.num(P1, Q1),
    I.Int{P1, Nat.sub(Q1, P1)},
    I.Int{P1, Q1},
    Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(Q1, P1)}, Nat.sub(P1, Q1), P1,
      N.sub_diag(Nat.cmp(np1, nn1), np1, nn1, {==})),
    Equal.cong(Nat, I.Int, u => I.Int{P1, u}, Nat.sub(Q1, P1), Q1,
      N.sub_diag(N.Cmp.flip(Nat.cmp(np1, nn1)), nn1, np1,
        Equal.trans(Cmp, N.Cmp.flip(Nat.cmp(np1, nn1)),
          N.Cmp.flip(N.Cmp.flip(Nat.cmp(nn1, np1))), Nat.cmp(nn1, np1),
          Equal.cong(Cmp, Cmp, N.Cmp.flip, Nat.cmp(np1, nn1), N.Cmp.flip(Nat.cmp(nn1, np1)),
            N.cmp_antisym(np1, nn1)),
          N.flip_flip(Nat.cmp(nn1, np1))))))
  +v = Equal.trans(I.Int,
    I.Int.mul(A, I.Int.unit(d)),
    I.Int.mul(R.Rat.num(P1, Q1), I.Int.unit(k1)),
    I.Int.mul(I.Int{P1, Q1}, I.Int.unit(k1)),
    R.Rat.mk.value(Nat.cmp(P1, Q1), P1, Q1, d, {==}, pd),
    Equal.cong(I.Int, I.Int, u => I.Int.mul(u, I.Int.unit(k1)), R.Rat.num(P1, Q1), I.Int{P1, Q1}, ev))
  R.Rat.mk.eqv.raw(nL, dL, T, dT,
    N.mul_pos(k1, Yd, pq, {==}),
    N.mul_pos(d, Yd, pd, {==}),
    Rat.h.add.mixed.cross(A, I.Int{P1, Q1}, I.Int{P2, Q2}, d, Yd, k1, v))

def Rat.h.nat.pad(+b: Nat, +Xd: Nat, +Zd: Nat, +D: Nat)
  -> {Nat.mul(Nat.mul(b, Xd), Nat.mul(Zd, D)) == Nat.mul(Nat.mul(b, Zd), Nat.mul(Xd, D)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(b, Xd), Nat.mul(Zd, D)), Nat.mul(b, Nat.mul(Xd, Nat.mul(Zd, D))),
      N.mul_assoc(b, Xd, Nat.mul(Zd, D)))
    : {_ == Nat.mul(Nat.mul(b, Zd), Nat.mul(Xd, D)) : Nat}
  %N.mul_assoc(Xd, Zd, D)
    : {Nat.mul(b, _) == Nat.mul(Nat.mul(b, Zd), Nat.mul(Xd, D)) : Nat}
  %Equal.cong(Nat, Nat, v => Nat.mul(v, D), Nat.mul(Zd, Xd), Nat.mul(Xd, Zd),
      Equal.sym(Nat, Nat.mul(Xd, Zd), Nat.mul(Zd, Xd), N.mul_comm(Xd, Zd)))
    : {Nat.mul(b, _) == Nat.mul(Nat.mul(b, Zd), Nat.mul(Xd, D)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Zd, Xd), D), Nat.mul(Zd, Nat.mul(Xd, D)), N.mul_assoc(Zd, Xd, D))
    : {Nat.mul(b, _) == Nat.mul(Nat.mul(b, Zd), Nat.mul(Xd, D)) : Nat}
  %N.mul_assoc(b, Zd, Nat.mul(Xd, D))
    : {_ == Nat.mul(Nat.mul(b, Zd), Nat.mul(Xd, D)) : Nat}
  {==}

def Rat.h.nat.exch4(+x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat)
  -> {Nat.add(Nat.add(x1, x3), Nat.add(x2, x4)) == Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x3), Nat.add(x2, x4)), Nat.add(x1, Nat.add(x3, Nat.add(x2, x4))),
      N.add_assoc(x1, x3, Nat.add(x2, x4)))
    : {_ == Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x2, x4)), Nat.add(x2, Nat.add(x3, x4)),
      N.add_exchange(x3, x2, x4))
    : {Nat.add(x1, _) == Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, x4), Nat.add(x4, x3), N.add_comm(x3, x4))
    : {Nat.add(x1, Nat.add(x2, _)) == Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)) : Nat}
  %N.add_exchange(x4, x2, x3)
    : {Nat.add(x1, _) == Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)) : Nat}
  %N.add_assoc(x1, x4, Nat.add(x2, x3))
    : {_ == Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)) : Nat}
  {==}

def Rat.h.nat.split(+P: Nat, +Q: Nat, +vg: Nat, +vp: Nat, +ug: Nat, +up: Nat, +s: Nat, +T: Nat, +T2: Nat,
          e: {Nat.add(P, Nat.add(vg, vp)) == Nat.add(Q, Nat.add(ug, up)) : Nat},
          ev: {Nat.mul(vp, s) == T : Nat},
          eu: {Nat.mul(up, s) == T2 : Nat})
  -> {Nat.add(Nat.add(Nat.mul(P, s), Nat.mul(vg, s)), T)
      == Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), T2) : Nat}:
  %ev : {Nat.add(Nat.add(Nat.mul(P, s), Nat.mul(vg, s)), _)
         == Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), T2) : Nat}
  %eu : {Nat.add(Nat.add(Nat.mul(P, s), Nat.mul(vg, s)), Nat.mul(vp, s))
         == Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(P, s), Nat.mul(vg, s)), Nat.mul(vp, s)),
      Nat.add(Nat.mul(P, s), Nat.add(Nat.mul(vg, s), Nat.mul(vp, s))),
      N.add_assoc(Nat.mul(P, s), Nat.mul(vg, s), Nat.mul(vp, s)))
    : {_ == Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), Nat.mul(up, s)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(vg, s), Nat.mul(vp, s)), Nat.mul(Nat.add(vg, vp), s),
      N.mul_add_left(vg, vp, s))
    : {Nat.add(Nat.mul(P, s), _) == Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), Nat.mul(up, s)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(P, s), Nat.mul(Nat.add(vg, vp), s)), Nat.mul(Nat.add(P, Nat.add(vg, vp)), s),
      N.mul_add_left(P, Nat.add(vg, vp), s))
    : {_ == Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), Nat.mul(up, s)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Q, s), Nat.mul(ug, s)), Nat.mul(up, s)),
      Nat.add(Nat.mul(Q, s), Nat.add(Nat.mul(ug, s), Nat.mul(up, s))),
      N.add_assoc(Nat.mul(Q, s), Nat.mul(ug, s), Nat.mul(up, s)))
    : {Nat.mul(Nat.add(P, Nat.add(vg, vp)), s) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(ug, s), Nat.mul(up, s)), Nat.mul(Nat.add(ug, up), s),
      N.mul_add_left(ug, up, s))
    : {Nat.mul(Nat.add(P, Nat.add(vg, vp)), s) == Nat.add(Nat.mul(Q, s), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Q, s), Nat.mul(Nat.add(ug, up), s)), Nat.mul(Nat.add(Q, Nat.add(ug, up)), s),
      N.mul_add_left(Q, Nat.add(ug, up), s))
    : {Nat.mul(Nat.add(P, Nat.add(vg, vp)), s) == _ : Nat}
  %Equal.cong(Nat, Nat, u => Nat.mul(u, s), Nat.add(P, Nat.add(vg, vp)), Nat.add(Q, Nat.add(ug, up)), e)
    : {Nat.mul(Nat.add(P, Nat.add(vg, vp)), s) == _ : Nat}
  {==}

def Rat.h.nat.d3(+Xd: Nat, +Yd: Nat, +Zd: Nat) -> Nat:
  Nat.mul(Xd, Nat.mul(Yd, Zd))

def Rat.h.nat.xy(+Xd: Nat, +Yd: Nat) -> Nat:
  Nat.mul(Xd, Yd)

def Rat.h.nat.flip2(+P: Nat, +Q: Nat, +vp: Nat, +vg: Nat, +up: Nat, +ug: Nat,
          e: {Nat.add(P, Nat.add(vp, vg)) == Nat.add(Q, Nat.add(up, ug)) : Nat})
  -> {Nat.add(P, Nat.add(vg, vp)) == Nat.add(Q, Nat.add(ug, up)) : Nat}:
  Equal.trans(Nat,
    Nat.add(P, Nat.add(vg, vp)),
    Nat.add(P, Nat.add(vp, vg)),
    Nat.add(Q, Nat.add(ug, up)),
    Equal.cong(Nat, Nat, u => Nat.add(P, u), Nat.add(vg, vp), Nat.add(vp, vg),
      Equal.sym(Nat, Nat.add(vp, vg), Nat.add(vg, vp), N.add_comm(vp, vg))),
    Equal.trans(Nat,
      Nat.add(P, Nat.add(vp, vg)),
      Nat.add(Q, Nat.add(up, ug)),
      Nat.add(Q, Nat.add(ug, up)),
      e,
      Equal.sym(Nat, Nat.add(Q, Nat.add(ug, up)), Nat.add(Q, Nat.add(up, ug)),
        Equal.cong(Nat, Nat, u => Nat.add(Q, u), Nat.add(ug, up), Nat.add(up, ug),
          Equal.sym(Nat, Nat.add(up, ug), Nat.add(ug, up), N.add_comm(up, ug))))))

def Rat.h.nat.foldA(+c1: Nat, +c2: Nat, +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.add(Nat.mul(c1, Nat.mul(Zd, Rat.h.nat.d3(Xd, Yd, Zd))),
            Nat.mul(Nat.mul(c2, Yd), Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd))))
      == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}:
  %N.mul_assoc(c1, Zd, Rat.h.nat.d3(Xd, Yd, Zd))
    : {Nat.add(_, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd))))
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd))),
      Nat.mul(c2, Nat.mul(Yd, Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd)))),
      N.mul_assoc(c2, Yd, Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd))))
    : {Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.h.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.trans(Nat,
      Nat.mul(Rat.h.nat.xy(Xd, Yd), Rat.h.nat.d3(Xd, Yd, Zd)),
      Nat.mul(Nat.mul(Yd, Xd), Rat.h.nat.d3(Xd, Yd, Zd)),
      Nat.mul(Yd, Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd))),
      Equal.cong(Nat, Nat, v => Nat.mul(v, Rat.h.nat.d3(Xd, Yd, Zd)), Rat.h.nat.xy(Xd, Yd), Nat.mul(Yd, Xd), N.mul_comm(Xd, Yd)),
      N.mul_assoc(Yd, Xd, Rat.h.nat.d3(Xd, Yd, Zd)))
    : {Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.h.nat.d3(Xd, Yd, Zd)), Nat.mul(c2, _))
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %N.mul_assoc(c2, Rat.h.nat.xy(Xd, Yd), Rat.h.nat.d3(Xd, Yd, Zd))
    : {Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.h.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.h.nat.d3(Xd, Yd, Zd)),
        Nat.mul(Nat.mul(c2, Rat.h.nat.xy(Xd, Yd)), Rat.h.nat.d3(Xd, Yd, Zd))),
      Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)),
      N.mul_add_left(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd)), Rat.h.nat.d3(Xd, Yd, Zd)))
    : {_ == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  {==}

def Rat.h.nat.foldB(+c1: Nat, +c2: Nat, +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.add(Nat.mul(c1, Nat.mul(Xd, Rat.h.nat.d3(Xd, Yd, Zd))),
            Nat.mul(Nat.mul(c2, Yd), Nat.mul(Zd, Rat.h.nat.d3(Xd, Yd, Zd))))
      == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}:
  %N.mul_assoc(c1, Xd, Rat.h.nat.d3(Xd, Yd, Zd))
    : {Nat.add(_, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Zd, Rat.h.nat.d3(Xd, Yd, Zd))))
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Zd, Rat.h.nat.d3(Xd, Yd, Zd))),
      Nat.mul(c2, Nat.mul(Yd, Nat.mul(Zd, Rat.h.nat.d3(Xd, Yd, Zd)))),
      N.mul_assoc(c2, Yd, Nat.mul(Zd, Rat.h.nat.d3(Xd, Yd, Zd))))
    : {Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.h.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %N.mul_assoc(Yd, Zd, Rat.h.nat.d3(Xd, Yd, Zd))
    : {Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.h.nat.d3(Xd, Yd, Zd)), Nat.mul(c2, _))
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %N.mul_assoc(c2, Nat.mul(Yd, Zd), Rat.h.nat.d3(Xd, Yd, Zd))
    : {Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.h.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.h.nat.d3(Xd, Yd, Zd)),
        Nat.mul(Nat.mul(c2, Nat.mul(Yd, Zd)), Rat.h.nat.d3(Xd, Yd, Zd))),
      Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)),
      N.mul_add_left(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd)), Rat.h.nat.d3(Xd, Yd, Zd)))
    : {_ == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)) : Nat}
  {==}

def Rat.h.nat.cross4(+P1: Nat, +Q1: Nat, +P2: Nat, +Q2: Nat,
           +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +a3: Nat, +b3: Nat,
           +Xd: Nat, +Yd: Nat, +Zd: Nat,
           e1: {Nat.add(P1, Nat.add(Nat.mul(b1, Yd), Nat.mul(b2, Xd)))
                == Nat.add(Q1, Nat.add(Nat.mul(a1, Yd), Nat.mul(a2, Xd))) : Nat},
           e2: {Nat.add(P2, Nat.add(Nat.mul(b2, Zd), Nat.mul(b3, Yd)))
                == Nat.add(Q2, Nat.add(Nat.mul(a2, Zd), Nat.mul(a3, Yd))) : Nat})
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Zd), Nat.mul(a3, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd)),
           Nat.mul(Nat.add(Nat.mul(Q2, Xd), Nat.mul(b1, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(P2, Xd), Nat.mul(a1, Nat.mul(Yd, Zd))), Rat.h.nat.d3(Xd, Yd, Zd)),
                 Nat.mul(Nat.add(Nat.mul(Q1, Zd), Nat.mul(b3, Rat.h.nat.xy(Xd, Yd))), Rat.h.nat.d3(Xd, Yd, Zd))) : Nat}:
  +D = Rat.h.nat.d3(Xd, Yd, Zd)
  +s1 = Nat.mul(Zd, D)
  +s2 = Nat.mul(Xd, D)
  +A = Nat.add(Nat.mul(P1, s1), Nat.mul(Nat.mul(b1, Yd), s1))
  +A2 = Nat.add(Nat.mul(Q1, s1), Nat.mul(Nat.mul(a1, Yd), s1))
  +B = Nat.add(Nat.mul(P2, s2), Nat.mul(Nat.mul(b3, Yd), s2))
  +B2 = Nat.add(Nat.mul(Q2, s2), Nat.mul(Nat.mul(a3, Yd), s2))
  +Tb = Nat.mul(Nat.mul(b2, Zd), s2)
  +Ta = Nat.mul(Nat.mul(a2, Zd), s2)
  +e2f = Rat.h.nat.flip2(P2, Q2, Nat.mul(b2, Zd), Nat.mul(b3, Yd), Nat.mul(a2, Zd), Nat.mul(a3, Yd), e2)
  +h1 = Rat.h.nat.split(P1, Q1, Nat.mul(b1, Yd), Nat.mul(b2, Xd), Nat.mul(a1, Yd), Nat.mul(a2, Xd),
    s1, Tb, Ta, e1, Rat.h.nat.pad(b2, Xd, Zd, D), Rat.h.nat.pad(a2, Xd, Zd, D))
  +h2 = Rat.h.nat.split(P2, Q2, Nat.mul(b3, Yd), Nat.mul(b2, Zd), Nat.mul(a3, Yd), Nat.mul(a2, Zd),
    s2, Tb, Ta, e2f, {==}, {==})
  +c = N.cross_add(A, A2, B, B2, Tb, Ta, h1, h2)
  +x1 = Nat.mul(P1, s1)
  +x2 = Nat.mul(Q2, s2)
  +x3 = Nat.mul(Nat.mul(b1, Yd), s1)
  +x4 = Nat.mul(Nat.mul(a3, Yd), s2)
  +y1 = Nat.mul(Q1, s1)
  +y2 = Nat.mul(P2, s2)
  +y3 = Nat.mul(Nat.mul(a1, Yd), s1)
  +y4 = Nat.mul(Nat.mul(b3, Yd), s2)
  +xf = Rat.h.nat.exch4(x1, x2, x3, x4)
  +yf = Rat.h.nat.exch4(y1, y2, y3, y4)
  +r1 = Nat.mul(Nat.add(Nat.mul(P1, Zd), Nat.mul(a3, Rat.h.nat.xy(Xd, Yd))), D)
  +r2 = Nat.mul(Nat.add(Nat.mul(Q2, Xd), Nat.mul(b1, Nat.mul(Yd, Zd))), D)
  +r3 = Nat.mul(Nat.add(Nat.mul(P2, Xd), Nat.mul(a1, Nat.mul(Yd, Zd))), D)
  +r4 = Nat.mul(Nat.add(Nat.mul(Q1, Zd), Nat.mul(b3, Rat.h.nat.xy(Xd, Yd))), D)
  +lc = Equal.trans(Nat,
      Nat.add(A, B2),
      Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)),
      Nat.add(r1, r2),
      xf,
      Equal.trans(Nat,
        Nat.add(Nat.add(x1, x4), Nat.add(x2, x3)),
        Nat.add(r1, Nat.add(x2, x3)),
        Nat.add(r1, r2),
        Equal.cong(Nat, Nat, u => Nat.add(u, Nat.add(x2, x3)), Nat.add(x1, x4), r1,
          Rat.h.nat.foldA(P1, a3, Xd, Yd, Zd)),
        Equal.cong(Nat, Nat, u => Nat.add(r1, u), Nat.add(x2, x3), r2,
          Rat.h.nat.foldB(Q2, b1, Xd, Yd, Zd))))
  +rc = Equal.trans(Nat,
      Nat.add(A2, B),
      Nat.add(Nat.add(y1, y4), Nat.add(y2, y3)),
      Nat.add(r3, r4),
      yf,
      Equal.trans(Nat,
        Nat.add(Nat.add(y1, y4), Nat.add(y2, y3)),
        Nat.add(r4, Nat.add(y2, y3)),
        Nat.add(r3, r4),
        Equal.cong(Nat, Nat, u => Nat.add(u, Nat.add(y2, y3)), Nat.add(y1, y4), r4,
          Rat.h.nat.foldA(Q1, b3, Xd, Yd, Zd)),
        Equal.trans(Nat,
          Nat.add(r4, Nat.add(y2, y3)),
          Nat.add(r4, r3),
          Nat.add(r3, r4),
          Equal.cong(Nat, Nat, u => Nat.add(r4, u), Nat.add(y2, y3), r3,
            Rat.h.nat.foldB(P2, a1, Xd, Yd, Zd)),
          N.add_comm(r4, r3))))
  Equal.trans(Nat,
    Nat.add(r1, r2),
    Nat.add(A, B2),
    Nat.add(r3, r4),
    Equal.sym(Nat, Nat.add(A, B2), Nat.add(r1, r2), lc),
    Equal.trans(Nat, Nat.add(A, B2), Nat.add(A2, B), Nat.add(r3, r4), c, rc))

def R.Rat.add_assoc(np1, nn1, dp1, np2, nn2, dp2, np3, nn3, dp3):
  +Xd = Nat.add(1n, dp1)
  +Yd = Nat.add(1n, dp2)
  +Zd = Nat.add(1n, dp3)
  +a1 = Nat.sub(np1, nn1)
  +b1 = Nat.sub(nn1, np1)
  +a2 = Nat.sub(np2, nn2)
  +b2 = Nat.sub(nn2, np2)
  +a3 = Nat.sub(np3, nn3)
  +b3 = Nat.sub(nn3, np3)
  +xn = R.Rat.num(np1, nn1)
  +yn = R.Rat.num(np2, nn2)
  +zn = R.Rat.num(np3, nn3)
  +U1 = Nat.add(Nat.mul(a1, Yd), Nat.mul(a2, Xd))
  +V1 = Nat.add(Nat.mul(b1, Yd), Nat.mul(b2, Xd))
  +U2 = Nat.add(Nat.mul(a2, Zd), Nat.mul(a3, Yd))
  +V2 = Nat.add(Nat.mul(b2, Zd), Nat.mul(b3, Yd))
  +d1 = Nat.mul(Xd, Yd)
  +d2 = Nat.mul(Yd, Zd)
  +M1 = R.Rat.mk(I.Int{U1, V1}, d1)
  +M2 = R.Rat.mk(I.Int{U2, V2}, d2)
  +P1 = Nat.sub(U1, V1)
  +Q1 = Nat.sub(V1, U1)
  +P2 = Nat.sub(U2, V2)
  +Q2 = Nat.sub(V2, U2)
  +N1 = R.Rat.mk(R.Rat.num(P1, Q1), d1)
  +N2 = R.Rat.mk(R.Rat.num(P2, Q2), d2)
  +D = Rat.h.nat.d3(Xd, Yd, Zd)
  +TLp = Nat.add(Nat.mul(P1, Zd), Nat.mul(a3, Rat.h.nat.xy(Xd, Yd)))
  +TLn = Nat.add(Nat.mul(Q1, Zd), Nat.mul(b3, Rat.h.nat.xy(Xd, Yd)))
  +TRp = Nat.add(Nat.mul(P2, Xd), Nat.mul(a1, Nat.mul(Yd, Zd)))
  +TRn = Nat.add(Nat.mul(Q2, Xd), Nat.mul(b1, Nat.mul(Yd, Zd)))
  +G1 = R.Rat.g(Nat.sub(P1, Q1), Nat.sub(Q1, P1), d1)
  +G2 = R.Rat.g(Nat.sub(P2, Q2), Nat.sub(Q2, P2), d2)
  +pd1 = N.mul_pos(Xd, Yd, {==}, {==})
  +pq1 = N.div_pos_wit(G1, Nat.add(dp2, Nat.mul(dp1, Nat.add(1n, dp2))),
    Pair.snd(N.Nat.divides(G1, R.Rat.mag(Nat.sub(P1, Q1), Nat.sub(Q1, P1))),
             N.Nat.divides(G1, d1),
             N.gcd_divides(R.Rat.mag(Nat.sub(P1, Q1), Nat.sub(Q1, P1)), d1)))
  +pd2 = N.mul_pos(Yd, Zd, {==}, {==})
  +pq2 = N.div_pos_wit(G2, Nat.add(dp3, Nat.mul(dp2, Nat.add(1n, dp3))),
    Pair.snd(N.Nat.divides(G2, R.Rat.mag(Nat.sub(P2, Q2), Nat.sub(Q2, P2))),
             N.Nat.divides(G2, d2),
             N.gcd_divides(R.Rat.mag(Nat.sub(P2, Q2), Nat.sub(Q2, P2)), d2)))
  +rawXY = I.Int.add(I.Int.mul(xn, I.Int.unit(Yd)), I.Int.mul(yn, I.Int.unit(Xd)))
  +rawYZ = I.Int.add(I.Int.mul(yn, I.Int.unit(Zd)), I.Int.mul(zn, I.Int.unit(Yd)))
  +rawL = I.Int.add(I.Int.mul(I.Int{Nat.sub(P1, Q1), Nat.sub(Q1, P1)}, I.Int.unit(Zd)),
                    I.Int.mul(I.Int{Nat.sub(np3, nn3), Nat.sub(nn3, np3)}, I.Int.unit(d1)))
  +rawR = I.Int.add(I.Int.mul(I.Int{Nat.sub(P2, Q2), Nat.sub(Q2, P2)}, I.Int.unit(Xd)),
                    I.Int.mul(I.Int{Nat.sub(np1, nn1), Nat.sub(nn1, np1)}, I.Int.unit(d2)))
  +eXYi = Equal.trans(I.Int,
    rawXY,
    I.Int.add(I.Int{Nat.mul(a1, Yd), Nat.mul(b1, Yd)}, I.Int.mul(yn, I.Int.unit(Xd))),
    I.Int{U1, V1},
    Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(yn, I.Int.unit(Xd))),
      I.Int.mul(xn, I.Int.unit(Yd)), I.Int{Nat.mul(a1, Yd), Nat.mul(b1, Yd)}, I.Int.mul_scale(a1, b1, Yd)),
    Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int{Nat.mul(a1, Yd), Nat.mul(b1, Yd)}, u),
      I.Int.mul(yn, I.Int.unit(Xd)), I.Int{Nat.mul(a2, Xd), Nat.mul(b2, Xd)}, I.Int.mul_scale(a2, b2, Xd)))
  +eXY = Equal.trans(R.Rat,
    R.Rat.add(R.Rat{xn, Xd}, R.Rat{yn, Yd}),
    R.Rat.mk(rawXY, d1),
    M1,
    {==},
    Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, d1), rawXY, I.Int{U1, V1}, eXYi))
  +eYZi = Equal.trans(I.Int,
    rawYZ,
    I.Int.add(I.Int{Nat.mul(a2, Zd), Nat.mul(b2, Zd)}, I.Int.mul(zn, I.Int.unit(Yd))),
    I.Int{U2, V2},
    Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(zn, I.Int.unit(Yd))),
      I.Int.mul(yn, I.Int.unit(Zd)), I.Int{Nat.mul(a2, Zd), Nat.mul(b2, Zd)}, I.Int.mul_scale(a2, b2, Zd)),
    Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int{Nat.mul(a2, Zd), Nat.mul(b2, Zd)}, u),
      I.Int.mul(zn, I.Int.unit(Yd)), I.Int{Nat.mul(a3, Yd), Nat.mul(b3, Yd)}, I.Int.mul_scale(a3, b3, Yd)))
  +eYZ = Equal.trans(R.Rat,
    R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd}),
    R.Rat.mk(rawYZ, d2),
    M2,
    {==},
    Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, d2), rawYZ, I.Int{U2, V2}, eYZi))
  +L1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat{zn, Zd}),
    R.Rat.add(R.Rat{xn, Xd}, R.Rat{yn, Yd}), M1, eXY)
  +L2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat{zn, Zd}), M1, N1, R.Rat.mk.trunc(U1, V1, d1))
  +L3 = R.Rat.add.value.mixed(P1, Q1, d1, pd1, pq1, np3, nn3, dp3)
  +ePi = Equal.trans(I.Int,
    R.Rat.num(P1, Q1),
    I.Int{P1, Nat.sub(Q1, P1)},
    I.Int{P1, Q1},
    Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(Q1, P1)}, Nat.sub(P1, Q1), P1,
      N.sub_diag(Nat.cmp(U1, V1), U1, V1, {==})),
    Equal.cong(Nat, I.Int, u => I.Int{P1, u}, Nat.sub(Q1, P1), Q1,
      N.sub_diag(Nat.cmp(V1, U1), V1, U1, {==})))
  +L4i = Equal.trans(I.Int,
    rawL,
    I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(Zd)),
              I.Int.mul(I.Int{a3, b3}, I.Int.unit(d1))),
    I.Int{TLp, TLn},
    Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(u, I.Int.unit(Zd)),
        I.Int.mul(I.Int{a3, b3}, I.Int.unit(d1))),
      I.Int{Nat.sub(P1, Q1), Nat.sub(Q1, P1)}, I.Int{P1, Q1}, ePi),
    Equal.trans(I.Int,
      I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(Zd)), I.Int.mul(I.Int{a3, b3}, I.Int.unit(d1))),
      I.Int.add(I.Int{Nat.mul(P1, Zd), Nat.mul(Q1, Zd)}, I.Int.mul(I.Int{a3, b3}, I.Int.unit(d1))),
      I.Int{TLp, TLn},
      Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(I.Int{a3, b3}, I.Int.unit(d1))),
        I.Int.mul(I.Int{P1, Q1}, I.Int.unit(Zd)), I.Int{Nat.mul(P1, Zd), Nat.mul(Q1, Zd)},
        I.Int.mul_scale(P1, Q1, Zd)),
      Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int{Nat.mul(P1, Zd), Nat.mul(Q1, Zd)}, u),
        I.Int.mul(I.Int{a3, b3}, I.Int.unit(d1)), I.Int{Nat.mul(a3, d1), Nat.mul(b3, d1)},
        I.Int.mul_scale(a3, b3, d1))))
  +L4 = Equal.trans(R.Rat,
    R.Rat.mk(rawL, Nat.mul(d1, Zd)),
    R.Rat.mk(I.Int{TLp, TLn}, Nat.mul(d1, Zd)),
    R.Rat.mk(I.Int{TLp, TLn}, D),
    Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(d1, Zd)), rawL, I.Int{TLp, TLn}, L4i),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int{TLp, TLn}, u), Nat.mul(d1, Zd), D,
      N.mul_assoc(Xd, Yd, Zd)))
  +eL = Equal.trans(R.Rat,
    R.Rat.add(R.Rat.add(R.Rat{xn, Xd}, R.Rat{yn, Yd}), R.Rat{zn, Zd}),
    R.Rat.add(M1, R.Rat{zn, Zd}),
    R.Rat.mk(I.Int{TLp, TLn}, D),
    L1,
    Equal.trans(R.Rat,
      R.Rat.add(M1, R.Rat{zn, Zd}),
      R.Rat.add(N1, R.Rat{zn, Zd}),
      R.Rat.mk(I.Int{TLp, TLn}, D),
      L2,
      Equal.trans(R.Rat, R.Rat.add(N1, R.Rat{zn, Zd}), R.Rat.mk(rawL, Nat.mul(d1, Zd)),
        R.Rat.mk(I.Int{TLp, TLn}, D), L3, L4)))
  +R0 = R.Rat.add_comm(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd}))
  +R1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat{xn, Xd}),
    R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd}), M2, eYZ)
  +R2 = Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, R.Rat{xn, Xd}), M2, N2, R.Rat.mk.trunc(U2, V2, d2))
  +R3 = R.Rat.add.value.mixed(P2, Q2, d2, pd2, pq2, np1, nn1, dp1)
  +eQi = Equal.trans(I.Int,
    R.Rat.num(P2, Q2),
    I.Int{P2, Nat.sub(Q2, P2)},
    I.Int{P2, Q2},
    Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(Q2, P2)}, Nat.sub(P2, Q2), P2,
      N.sub_diag(Nat.cmp(U2, V2), U2, V2, {==})),
    Equal.cong(Nat, I.Int, u => I.Int{P2, u}, Nat.sub(Q2, P2), Q2,
      N.sub_diag(Nat.cmp(V2, U2), V2, U2, {==})))
  +R4i = Equal.trans(I.Int,
    rawR,
    I.Int.add(I.Int.mul(I.Int{P2, Q2}, I.Int.unit(Xd)),
              I.Int.mul(I.Int{a1, b1}, I.Int.unit(d2))),
    I.Int{TRp, TRn},
    Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(u, I.Int.unit(Xd)),
        I.Int.mul(I.Int{a1, b1}, I.Int.unit(d2))),
      I.Int{Nat.sub(P2, Q2), Nat.sub(Q2, P2)}, I.Int{P2, Q2}, eQi),
    Equal.trans(I.Int,
      I.Int.add(I.Int.mul(I.Int{P2, Q2}, I.Int.unit(Xd)), I.Int.mul(I.Int{a1, b1}, I.Int.unit(d2))),
      I.Int.add(I.Int{Nat.mul(P2, Xd), Nat.mul(Q2, Xd)}, I.Int.mul(I.Int{a1, b1}, I.Int.unit(d2))),
      I.Int{TRp, TRn},
      Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(I.Int{a1, b1}, I.Int.unit(d2))),
        I.Int.mul(I.Int{P2, Q2}, I.Int.unit(Xd)), I.Int{Nat.mul(P2, Xd), Nat.mul(Q2, Xd)},
        I.Int.mul_scale(P2, Q2, Xd)),
      Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int{Nat.mul(P2, Xd), Nat.mul(Q2, Xd)}, u),
        I.Int.mul(I.Int{a1, b1}, I.Int.unit(d2)), I.Int{Nat.mul(a1, d2), Nat.mul(b1, d2)},
        I.Int.mul_scale(a1, b1, d2))))
  +R4 = Equal.trans(R.Rat,
    R.Rat.mk(rawR, Nat.mul(d2, Xd)),
    R.Rat.mk(I.Int{TRp, TRn}, Nat.mul(d2, Xd)),
    R.Rat.mk(I.Int{TRp, TRn}, D),
    Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(d2, Xd)), rawR, I.Int{TRp, TRn}, R4i),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int{TRp, TRn}, u), Nat.mul(d2, Xd), D,
      N.mul_comm(Nat.mul(Yd, Zd), Xd)))
  +eR = Equal.trans(R.Rat,
    R.Rat.add(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd})),
    R.Rat.add(R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd}), R.Rat{xn, Xd}),
    R.Rat.mk(I.Int{TRp, TRn}, D),
    R0,
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd}), R.Rat{xn, Xd}),
      R.Rat.add(M2, R.Rat{xn, Xd}),
      R.Rat.mk(I.Int{TRp, TRn}, D),
      R1,
      Equal.trans(R.Rat,
        R.Rat.add(M2, R.Rat{xn, Xd}),
        R.Rat.add(N2, R.Rat{xn, Xd}),
        R.Rat.mk(I.Int{TRp, TRn}, D),
        R2,
        Equal.trans(R.Rat, R.Rat.add(N2, R.Rat{xn, Xd}), R.Rat.mk(rawR, Nat.mul(d2, Xd)),
          R.Rat.mk(I.Int{TRp, TRn}, D), R3, R4))))
  +ee1 = N.sub_cross(Nat.cmp(U1, V1), U1, V1, {==})
  +ee2 = N.sub_cross(Nat.cmp(U2, V2), U2, V2, {==})
  +Hn = Rat.h.nat.cross4(P1, Q1, P2, Q2, a1, b1, a2, b2, a3, b3, Xd, Yd, Zd, ee1, ee2)
  +pD = N.mul_pos(Xd, Nat.mul(Yd, Zd), {==}, N.mul_pos(Yd, Zd, {==}, {==}))
  +val = R.Rat.mk.eqv.val(TLp, TLn, D, pD, TRp, TRn, D, pD, Hn)
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat.add(R.Rat{xn, Xd}, R.Rat{yn, Yd}), R.Rat{zn, Zd}),
    R.Rat.mk(I.Int{TLp, TLn}, D),
    R.Rat.add(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd})),
    eL,
    Equal.trans(R.Rat,
      R.Rat.mk(I.Int{TLp, TLn}, D),
      R.Rat.mk(I.Int{TRp, TRn}, D),
      R.Rat.add(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd})),
      val,
      Equal.sym(R.Rat, R.Rat.add(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd})),
        R.Rat.mk(I.Int{TRp, TRn}, D), eR)))

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
