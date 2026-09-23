import Base
import ./src/nat.bend as N
import ./src/int.bend as I
import ./src/rat.bend as R
import ./src/qrat.bend as Q
import ./src/nat_proofs.bend as NP
import ./src/int_proofs.bend as IP
import ./src/rat_proofs.bend as RP
import ./src/qrat_proofs.bend as QP

# Consumer check for the division payoff, QExt.inv.value.gt / .lt:
#
#     1/x = conj(x)/norm(d,x),   x = a + b*sqrt(d)
#
# written the way a downstream file would write it -- the conclusion spelled
# from the caller's side, the body a call to the published name. The first two
# defs record the conversion the whole design rests on; the last two are the
# arithmetic itself, at a concrete x on each side of zero, where the left-hand
# side really does compute to 1.

# The divisor's sign in the spelling is what makes Rat.div usable: at a
# *variable* dividend it already unfolds to mul(a, reciprocal), no law and no
# rewrite, because the Nat.cmp inside Rat.inv's argument list computes on
# constructors. This is the fact that keeps every fill in the payoff a
# rearrangement of products.
def probe.unfold.div.pos(+a: R.Rat, +ap: Nat, +dp: Nat)
  -> {R.Rat.div(a, R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp})
      == R.Rat.mul(a, R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap}) : R.Rat}:
  {==}

# The negative spelling, where the reciprocal is the *other* raw shape: not
# Rat{Rat.num(1n+dp, 0n), 1n+ap} with a coordinate flipped but
# Rat{Rat.num(0n, 1n+dp), 1n+bp} (round four measured that; the LT payoff fill
# closing against Rat.mul_inv.lt depends on it).
def probe.unfold.div.neg(+a: R.Rat, +bp: Nat, +dp: Nat)
  -> {R.Rat.div(a, R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp})
      == R.Rat.mul(a, R.Rat{R.Rat.num(0n, 1n+dp), 1n+bp}) : R.Rat}:
  {==}

# The law from the caller's side, at a variable x: the same statement qrat.bend
# makes, reached through the published name. A consumer with a positive norm
# spelled as (1+ap)/(1+dp) needs nothing else -- gx, hx and hZ are {==} at any
# canonical call site.
def probe.payoff.gt(+d: Nat, +x: Q.QExt,
                    +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                    +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                    +ap: Nat, +dp: Nat,
                    +hZ: {R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}
                          == Q.QExt.norm(d, x) : R.Rat})
  -> {Q.QExt.mul(d, x,
        Q.QExt{R.Rat.div(Q.QExt.re(x), R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}),
               R.Rat.div(R.Rat.neg(Q.QExt.im(x)),
                         R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp})})
      == Q.QExt.one() : Q.QExt}:
  Q.QExt.inv.value.gt(d, x, gx, hx, ap, dp, hZ)

# The arithmetic: 1/(2 + sqrt 2) = (2 - sqrt 2)/2. The norm of 2 + sqrt 2 is
# 4 - 2 = 2, which is the divisor spelling at ap = 1, dp = 0, so every
# hypothesis is {==}. At literals the whole product also reduces on its own --
# measured, {==} closes this same goal -- so what this def adds over the
# variable one is only that the published name is callable at a concrete
# instance with every implicit argument inferred.
def probe.payoff.instance()
  -> {Q.QExt.mul(2n,
        Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
        Q.QExt{R.Rat.div(R.Rat{I.Int{2n, 0n}, 1n},
                         R.Rat{R.Rat.num(1n+1n, 0n), 1n+0n}),
               R.Rat.div(R.Rat.neg(R.Rat{I.Int{1n, 0n}, 1n}),
                         R.Rat{R.Rat.num(1n+1n, 0n), 1n+0n})})
      == Q.QExt.one() : Q.QExt}:
  Q.QExt.inv.value.gt(2n,
    Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
    {==}, {==}, 1n, 0n, {==})

# The law from the caller's side on the other side of zero, at a variable x.
def probe.payoff.lt(+d: Nat, +x: Q.QExt,
                    +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                    +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                    +bp: Nat, +dp: Nat,
                    +hZ: {R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}
                          == Q.QExt.norm(d, x) : R.Rat})
  -> {Q.QExt.mul(d, x,
        Q.QExt{R.Rat.div(Q.QExt.re(x), R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}),
               R.Rat.div(R.Rat.neg(Q.QExt.im(x)),
                         R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp})})
      == Q.QExt.one() : Q.QExt}:
  Q.QExt.inv.value.lt(d, x, gx, hx, bp, dp, hZ)

# The arithmetic, on the negative side: 1/(1 + 2*sqrt 3) = (1 - 2*sqrt 3)/(-11).
# The norm of 1 + 2*sqrt 3 is 1 - 12 = -11, the divisor spelling at bp = 10,
# dp = 0, so again every hypothesis is {==}. This is the case the GT law cannot
# state at all -- there is no positive raw pair equal to -11 -- and round five
# measured what happens when the sign is forced: the same product built against
# the positive spelling 11 comes out -1.
def probe.payoff.instance.lt()
  -> {Q.QExt.mul(3n,
        Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{2n, 0n}, 1n}},
        Q.QExt{R.Rat.div(R.Rat{I.Int{1n, 0n}, 1n},
                         R.Rat{R.Rat.num(0n, 1n+10n), 1n+0n}),
               R.Rat.div(R.Rat.neg(R.Rat{I.Int{2n, 0n}, 1n}),
                         R.Rat{R.Rat.num(0n, 1n+10n), 1n+0n})})
      == Q.QExt.one() : Q.QExt}:
  Q.QExt.inv.value.lt(3n,
    Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{2n, 0n}, 1n}},
    {==}, {==}, 10n, 0n, {==})
