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

# The operation-level surface: QExt.inv and QExt.div, and the two laws stated
# over them. The defs above spell the quotient as Rat.div inside a QExt
# constructor, which is the *value* form of the payoff; the operation is that
# same expression with a name on it. These defs are the check that the name
# unfolds to it -- QExt.div is not a second implementation, and the reason no
# `x/x = 1` law was added is visible here: the quotient unfolds to exactly the
# product QExt.mul_inv's conclusion is stated over, so a caller writes the
# quotient they want and cites that law.

# The operation's body at a variable value and a variable rational: a
# conversion, not a law, and the fact that keeps the two operation laws
# one-call fills.
def probe.op.unfold.inv(+x: Q.QExt, +q: R.Rat)
  -> {Q.QExt.inv(x, q)
      == Q.QExt{R.Rat.div(Q.QExt.re(x), q),
                R.Rat.div(R.Rat.neg(Q.QExt.im(x)), q)} : Q.QExt}:
  {==}

# x/x = 1, from the caller's side at a variable x, on each side of zero. The
# body is one call: this is QExt.mul_inv with the quotient written as a
# quotient. That is the whole content of the missing third law.
def probe.op.div.self.gt(+d: Nat, +x: Q.QExt,
                         +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                         +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                         +ap: Nat, +dp: Nat,
                         +hZ: {R.Rat.of(1n+ap, 0n, dp) == Q.QExt.norm(d, x) : R.Rat})
  -> {Q.QExt.div(d, x, x, R.Rat.of(1n+ap, 0n, dp)) == Q.QExt.one() : Q.QExt}:
  Q.QExt.mul_inv.gt(d, x, gx, hx, ap, dp, hZ)

def probe.op.div.self.lt(+d: Nat, +x: Q.QExt,
                         +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                         +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                         +bp: Nat, +dp: Nat,
                         +hZ: {R.Rat.of(0n, 1n+bp, dp) == Q.QExt.norm(d, x) : R.Rat})
  -> {Q.QExt.div(d, x, x, R.Rat.of(0n, 1n+bp, dp)) == Q.QExt.one() : Q.QExt}:
  Q.QExt.mul_inv.lt(d, x, gx, hx, bp, dp, hZ)

# (x + y)/z = x/z + y/z at variables. Six hypotheses, and none of them is about
# the quotient's own coordinates: the fill derives those inside (the reciprocal
# of a spelled rational has denominator 1n+ap, so its positivity is {==}).
def probe.op.div_add.gt(+d: Nat, +x: Q.QExt, +y: Q.QExt, +z: Q.QExt,
                        +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                        +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                        +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                        +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp},
                        +gz: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(z))) == LT{} : Cmp},
                        +hz: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(z))) == LT{} : Cmp},
                        +ap: Nat, +dp: Nat)
  -> {Q.QExt.div(d, Q.QExt.add(x, y), z, R.Rat.of(1n+ap, 0n, dp))
      == Q.QExt.add(Q.QExt.div(d, x, z, R.Rat.of(1n+ap, 0n, dp)),
                    Q.QExt.div(d, y, z, R.Rat.of(1n+ap, 0n, dp))) : Q.QExt}:
  Q.QExt.div_add.gt(d, x, y, z, gx, hx, gy, hy, gz, hz, ap, dp)

def probe.op.div_add.lt(+d: Nat, +x: Q.QExt, +y: Q.QExt, +z: Q.QExt,
                        +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                        +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                        +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                        +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp},
                        +gz: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(z))) == LT{} : Cmp},
                        +hz: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(z))) == LT{} : Cmp},
                        +bp: Nat, +dp: Nat)
  -> {Q.QExt.div(d, Q.QExt.add(x, y), z, R.Rat.of(0n, 1n+bp, dp))
      == Q.QExt.add(Q.QExt.div(d, x, z, R.Rat.of(0n, 1n+bp, dp)),
                    Q.QExt.div(d, y, z, R.Rat.of(0n, 1n+bp, dp))) : Q.QExt}:
  Q.QExt.div_add.lt(d, x, y, z, gx, hx, gy, hy, gz, hz, bp, dp)

# The operation at a canonical literal: (2 + sqrt 2)/(2 + sqrt 2) = 1, d = 2,
# norm 2. Everything here computes -- {==} closes it, as it closes the whole
# product in probe.cancel.instance's shape -- so this def is the arithmetic, not
# the law.
def probe.op.instance()
  -> {Q.QExt.div(2n,
        Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
        Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
        R.Rat.of(1n+1n, 0n, 0n))
      == Q.QExt.one() : Q.QExt}:
  {==}

# The field axiom (x/y)*y = x is not here yet, and the measurements say what
# shape it must take: at a canonical literal instance it closes by computation
# ({==}, measured), but at a variable dividend every route passes through
# x * 1 = x, and that step does not hold at non-canonical values -- the real
# coordinate of mul(x, one()) comes back normalized (Rat{Int{2,0},2} prints as
# Rat{Int{1,0},1} against an x that keeps Rat{Int{2,0},2}), measured. So the
# field axiom is stated over canonical spellings, the same way QExt.neg_neg and
# QExt.mul_one are, and x * 1 = x is no longer the gap: QExt.mul_one is in, with
# probe.mul_one above its caller's-side statement. What remains is the
# composition, one QExt.mul_inv call plus that law.

# QExt.mul_one from the caller's side, at a variable value: qrat.bend's own
# statement in the same spelling, and the body is one call. The two bridges are
# Rat.mul_one's hypothesis, one per coordinate -- the caller supplies them.
def probe.mul_one(+d: Nat, +np: Nat, +nn: Nat, +dp: Nat,
                  +mq: Nat, +mn: Nat, +dq: Nat,
                  +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                        == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat},
                  +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                        == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat})
  -> {Q.QExt.mul(d, Q.QExt.of(np, nn, dp, mq, mn, dq), Q.QExt.one())
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  Q.QExt.mul_one(d, np, nn, dp, mq, mn, dq, f1, f2)

# Where a downstream file has what QExt.neg_neg asks for -- coprimality of each
# coordinate -- the bridges are not extra hypotheses at all: Rat.mk.fixed is the
# step from gcd = 1 to mk(n,d) = Rat{n,d}, one call per coordinate, so a
# neg_neg-style caller reaches this law with nothing new to prove. That is why
# QExt.mul_one is stated on the bridges rather than on coprimality: a bridge is
# strictly weaker, and it is exactly what Rat.mul_one consumes.
def probe.mul_one.fixed(+d: Nat, +np: Nat, +nn: Nat, +dp: Nat,
                        +g: {N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp) == 1n : Nat},
                        +mq: Nat, +mn: Nat, +dq: Nat,
                        +h: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat})
  -> {Q.QExt.mul(d, Q.QExt.of(np, nn, dp, mq, mn, dq), Q.QExt.one())
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  +f1 = R.Rat.mk.fixed(Nat.cmp(np, nn), np, nn, dp, {==}, g)
  +f2 = R.Rat.mk.fixed(Nat.cmp(mq, mn), mq, mn, dq, {==}, h)
  Q.QExt.mul_one(d, np, nn, dp, mq, mn, dq, f1, f2)

# The arithmetic at 2 + sqrt 2: both denominators are base 1 and both numerators
# are integers, so every bridge is {==} and the product computes on its own --
# measured, {==} closes the whole goal and the law is not needed for it.
def probe.mul_one.instance()
  -> {Q.QExt.mul(2n,
        Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
        Q.QExt.one())
      == Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}} : Q.QExt}:
  {==}

# The field axiom, from the caller's side. QExt.div_mul_cancel.gt above is
# qrat.bend's own statement in the same spelling, and the body is one call --
# the law exists so that the composition (mul_assoc, then mul_comm under a cong,
# then mul_inv, then mul_one) is stated once instead of once per caller. x is
# canonical, so its two positivity facts are computed ({==}) and do not appear
# here; y is arbitrary, so both of its coordinates' positivity and the spelled
# norm are asked for, exactly as QExt.mul_inv asks for them.
def probe.div_mul_cancel.gt(+d: Nat,
                            +np: Nat, +nn: Nat, +dp: Nat,
                            +mq: Nat, +mn: Nat, +dq: Nat,
                            +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                                  == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat},
                            +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                                  == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat},
                            +y: Q.QExt,
                            +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                            +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp},
                            +ap: Nat, +ep: Nat,
                            +hZ: {R.Rat.of(1n+ap, 0n, ep) == Q.QExt.norm(d, y) : R.Rat})
  -> {Q.QExt.mul(d, Q.QExt.div(d, Q.QExt.of(np, nn, dp, mq, mn, dq), y,
                               R.Rat.of(1n+ap, 0n, ep)), y)
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  Q.QExt.div_mul_cancel.gt(d, np, nn, dp, mq, mn, dq, f1, f2, y, gy, hy, ap, ep, hZ)

# The LT twin: one law per sign of the norm's spelling, and the negative case is
# not optional -- an extension whose norm is negative has no positive raw pair at
# all (1 + 2*sqrt 3 has norm -11), so a GT-only pair of laws would not state the
# field axiom for it.
def probe.div_mul_cancel.lt(+d: Nat,
                            +np: Nat, +nn: Nat, +dp: Nat,
                            +mq: Nat, +mn: Nat, +dq: Nat,
                            +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                                  == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat},
                            +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                                  == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat},
                            +y: Q.QExt,
                            +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                            +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp},
                            +bp: Nat, +ep: Nat,
                            +hZ: {R.Rat.of(0n, 1n+bp, ep) == Q.QExt.norm(d, y) : R.Rat})
  -> {Q.QExt.mul(d, Q.QExt.div(d, Q.QExt.of(np, nn, dp, mq, mn, dq), y,
                               R.Rat.of(0n, 1n+bp, ep)), y)
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  Q.QExt.div_mul_cancel.lt(d, np, nn, dp, mq, mn, dq, f1, f2, y, gy, hy, bp, ep, hZ)

# The arithmetic: 1/(2 + sqrt 2) times (2 + sqrt 2). x is 1, the norm of
# 2 + sqrt 2 is 4 - 2 = 2, so the spelled divisor is of(1 + ap, 0, ep) at
# ap = 1, ep = 0, and every hypothesis is {==} -- the bounds compute, the norm
# identity computes, and both bridges are base cases. Measurement, as with
# probe.mul_one.instance: at literals the whole product also reduces on its own,
# so {==} closes this goal and the law is not needed for it. What exercises the
# law is the variable defs above; this one is the arithmetic check.
def probe.div_mul_cancel.instance()
  -> {Q.QExt.mul(2n,
        Q.QExt.div(2n, Q.QExt.of(1n, 0n, 0n, 0n, 0n, 0n),
          Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
          R.Rat.of(1n+1n, 0n, 0n)),
        Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}})
      == Q.QExt.of(1n, 0n, 0n, 0n, 0n, 0n) : Q.QExt}:
  {==}

# The additive identity and inverse, from the caller's side -- qrat.bend's own
# statements in the same spellings, each body one call, so an implicit argument
# that stops being inferable fails here first. The two identity laws take the
# same canonical presentation and the same two bridges QExt.mul_one takes;
# QExt.add_neg takes neither, and gets the coefficients' positivity instead.
def probe.add_zero(+np: Nat, +nn: Nat, +dp: Nat,
                   +mq: Nat, +mn: Nat, +dq: Nat,
                   +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                         == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat},
                   +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                         == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat})
  -> {Q.QExt.add(Q.QExt.of(np, nn, dp, mq, mn, dq), Q.QExt.zero())
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  Q.QExt.add_zero(np, nn, dp, mq, mn, dq, f1, f2)

def probe.zero_add(+np: Nat, +nn: Nat, +dp: Nat,
                   +mq: Nat, +mn: Nat, +dq: Nat,
                   +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                         == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat},
                   +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                         == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat})
  -> {Q.QExt.add(Q.QExt.zero(), Q.QExt.of(np, nn, dp, mq, mn, dq))
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  Q.QExt.zero_add(np, nn, dp, mq, mn, dq, f1, f2)

def probe.add_neg(+x: Q.QExt,
                  +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                  +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp})
  -> {Q.QExt.add(x, Q.QExt.neg(x)) == Q.QExt.zero() : Q.QExt}:
  Q.QExt.add_neg(x, gx, hx)

# The payoff of add_neg: QExt.sub is a definition (x + (-y)), so the difference
# of a value with itself is the additive inverse law at work -- and the goal here
# is stated with QExt.sub, which the law's conclusion reaches by conversion
# alone. That is the shape a caller writing x - x actually has.
def probe.add_neg.sub_self(+x: Q.QExt,
                           +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                           +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp})
  -> {Q.QExt.sub(x, x) == Q.QExt.zero() : Q.QExt}:
  Q.QExt.add_neg(x, gx, hx)

# The arithmetic at 2 + sqrt 2, where every denominator is base 1: (2 + sqrt 2)
# + 0 = 2 + sqrt 2, and the same measurement note as the other literal instances
# -- the coordinates are canonical and the sum reduces on its own, so {==} closes
# it and the law is not needed for the instance.
def probe.add_zero.instance()
  -> {Q.QExt.add(Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
                 Q.QExt.zero())
      == Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}} : Q.QExt}:
  {==}

# The negation and conjugation laws, from the caller's side -- qrat.bend's own
# statements in the same spellings, each body one call, so an implicit argument
# that stops being inferable fails here first. These five are the arbitrary-value
# laws, and the hypotheses they take are the ones the Rat laws underneath them
# need, not more: the sum laws ask for their *summands*' positivity and never for
# the sum's, and the conjugate's involution asks for the imaginary coordinate's
# coprimality alone (the real coordinate is carried through untouched).
def probe.neg_add(+x: Q.QExt, +y: Q.QExt,
                  +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                  +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                  +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                  +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp})
  -> {Q.QExt.neg(Q.QExt.add(x, y)) == Q.QExt.add(Q.QExt.neg(x), Q.QExt.neg(y)) : Q.QExt}:
  Q.QExt.neg_add(x, y, gx, gy, hx, hy)

# The same law read backwards, which is how a caller who *has* a sum of negations
# reaches the negation of the sum: one Equal.sym, since the law is an equation and
# not a rewrite. Nothing else here -- the point is that the orientation a caller
# needs is not baked into the statement.
def probe.neg_add.out(+x: Q.QExt, +y: Q.QExt,
                      +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                      +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                      +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                      +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp})
  -> {Q.QExt.add(Q.QExt.neg(x), Q.QExt.neg(y)) == Q.QExt.neg(Q.QExt.add(x, y)) : Q.QExt}:
  Equal.sym(Q.QExt, Q.QExt.neg(Q.QExt.add(x, y)),
    Q.QExt.add(Q.QExt.neg(x), Q.QExt.neg(y)),
    Q.QExt.neg_add(x, y, gx, gy, hx, hy))

def probe.mul_neg(+d: Nat, +x: Q.QExt, +y: Q.QExt,
                  +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                  +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                  +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                  +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp})
  -> {Q.QExt.mul(d, x, Q.QExt.neg(y)) == Q.QExt.neg(Q.QExt.mul(d, x, y)) : Q.QExt}:
  Q.QExt.mul_neg(d, x, y, gx, hx, gy, hy)

def probe.neg_mul(+d: Nat, +x: Q.QExt, +y: Q.QExt,
                  +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                  +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                  +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                  +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp})
  -> {Q.QExt.mul(d, Q.QExt.neg(x), y) == Q.QExt.neg(Q.QExt.mul(d, x, y)) : Q.QExt}:
  Q.QExt.neg_mul(d, x, y, gx, hx, gy, hy)

def probe.conj_add(+x: Q.QExt, +y: Q.QExt,
                   +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                   +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp})
  -> {Q.QExt.conj(Q.QExt.add(x, y))
      == Q.QExt.add(Q.QExt.conj(x), Q.QExt.conj(y)) : Q.QExt}:
  Q.QExt.conj_add(x, y, hx, hy)

# The involution at the law's own presentation, and the caller's-side statement of
# what a downstream file has: coprimality of the imaginary coordinate, which
# Rat.mk.fixed turns into the bridge that spelling needs -- not asked for here,
# exactly as in qrat.bend, because the real coordinate never enters a gcd.
def probe.conj_conj(+np: Nat, +nn: Nat, +dp: Nat,
                    +mq: Nat, +mn: Nat, +dq: Nat,
                    +h: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat})
  -> {Q.QExt.conj(Q.QExt.conj(Q.QExt.of(np, nn, dp, mq, mn, dq)))
      == Q.QExt.of(np, nn, dp, mq, mn, dq) : Q.QExt}:
  Q.QExt.conj_conj(np, nn, dp, mq, mn, dq, h)

# The arithmetic at 1 + sqrt 2: conj(conj(x)) = x with every implicit argument
# inferred at a concrete instance (dq = 1 makes the imaginary denominator 1 + 1,
# so the coprimality gcd(1, 2) = 1 computes and the evidence is {==}).
def probe.conj_conj.instance()
  -> {Q.QExt.conj(Q.QExt.conj(
        Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}))
      == Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}} : Q.QExt}:
  {==}

# The multiplicativity law, reached from the caller's side. The statement below is
# the spelled one the law used to carry, which is now its instance: x and y are
# QExt.of's six-coordinate values, so the law's four positivity hypotheses and the
# two naming its imaginary coefficients are all `{==}`, and only the coprimality
# carries over. That is what the restatement buys -- the same fact, at a price the
# checker can pay (PROVING.md, round thirteen).
def probe.conj_mul(+d: Nat, +np: Nat, +nn: Nat, +dp: Nat,
                   +mq: Nat, +mn: Nat, +dq: Nat,
                   +rp: Nat, +rn: Nat, +dr: Nat,
                   +sp: Nat, +sn: Nat, +ds: Nat,
                   +h1: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat},
                   +h2: {N.Nat.gcd(R.Rat.mag(sp, sn), 1n+ds) == 1n : Nat})
  -> {Q.QExt.conj(Q.QExt.mul(d, Q.QExt.of(np, nn, dp, mq, mn, dq),
                               Q.QExt.of(rp, rn, dr, sp, sn, ds)))
      == Q.QExt.mul(d, Q.QExt.conj(Q.QExt.of(np, nn, dp, mq, mn, dq)),
                       Q.QExt.conj(Q.QExt.of(rp, rn, dr, sp, sn, ds))) : Q.QExt}:
  Q.QExt.conj_mul(d, Q.QExt.of(np, nn, dp, mq, mn, dq),
    Q.QExt.of(rp, rn, dr, sp, sn, ds),
    mq, mn, dq, sp, sn, ds,
    {==}, {==}, {==}, {==}, {==}, {==}, h1, h2)

# The arithmetic at 1 + sqrt 2: same instance as conj_conj.instance, with the
# radicand 2 and both operands equal. mag(1, 0) = 1 against the denominator
# 1 + 1 = 2, so both coprimality gcds compute and both pieces of evidence are
# {==} -- the law applies with nothing left for a caller to derive.
def probe.conj_mul.instance()
  -> {Q.QExt.conj(Q.QExt.mul(2n,
        Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}},
        Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}))
      == Q.QExt.mul(2n,
        Q.QExt.conj(Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}),
        Q.QExt.conj(Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}})) : Q.QExt}:
  Q.QExt.conj_mul(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}},
      1n, 0n, 1n, 1n, 0n, 1n,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# The norm's multiplicativity, reached from the caller's side. This law's
# hypotheses are the point of its statement: x and y arbitrary, the three norms
# *named* instead of written out (hnx/hny/hnxy), the product's own coordinates'
# positivity handed over (gxy/hxy), and the conj_mul instance supplied (hc)
# rather than derived. Each of those is a fact about a term that does not reduce,
# so a caller always holds them already -- and writing them out is exactly what
# made an earlier draft of the fill uncheckable.
def probe.norm.mul(+d: Nat, +x: Q.QExt, +y: Q.QExt,
                   +nx: R.Rat, +ny: R.Rat, +nxy: R.Rat,
                   +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                   +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                   +gy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(y))) == LT{} : Cmp},
                   +hy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(y))) == LT{} : Cmp},
                   +gxy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(Q.QExt.mul(d, x, y)))) == LT{} : Cmp},
                   +hxy: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(Q.QExt.mul(d, x, y)))) == LT{} : Cmp},
                   +hnx: {nx == Q.QExt.norm(d, x) : R.Rat},
                   +hny: {ny == Q.QExt.norm(d, y) : R.Rat},
                   +hnxy: {nxy == Q.QExt.norm(d, Q.QExt.mul(d, x, y)) : R.Rat},
                   +hc: {Q.QExt.conj(Q.QExt.mul(d, x, y))
                         == Q.QExt.mul(d, Q.QExt.conj(x), Q.QExt.conj(y)) : Q.QExt})
  -> {Q.QExt.emb(nxy) == Q.QExt.mul(d, Q.QExt.emb(nx), Q.QExt.emb(ny)) : Q.QExt}:
  Q.QExt.norm.mul(d, x, y, nx, ny, nxy, gx, hx, gy, hy, gxy, hxy, hnx, hny, hnxy, hc)

# The arithmetic at 1 + sqrt 2 with radicand 2: norm(1 + sqrt 2) = 1 - 2 = -1,
# the square (1 + sqrt 2)^2 = 3 + 2 sqrt 2 has norm 9 - 8 = 1, and (-1)*(-1) = 1.
# Every hypothesis the law asks for is {==} here -- the values are concrete, so
# each named norm, each positivity, and the conj_mul instance all compute. The
# conj_mul instance is passed as the law's own instance rather than as {==},
# since that is what a caller composing the two laws writes.
def probe.norm.mul.instance()
  -> {Q.QExt.emb(Q.QExt.norm(2n, Q.QExt.mul(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}})))
      == Q.QExt.mul(2n,
        Q.QExt.emb(Q.QExt.norm(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}})),
        Q.QExt.emb(Q.QExt.norm(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}))) : Q.QExt}:
  Q.QExt.norm.mul(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}},
    Q.QExt.norm(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}),
    Q.QExt.norm(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}),
    Q.QExt.norm(2n, Q.QExt.mul(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}})),
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    Q.QExt.conj_mul(2n, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}}, Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n+1n}},
      1n, 0n, 1n, 1n, 0n, 1n,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))

# QExt.mul_zero and QExt.mul_eq_zero from a caller's side. The zero-divisor law
# is the last one the roadmap was waiting on, so it gets both shapes: the law
# over its own sixteen hypotheses, and an instance where every hypothesis is
# `{==}` -- including hz, which needs the product to compute to QExt.zero().

def probe.use.mul_zero(+d: Nat, +x: Q.QExt,
                       +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                       +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp})
  -> {Q.QExt.mul(d, Q.QExt.zero(), x) == Q.QExt.zero() : Q.QExt}:
  Q.QExt.mul_zero(d, x, gx, hx)

def probe.use.mul_eq_zero(+d: Nat,
                          +np: Nat, +nn: Nat, +dp: Nat,
                          +mq: Nat, +mn: Nat, +dq: Nat,
                          +f1: {R.Rat.mk(R.Rat.num(np, nn), 1n+dp)
                                == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat},
                          +f2: {R.Rat.mk(R.Rat.num(mq, mn), 1n+dq)
                                == R.Rat{R.Rat.num(mq, mn), 1n+dq} : R.Rat},
                          +x: Q.QExt,
                          +gx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(x))) == LT{} : Cmp},
                          +hx: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(x))) == LT{} : Cmp},
                          +zi: Q.QExt,
                          +hi: {Q.QExt.mul(d, x, zi) == Q.QExt.one() : Q.QExt},
                          +gzi: {Nat.cmp(0n, R.Rat.denof(Q.QExt.re(zi))) == LT{} : Cmp},
                          +hzi: {Nat.cmp(0n, R.Rat.denof(Q.QExt.im(zi))) == LT{} : Cmp},
                          +hz: {Q.QExt.mul(d, x, Q.QExt.of(np, nn, dp, mq, mn, dq))
                                == Q.QExt.zero() : Q.QExt})
  -> {Q.QExt.of(np, nn, dp, mq, mn, dq) == Q.QExt.zero() : Q.QExt}:
  Q.QExt.mul_eq_zero(d, np, nn, dp, mq, mn, dq, f1, f2, x, gx, hx, zi, hi, gzi, hzi, hz)

# 1 + sqrt 2 over radicand 2 has inverse -1 + sqrt 2, since (1+x)(-1+x) = x^2 - 1
# = 1. The zero factor is spelled QExt.of(0,0,0,0,0,0) -- the canonical zero
# written through the six-coordinate spelling, which is what makes the
# conclusion (not the hypothesis) the thing the chain has to reach.
def probe.mul_eq_zero.instance()
  -> {Q.QExt.of(0n, 0n, 0n, 0n, 0n, 0n) == Q.QExt.zero() : Q.QExt}:
  Q.QExt.mul_eq_zero(2n, 0n, 0n, 0n, 0n, 0n, 0n,
    {==}, {==},
    Q.QExt{R.Rat{I.Int{1n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
    {==}, {==},
    Q.QExt{R.Rat{I.Int{0n, 1n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
    {==}, {==}, {==},
    {==})

# The hypothesis is not cosmetic. At d = 4 the element -2 + sqrt 4 has norm
# 4 - 4 = 0, and it is a genuine zero divisor: (-2 + x)(2 + x) = x^2 - 4 = 0 at
# x^2 = 4. Neither factor is zero (their real coordinates are -2 and 2), so with
# norm(x) = 0 the conclusion y = 0 is simply false and QExt.mul_eq_zero must say
# nothing -- which is why the law carries the inverse as a hypothesis instead.
def probe.zero_divisor.d4()
  -> {Q.QExt.mul(4n,
        Q.QExt{R.Rat{I.Int{0n, 2n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}},
        Q.QExt{R.Rat{I.Int{2n, 0n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}})
      == Q.QExt.zero() : Q.QExt}:
  {==}

def probe.zero_divisor.d4.norm()
  -> {Q.QExt.norm(4n,
        Q.QExt{R.Rat{I.Int{0n, 2n}, 1n}, R.Rat{I.Int{1n, 0n}, 1n}})
      == R.Rat.zero() : R.Rat}:
  {==}

# The norm and conjugation identities from a caller's side, plus the boundary
# instances cited from a consumer and one literal instance of the invariance.

def probe.use.conj_neg(+x: Q.QExt)
  -> {Q.QExt.conj(Q.QExt.neg(x)) == Q.QExt.neg(Q.QExt.conj(x)) : Q.QExt}:
  Q.QExt.conj_neg(x)

def probe.use.norm.zero(+d: Nat)
  -> {Q.QExt.norm(d, Q.QExt.zero()) == R.Rat.zero() : R.Rat}:
  Q.QExt.norm.zero(d)

def probe.use.norm.one(+d: Nat)
  -> {Q.QExt.norm(d, Q.QExt.one()) == R.Rat.one() : R.Rat}:
  Q.QExt.norm.one(d)

def probe.use.norm.conj(+d: Nat, +x: Q.QExt,
                        +mq: Nat, +mn: Nat, +dq: Nat,
                        +him: {Q.QExt.im(x) == R.Rat.of(mq, mn, dq) : R.Rat},
                        +h: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat})
  -> {Q.QExt.norm(d, Q.QExt.conj(x)) == Q.QExt.norm(d, x) : R.Rat}:
  Q.QExt.norm.conj(d, x, mq, mn, dq, him, h)

def probe.use.norm.neg(+d: Nat, +x: Q.QExt,
                       +np: Nat, +nn: Nat, +dp: Nat,
                       +hre: {Q.QExt.re(x) == R.Rat.of(np, nn, dp) : R.Rat},
                       +g: {N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp) == 1n : Nat},
                       +mq: Nat, +mn: Nat, +dq: Nat,
                       +him: {Q.QExt.im(x) == R.Rat.of(mq, mn, dq) : R.Rat},
                       +h: {N.Nat.gcd(R.Rat.mag(mq, mn), 1n+dq) == 1n : Nat})
  -> {Q.QExt.norm(d, Q.QExt.neg(x)) == Q.QExt.norm(d, x) : R.Rat}:
  Q.QExt.norm.neg(d, x, np, nn, dp, hre, g, mq, mn, dq, him, h)

# The spelled statement is the instance: at x := QExt.of's six coordinates both
# naming hypotheses are `{==}`, which is what the restatement moved out of the
# law and into the caller. norm(2, 1 + sqrt 2) = norm(2, -1 - sqrt 2) = -1.
def probe.norm.neg.instance()
  -> {Q.QExt.norm(2n, Q.QExt.neg(Q.QExt{R.Rat.of(1n, 0n, 0n), R.Rat.of(1n, 0n, 0n)}))
      == Q.QExt.norm(2n, Q.QExt{R.Rat.of(1n, 0n, 0n), R.Rat.of(1n, 0n, 0n)}) : R.Rat}:
  Q.QExt.norm.neg(2n, Q.QExt{R.Rat.of(1n, 0n, 0n), R.Rat.of(1n, 0n, 0n)},
    1n, 0n, 0n, {==}, {==}, 1n, 0n, 0n, {==}, {==})

# The boundary, cited rather than re-proved: -2 + sqrt 4 is a genuine zero
# divisor over radicand 4 and its norm is zero.
def probe.zero_divisor.law()
  -> {Q.QExt.mul(4n,
        Q.QExt{R.Rat.of(0n, 2n, 0n), R.Rat.of(1n, 0n, 0n)},
        Q.QExt{R.Rat.of(2n, 0n, 0n), R.Rat.of(1n, 0n, 0n)})
      == Q.QExt.zero() : Q.QExt}:
  Q.QExt.zero_divisor.d4()

def probe.zero_divisor.law.norm()
  -> {Q.QExt.norm(4n, Q.QExt{R.Rat.of(0n, 2n, 0n), R.Rat.of(1n, 0n, 0n)})
      == R.Rat.zero() : R.Rat}:
  Q.QExt.zero_divisor.d4.norm()
