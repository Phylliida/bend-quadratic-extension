import Base
import ./src/nat.bend as N
import ./src/nat_proofs.bend as NP
import ./src/int.bend as I
import ./src/int_proofs.bend as IP
import ./src/rat.bend as R
import ./src/rat_proofs.bend as RP

# Consumer check for the division laws. Every def here is written the way a
# downstream file would write it -- the conclusion spelled from the caller's
# side, the body a call to the published name -- so this is the test that the
# laws can actually be *used*, not just that their fills are closed. The last
# def is a fact that is not one of the ten: it composes Rat.div_add with
# Rat.div_one, which is what a consumer does with them.

# the value form, positive divisor, spelled out from the caller's side
def probe.use.div.value.gt(+ap: Nat, +dp: Nat, +Zp: Nat, +Zn: Nat, +D: Nat)
  -> {R.Rat.div(R.Rat{I.Int{Zp, Zn}, D}, R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp})
      == R.Rat.mk(I.Int.mul(I.Int{Zp, Zn}, R.Rat.num(1n+dp, 0n)),
                  Nat.mul(D, 1n+ap)) : R.Rat}:
  R.Rat.div.value.gt(ap, dp, Zp, Zn, D)

# the same at literals, to check that the arguments really are inferable
def probe.use.div.value.lt.lit()
  -> {R.Rat.div(R.Rat{I.Int{7n, 2n}, 11n}, R.Rat{R.Rat.num(0n, 1n+4n), 1n+5n})
      == R.Rat.mk(I.Int.mul(I.Int{7n, 2n}, R.Rat.num(0n, 1n+5n)),
                  Nat.mul(11n, 1n+4n)) : R.Rat}:
  R.Rat.div.value.lt(4n, 5n, 7n, 2n, 11n)

def probe.use.div.value.eq(+dp: Nat, +Zp: Nat, +Zn: Nat, +D: Nat)
  -> {R.Rat.div(R.Rat{I.Int{Zp, Zn}, D}, R.Rat{R.Rat.num(0n, 0n), 1n+dp})
      == R.Rat.mk(I.Int.mul(I.Int{Zp, Zn}, R.Rat.num(0n, 0n)),
                  Nat.mul(D, 0n)) : R.Rat}:
  R.Rat.div.value.eq(dp, Zp, Zn, D)

def probe.use.div_self.gt(+ap: Nat, +dp: Nat)
  -> {R.Rat.div(R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp},
                R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}) == R.Rat.one() : R.Rat}:
  R.Rat.div_self.gt(ap, dp)

def probe.use.div_self.lt.lit()
  -> {R.Rat.div(R.Rat{R.Rat.num(0n, 1n+6n), 1n+2n},
                R.Rat{R.Rat.num(0n, 1n+6n), 1n+2n}) == R.Rat.one() : R.Rat}:
  R.Rat.div_self.lt(6n, 2n)

def probe.use.div_one(+n: I.Int, +d: Nat,
                      +fx: {R.Rat.mk(n, d) == R.Rat{n, d} : R.Rat})
  -> {R.Rat.div(R.Rat{n, d}, R.Rat.one()) == R.Rat{n, d} : R.Rat}:
  R.Rat.div_one(n, d, fx)

def probe.use.div_mul_cancel.gt(+ap: Nat, +dp: Nat, +n: I.Int, +d: Nat,
                                +fx: {R.Rat.mk(n, d) == R.Rat{n, d} : R.Rat},
                                +pd: {Nat.cmp(0n, d) == LT{} : Cmp})
  -> {R.Rat.mul(R.Rat.div(R.Rat{n, d}, R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}),
                R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}) == R.Rat{n, d} : R.Rat}:
  R.Rat.div_mul_cancel.gt(ap, dp, n, d, fx, pd)

def probe.use.div_mul_cancel.lt(+bp: Nat, +dp: Nat, +n: I.Int, +d: Nat,
                                +fx: {R.Rat.mk(n, d) == R.Rat{n, d} : R.Rat},
                                +pd: {Nat.cmp(0n, d) == LT{} : Cmp})
  -> {R.Rat.mul(R.Rat.div(R.Rat{n, d}, R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}),
                R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}) == R.Rat{n, d} : R.Rat}:
  R.Rat.div_mul_cancel.lt(bp, dp, n, d, fx, pd)

def probe.use.div_add.gt(+ap: Nat, +dp: Nat, +x: R.Rat, +y: R.Rat,
                         +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp},
                         +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp})
  -> {R.Rat.div(R.Rat.add(x, y), R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp})
      == R.Rat.add(R.Rat.div(x, R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp}),
                   R.Rat.div(y, R.Rat{R.Rat.num(1n+ap, 0n), 1n+dp})) : R.Rat}:
  R.Rat.div_add.gt(ap, dp, x, y, px, py)

def probe.use.div_add.lt(+bp: Nat, +dp: Nat, +x: R.Rat, +y: R.Rat,
                         +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp},
                         +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp})
  -> {R.Rat.div(R.Rat.add(x, y), R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp})
      == R.Rat.add(R.Rat.div(x, R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp}),
                   R.Rat.div(y, R.Rat{R.Rat.num(0n, 1n+bp), 1n+dp})) : R.Rat}:
  R.Rat.div_add.lt(bp, dp, x, y, px, py)

# (x + y) / 1 = x + y -- not one of the laws: Rat.div_add.gt at the divisor 1
# (where Nat.cmp computes, so no branch hypothesis is needed) followed by
# Rat.div_one under two congruences. The first step is the interesting one,
# because it is where div_add's divisor instance has to be convertible to
# Rat.one() for the law to reach a goal stated with the constructor.
def probe.derived.div_add.one(+n1: I.Int, +d1: Nat, +n2: I.Int, +d2: Nat,
                              +f1: {R.Rat.mk(n1, d1) == R.Rat{n1, d1} : R.Rat},
                              +f2: {R.Rat.mk(n2, d2) == R.Rat{n2, d2} : R.Rat},
                              +p1: {Nat.cmp(0n, d1) == LT{} : Cmp},
                              +p2: {Nat.cmp(0n, d2) == LT{} : Cmp})
  -> {R.Rat.div(R.Rat.add(R.Rat{n1, d1}, R.Rat{n2, d2}), R.Rat.one())
      == R.Rat.add(R.Rat{n1, d1}, R.Rat{n2, d2}) : R.Rat}:
  Equal.trans(R.Rat,
    R.Rat.div(R.Rat.add(R.Rat{n1, d1}, R.Rat{n2, d2}), R.Rat.one()),
    R.Rat.add(R.Rat.div(R.Rat{n1, d1}, R.Rat.one()),
              R.Rat.div(R.Rat{n2, d2}, R.Rat.one())),
    R.Rat.add(R.Rat{n1, d1}, R.Rat{n2, d2}),
    R.Rat.div_add.gt(0n, 0n, R.Rat{n1, d1}, R.Rat{n2, d2}, p1, p2),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.div(R.Rat{n1, d1}, R.Rat.one()),
                R.Rat.div(R.Rat{n2, d2}, R.Rat.one())),
      R.Rat.add(R.Rat{n1, d1}, R.Rat.div(R.Rat{n2, d2}, R.Rat.one())),
      R.Rat.add(R.Rat{n1, d1}, R.Rat{n2, d2}),
      Equal.cong(R.Rat, R.Rat,
        u => R.Rat.add(u, R.Rat.div(R.Rat{n2, d2}, R.Rat.one())),
        R.Rat.div(R.Rat{n1, d1}, R.Rat.one()), R.Rat{n1, d1},
        R.Rat.div_one(n1, d1, f1)),
      Equal.cong(R.Rat, R.Rat,
        u => R.Rat.add(R.Rat{n1, d1}, u),
        R.Rat.div(R.Rat{n2, d2}, R.Rat.one()), R.Rat{n2, d2},
        R.Rat.div_one(n2, d2, f2))))

# Rat.zero_mul and Rat.mul_eq_zero from the caller's side: hypotheses in,
# conclusion out, exactly as a downstream file would write them.

def probe.use.zero_mul(+x: R.Rat, +px: {Nat.cmp(0n, R.Rat.denof(x)) == LT{} : Cmp})
  -> {R.Rat.mul(R.Rat.zero(), x) == R.Rat.zero() : R.Rat}:
  R.Rat.zero_mul(x, px)

def probe.use.zero_mul.lit()
  -> {R.Rat.mul(R.Rat.zero(), R.Rat{R.Rat.num(3n, 1n), 1n+1n}) == R.Rat.zero() : R.Rat}:
  R.Rat.zero_mul(R.Rat{R.Rat.num(3n, 1n), 1n+1n}, {==})

def probe.use.mul_eq_zero(+n: I.Int, +d: Nat,
                          +fx: {R.Rat.mk(n, d) == R.Rat{n, d} : R.Rat},
                          +pd: {Nat.cmp(0n, d) == LT{} : Cmp},
                          +y: R.Rat,
                          +py: {Nat.cmp(0n, R.Rat.denof(y)) == LT{} : Cmp},
                          +q: R.Rat,
                          +pq: {Nat.cmp(0n, R.Rat.denof(q)) == LT{} : Cmp},
                          +hq: {R.Rat.mul(y, q) == R.Rat.one() : R.Rat},
                          +hz: {R.Rat.mul(R.Rat{n, d}, y) == R.Rat.zero() : R.Rat})
  -> {R.Rat{n, d} == R.Rat.zero() : R.Rat}:
  R.Rat.mul_eq_zero(n, d, fx, pd, y, py, q, pq, hq, hz)

