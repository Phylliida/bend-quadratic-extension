import Base
import ./rat.bend as R
import ./int.bend as I
import ./int_proofs.bend as IP
import ./nat.bend as N
import ./nat_proofs.bend as NP

# Rat proofs
# ==========
#
# Fills every law of rat.bend. Int evidence is called through I (the int.bend
# alias) and Nat evidence through N; the int_proofs.bend / nat_proofs.bend
# imports are what fill *those* laws (a fill attaches to the laws file's
# module, so I.<lemma> and N.<lemma> resolve).
#
# The block below is the congruence block: each law is the same two-step shape,
# a cong on the numerator and a cong on the denominator, because Rat.mk is a
# function and the Int/Nat ring laws already identify the raw arguments.

def R.Rat.add_comm(x, y):
  match x y:
    case R.Rat{xn, xd} R.Rat{yn, yd}:
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

def R.Rat.mul_comm(x, y):
  match x y:
    case R.Rat{xn, xd} R.Rat{yn, yd}:
      Equal.trans(R.Rat,
        R.Rat.mk(I.Int.mul(xn, yn), Nat.mul(xd, yd)),
        R.Rat.mk(I.Int.mul(yn, xn), Nat.mul(xd, yd)),
        R.Rat.mk(I.Int.mul(yn, xn), Nat.mul(yd, xd)),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(xd, yd)),
          I.Int.mul(xn, yn), I.Int.mul(yn, xn), I.Int.mul_comm(xn, yn)),
        Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int.mul(yn, xn), u),
          Nat.mul(xd, yd), Nat.mul(yd, xd), N.mul_comm(xd, yd)))

# Rat.sub_eq_add_neg: definitional -- Rat.sub is Rat.add(x, Rat.neg(y)).
def R.Rat.sub_eq_add_neg(x, y):
  {==}

# Canonicality
# ============

# Rat.mk.canon: the goal is
#   {Rat{Int{div(sub(np,nn), G), div(sub(nn,np), G)}, div(1+dp, G)}
#      == Rat{Int{sub(np,nn), sub(nn,np)}, 1+dp}}
# with G = gcd(mag(np,nn), 1+dp), and the coprime hypothesis turns G into 1;
# div_one then makes the three divisions disappear and the two sides are the
# same term.
def R.Rat.mk.canon(np, nn, dp, g1):
  %Equal.sym(Nat, N.Nat.gcd(R.Rat.mag(np, nn), 1n+dp), 1n, g1)
    : {R.Rat{I.Int{Nat.div(Nat.sub(np, nn), _), Nat.div(Nat.sub(nn, np), _)}, Nat.div(1n+dp, _)} == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  %Equal.sym(Nat, Nat.div(Nat.sub(np, nn), 1n), Nat.sub(np, nn), N.div_one(Nat.sub(np, nn)))
    : {R.Rat{I.Int{_, Nat.div(Nat.sub(nn, np), 1n)}, Nat.div(1n+dp, 1n)} == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  %Equal.sym(Nat, Nat.div(Nat.sub(nn, np), 1n), Nat.sub(nn, np), N.div_one(Nat.sub(nn, np)))
    : {R.Rat{I.Int{Nat.sub(np, nn), _}, Nat.div(1n+dp, 1n)} == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  %Equal.sym(Nat, Nat.div(1n+dp, 1n), 1n+dp, N.div_one(1n+dp))
    : {R.Rat{I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}, _} == R.Rat{R.Rat.num(np, nn), 1n+dp} : R.Rat}
  {==}

# Rat.mk.zero: gcd(0, 1+dp) is 1+dp by reduction (Nat.gcd answers its second
# argument at 0), the numerator divisions are 0/(1+dp) which also reduces, and
# the denominator division is div_self.
def R.Rat.mk.zero(dp):
  %Equal.sym(Nat, Nat.div(1n+dp, 1n+dp), 1n, N.div_self(dp))
    : {R.Rat{I.Int{0n, 0n}, _} == R.Rat.zero() : R.Rat}
  {==}

# Rat.mk.fixed: the goal is
#   {Rat{Int{div(A, G), div(B, G)}, div(1+dp, G)} == Rat{Int{u, v}, 1+dp}}
# with u = sub(np,nn), v = sub(nn,np), A = sub(u,v), B = sub(v,u) -- that is
# what mk sees when it destructures the difference pair it is handed -- and
# G = gcd(add(A,B), 1+dp).
#
# sub_diag collapses A to u and B to v, one rewrite each (the second at the
# *swapped* comparison, whose evidence is cmp_antisym through Cmp.flip and
# flip_flip); after that G is literally the hypothesis's gcd, so it collapses to
# 1 and the three divisions go away with div_one.
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

# The identity laws
# =================
#
# Each of these unfolds the operation (the argument is a constructor, so
# Rat.add/Rat.mul reduce), carries the Int/Nat identity into Rat.mk with one
# rewrite each, and then closes with fx -- the canonicality hypothesis itself.

def R.Rat.mul_one(n, d, fx):
  %Equal.sym(I.Int, I.Int.mul(n, I.Int.one()), n, I.Int.mul_one(n))
    : {R.Rat.mk(_, Nat.mul(d, 1n)) == R.Rat{n, d} : R.Rat}
  %N.mul_one(d) : {R.Rat.mk(n, _) == R.Rat{n, d} : R.Rat}
  fx

def R.Rat.one_mul(n, d, fx):
  %Equal.sym(I.Int, I.Int.mul(I.Int.one(), n), n, I.Int.one_mul(n))
    : {R.Rat.mk(_, Nat.mul(1n, d)) == R.Rat{n, d} : R.Rat}
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d))
    : {R.Rat.mk(n, _) == R.Rat{n, d} : R.Rat}
  fx

def R.Rat.add_zero(n, d, fx):
  %Equal.sym(I.Int, I.Int.mul(n, I.Int.one()), n, I.Int.mul_one(n))
    : {R.Rat.mk(I.Int.add(_, I.Int{0n, 0n}), Nat.mul(d, 1n)) == R.Rat{n, d} : R.Rat}
  %Equal.sym(I.Int, I.Int.add(n, I.Int.zero()), n, I.Int.add_zero(n))
    : {R.Rat.mk(_, Nat.mul(d, 1n)) == R.Rat{n, d} : R.Rat}
  %N.mul_one(d) : {R.Rat.mk(n, _) == R.Rat{n, d} : R.Rat}
  fx

def R.Rat.zero_add(n, d, fx):
  %Equal.sym(I.Int, I.Int.mul(n, I.Int.one()), n, I.Int.mul_one(n))
    : {R.Rat.mk(I.Int.add(I.Int{0n, 0n}, _), Nat.mul(1n, d)) == R.Rat{n, d} : R.Rat}
  %Equal.sym(I.Int, I.Int.add(I.Int.zero(), n), n, I.Int.zero_add(n))
    : {R.Rat.mk(_, Nat.mul(1n, d)) == R.Rat{n, d} : R.Rat}
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d))
    : {R.Rat.mk(n, _) == R.Rat{n, d} : R.Rat}
  fx

def R.Rat.mul_zero(n, dp):
  %Equal.sym(I.Int, I.Int.mul(n, I.Int.zero()), I.Int.zero(), I.Int.mul_zero(n))
    : {R.Rat.mk(_, Nat.mul(1n+dp, 1n)) == R.Rat.zero() : R.Rat}
  %N.mul_one(1n+dp) : {R.Rat.mk(I.Int.zero(), _) == R.Rat.zero() : R.Rat}
  R.Rat.mk.zero(dp)
