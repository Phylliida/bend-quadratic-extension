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

# Scaling
# =======
#
# mk.scale.num is the whole content; .neg is its mirror at the swapped
# comparison, .den is the same proof at the denominator, and .go/.scale are
# three rewrites each. All the arithmetic is Nat-level: the scaled comparison
# collapses with cmp_mul_right, the scaled difference with mul_sub_right, the
# scaled gcd with gcd_scale, and the two divisions with div_scale -- the new
# Nat lemma that packages div_exact_mul/div_exact around a divisor that only
# arrives as a divisibility witness (Pair.fst takes the witness out of the pair
# gcd_divides returns, which cannot be destructured where it is produced).

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

# Rat.mk.scale.neg: the mirror of .num at the swapped comparison -- one call,
# after commuting the two arguments of each gcd's sum so that the goal is
# literally the instance of .num at (nn, np).
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

# Rat.mk.scale.den: the same three rewrites at the denominator, then div_scale
# with the *other* half of the divisibility witness -- and with gravity
# reversed in the EQ branch, where the two sides are d/d and (d*(1+kp))/(d*(1+kp))
# and div_self, not div_zero, is what makes them equal.
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

# Rat.mk.scale.go: one rewrite per coordinate, each the matching Nat half.
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

# Rat.mk.scale: the Int spelling of the scaled numerator is
# Int{add(xp*(1+kp), xn*0), add(xp*0, xn*(1+kp))}; the two zero products come
# off (mul_zero and add_zero), the second slot is then already the scaled
# coordinate, and the reduced term is exactly what mk.scale.go is stated about.
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

# Rat.mk.eqv: equal cross products give equal normal forms. The two sides are
# scaled up to a common denominator -- each by the *other* side's denominator,
# which is what Rat.mk.scale is for -- and in the middle the two numerators are
# the same term by the hypothesis, with the two denominators equal by
# Nat.mul_comm.
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

# Rat.mk.eqv.raw: both denominators go to the successor form pos_witness gives
# (one cong each) and the cross product's two scales travel with them (a cong
# over the second argument of Int.mul, whose evidence is a cong over the
# constructor's Nat slot), which puts the goal in exactly the shape mk.eqv is
# stated about.
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

# Rat.mk.den.pos: one call of div_pos_wit at the second half of the
# divisibility witness gcd_divides returns for (mag, 1+dp) -- Pair.snd takes it
# out of the pair.
def R.Rat.mk.den.pos(np, nn, dp):
  N.div_pos_wit(R.Rat.g(np, nn, 1n+dp), dp,
    Pair.snd(N.Nat.divides(R.Rat.g(np, nn, 1n+dp), R.Rat.mag(np, nn)),
      N.Nat.divides(R.Rat.g(np, nn, 1n+dp), 1n+dp),
      N.gcd_divides(R.Rat.mag(np, nn), 1n+dp)))

# The value lemma
# ===============
#
# Rat.mk.value.go: the two witnesses come apart first (they are binders, so the
# destructure is legal -- a computed pair could not be), then each branch is the
# same three steps:
#
#   - positivity of the gcd, once for both coordinates: the d-witness is rebuilt
#     from its own fields (a Div value is a constructor, and divides_pos_wit
#     wants a witness, not its parts) and handed to divides_pos_wit.
#   - the nontrivial coordinate: g | |n| is a witness for the gcd's *dividend*
#     mag = P + Q, so the branch's comparison is what turns it into a witness
#     for the coordinate that is not zero -- mag collapses to P under GT, to Q
#     under LT (one cong on the sum, add_zero only in the GT case: add(0, Q)
#     already reduces). In EQ both coordinates are 0 and their witness equation
#     is 0 == g*0, which mul_zero gives.
#   - the trivial coordinate (the other one of P, Q): its witness equation
#     Q == g*0 (or P == g*0) is the same mul_zero, and div_cross then proves the
#     coordinate equation from it -- q = 0 is a perfectly good quotient, so no
#     branch needs a second argument.
#
# The assembly is two Equal.cong steps over the Int pair, one per coordinate.
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

# Rat.mk.value: the two raw products are Int.mul of a numerator with the scaled
# unit (d, 0) -- which is how Rat.add/Rat.mul write a Nat scale -- so
# Int.mul_scale unfolds them into the coordinate pair Rat.mk.value.go is stated
# in. In between, the two witnesses go straight through as Pair.fst/Pair.snd of
# the pair gcd_divides returns: .go takes them as binders precisely so that
# nothing here has to destructure a computed value.
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

# Rat.mk_idem.raw: the goal's two sides are
#   mk(numof(M), denof(M))   and   mk(Rat.num(np,nn), d)
# with M = mk(Rat.num(np,nn), d), which is
#   mk(Int{A, B}, R)   and   mk(Rat.num(np,nn), d)
# for A = div(P, G), B = div(Q, G), P = sub(np,nn), Q = sub(nn,np),
# G = Rat.g(P, Q, d) and R = denof(M) = div(d, G) -- i.e. exactly the two
# normal forms mk.eqv.raw compares, at the cross product mk.value gives for M:
#
#   v  is mk.value at (P, Q, d), the value equation numof(M)*d == Rat.num(P,Q)*R
#      (mk.value is stated over the raw coordinates, and P, Q are how mk sees
#      the difference pair it destructured -- so its own gcd is Rat.g(P,Q,d),
#      the very term in the goal, and no spelling has to be transported);
#   ev is the two sub_diags that turn Rat.num(P,Q) into Rat.num(np,nn): one at
#      the comparison c, one at the flipped comparison (cmp_antisym through
#      Cmp.flip, exactly as mk.fixed's fill does it);
#   and eqv.raw's cross product is v transported across ev by one cong.
#
# No coprimality is used anywhere; pd and pq are the law's own two hypotheses.
def R.Rat.mk_idem.raw(c, np, nn, d, e, pd, pq):
  +P = Nat.sub(np, nn)
  +Q = Nat.sub(nn, np)
  +M = R.Rat.mk(R.Rat.num(np, nn), d)
  +k = R.Rat.denof(M)
  +ev = Equal.trans(I.Int,
    R.Rat.num(P, Q),
    I.Int{Nat.sub(np, nn), Nat.sub(Q, P)},
    R.Rat.num(np, nn),
    Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(Q, P)},
      Nat.sub(P, Q), Nat.sub(np, nn), N.sub_diag(c, np, nn, e)),
    Equal.cong(Nat, I.Int, u => I.Int{Nat.sub(np, nn), u},
      Nat.sub(Q, P), Nat.sub(nn, np),
      N.sub_diag(N.Cmp.flip(c), nn, np,
        Equal.trans(Cmp, N.Cmp.flip(c), N.Cmp.flip(Nat.cmp(np, nn)), Nat.cmp(nn, np),
          Equal.cong(Cmp, Cmp, N.Cmp.flip, c, Nat.cmp(np, nn), e),
          Equal.trans(Cmp, N.Cmp.flip(Nat.cmp(np, nn)),
            N.Cmp.flip(N.Cmp.flip(Nat.cmp(nn, np))), Nat.cmp(nn, np),
            Equal.cong(Cmp, Cmp, N.Cmp.flip, Nat.cmp(np, nn),
              N.Cmp.flip(Nat.cmp(nn, np)), N.cmp_antisym(np, nn)),
            N.flip_flip(Nat.cmp(nn, np)))))))
  R.Rat.mk.eqv.raw(R.Rat.numof(M), k, R.Rat.num(np, nn), d, pq, pd,
    Equal.trans(I.Int,
      I.Int.mul(R.Rat.numof(M), I.Int{d, 0n}),
      I.Int.mul(R.Rat.num(P, Q), I.Int{k, 0n}),
      I.Int.mul(R.Rat.num(np, nn), I.Int{k, 0n}),
      R.Rat.mk.value(Nat.cmp(P, Q), P, Q, d, {==}, pd),
      Equal.cong(I.Int, I.Int, u => I.Int.mul(u, I.Int{k, 0n}),
        R.Rat.num(P, Q), R.Rat.num(np, nn), ev)))

# Rat.mk_idem: the successor-denominator law is unconditional, so the only work
# it does on its own is the positivity of the output's denominator -- and that
# is one div_pos_wit at the gcd spelling the *goal* carries (Rat.g of the raw
# coordinates mk destructured), with the divisibility witness gcd_divides
# returns for that same magnitude. Rat.mk.den.pos is stated at the unexpanded
# Rat.mag(np,nn) spelling of that gcd, which is why it does not fit here; this
# call does not need it. The rest is mk_idem.raw with pd discharged by
# computation, the denominator being a successor literal.
def R.Rat.mk_idem(c, np, nn, dp, e):
  +P = Nat.sub(np, nn)
  +Q = Nat.sub(nn, np)
  +G = R.Rat.g(P, Q, 1n+dp)
  R.Rat.mk_idem.raw(c, np, nn, 1n+dp, e, {==},
    N.div_pos_wit(G, dp,
      Pair.snd(N.Nat.divides(G, R.Rat.mag(P, Q)), N.Nat.divides(G, 1n+dp),
        N.gcd_divides(R.Rat.mag(P, Q), 1n+dp))))

# Rat.mk.rep: the goal's two sides are
#   mk(Rat.num(U,V), d)   and   mk(Int{U,V}, d)
# which unfold -- mk destructures its argument -- to
#   Rat{Int{div(sub(P,Q), G1), div(sub(Q,P), G1)}, div(d, G1)}   and
#   Rat{Int{div(P, G2), div(Q, G2)}, div(d, G2)}
# with P = sub(U,V), Q = sub(V,U), G1 = gcd(mag(P,Q), d), G2 = gcd(mag(U,V), d).
# The two agree coordinate by coordinate once the mag of the *one-sided* pair is
# collapsed: the two sub_diags mk.fixed's fill makes, here at the explicit
# comparisons cmp(U,V) and cmp(V,U) -- so no flip evidence and no comparison
# parameter.
#
# The rewrites have to reach three places each (both div dividends and the gcd
# that is the divisor), and the dividends sit under Nat.div, which is why every
# step is an Equal.cong with a motive rather than a %:
#
#   eg      the gcds agree -- the two summands of mag(P,Q) collapse, and what is
#           left is literally mag(U,V);
#   E1/E2/E3 the three coordinates agree, one cong on the dividend and one on
#           the divisor apiece;
#   En      the numerator pair, one cong per slot;
#   and then one cong per Rat slot, the denominator of the value not moving at
#   all.
#
# No division is ever evaluated, so nothing needs positivity or a divisibility
# witness: this is a rewrite of the quotients' arguments, which is what
# Equal.cong delivers.
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

# Rat.mk.trunc: the goal's two sides unfold -- both mks destructure -- to
#
#   Rat{Int{div(P, G1), div(Q, G1)}, div(d, G1)}                        and
#   Rat{Int{div(sub(sub(P,Q), sub(Q,P)), G2), div(sub(sub(Q,P), sub(P,Q)), G2)}, div(d, G2)}
#
# with P = sub(U,V), Q = sub(V,U), G1 = gcd(P + Q, d) and G2 = gcd of the
# *truncations of the truncation pair*. The two agree coordinate by coordinate
# once those truncations collapse: sub_diag at (P, Q) and then at (U, V) sends
# sub(sub(P,Q), sub(Q,P)) to P, and the same two instances at the swapped
# comparisons send the other coordinate to Q -- so the gcd's sum is P + Q in
# either spelling (eg), the three divisions agree, and the two Rat constructors
# are the same term.
#
# This is mk.rep's fill with the roles of the two representations exchanged (that
# one collapses the *pair's* mag, this one collapses the truncation pair's), and
# it is the same discipline: every rewrite is an Equal.cong with a motive, never a
# `%`, because each one reaches under a Nat.div.
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

# Rat.mk.canon.go: canon.go's branch value and Rat.num(xp,xn) are the same pair
# once the truncation the branch's own sign forces to zero has collapsed, so each
# branch is one congruence after Rat.mk.rep (read backwards) has put the
# numerator into the Rat.num spelling mk.rep is stated over:
#
#   GT: canon.go's value is Int{sub(xp,xn), 0}, and sub(xn,xp) is 0 by sub_of_lt
#       at the comparison the GT flips to (cmp_lt_of_gt);
#   LT: canon.go's value is Int{0, sub(xn,xp)}, and sub(xp,xn) is 0 by sub_of_lt
#       at the comparison itself;
#   EQ: both truncations are 0 -- cmp_eq turns the branch into xp == xn, and one
#       cong puts sub(xp,xp) at each of them for sub_self to close.
#
# Every rewrite is an Equal.cong rather than a %: the two truncations sit in the
# constructor's own slots, which a % could reach too, but the chain reads better
# with the endpoints spelled out (and the goal's own Rat.num spelling only meets
# the Int constructor by conversion).
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

# Rat.mk.eqv.val: two forward chains, one per side, meeting at the canonical
# forms. The left one runs
#
#   mk(Int{xp,xn}, d1)
#     -> mk(Int{xp,xn}, da)                        pos_witness (a = sub(d1,1))
#     -> mk(mul(Int{xp,xn}, db), D)                mk.scale by db = 1+b, backwards
#     -> mk(Int{xp*db, xn*db}, D)                  Int.mul_scale (the raw spelling)
#     -> mk(canon.go(cx, xp*db, xn*db), D)         mk.canon.go
#
# and the right one is the same four steps for (yp, yn, d2) with the two
# denominators exchanged, ending at mk(canon.go(cy, ...), D). The two canonical
# forms are equated by Int.canon.eqv.bwd from the cross sum, one cong carries
# that through mk, and the right chain is read backwards to close the goal.
#
# D = da*db with da = 1+a, db = 1+b; cx/cy are the comparisons of the *scaled*
# pairs, threaded in so that nothing cases on a computed Nat.cmp; and the cross
# sum bwd consumes is e re-spelled from (d1, d2) to (da, db) -- e mentions each
# denominator twice, so that re-spelling is two congs per side.
#
# The Int.mul_scale steps are not optional: Nat.mul matches on its *first*
# argument, so Int.mul(Int{xp,xn}, Int{db,0n}) is stuck at
# Int{add(xp*db, xn*0), add(xp*0, xn*db)} and does *not* convert to the raw pair
# the canonical laws are stated over -- that law is the only bridge, exactly as
# its own comment says.
#
# Every cong is written inline: a let-bound Equal.cong has no determined type
# (the motive's codomain is the cong's own second type argument and nothing fixes
# it), while the same term in an argument position of Equal.trans/Equal.sym is
# checked against the endpoints spelled there. The comparison arguments of
# mk.canon.go are Nat.cmp of the scaled coordinates with {==} evidence, the only
# spelling available inside a fill.
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

# The product shape
# =================
#
# The composing laws (mul_assoc and its siblings) have to relate two
# *normalized* results, and the only tool for that is Rat.mk.eqv, whose
# hypothesis is a cross product of the raw numerators. Rat.mk.value supplies
# each factor's cross product, but it names its numerator in Rat.num spelling
# (the difference pair), while the products the operations write are raw
# coordinates -- and those two are not the same Int: Rat.num(np,nn) is the
# one-sided pair sub(np,nn), sub(nn,np), which is a different *pair* from
# Int{np,nn}. Closing that gap is what the two helpers below do.
#
# Rat.num.mul: the product of two difference pairs is Rat.num of the product's
# own coordinates -- i.e. that product is one-sided again. Which side is zero is
# exactly the sign of the two factors, so the two comparisons arrive as
# parameters and the fill splits on them; each branch derives the zeros
# (sub_of_lt at the flipped comparison) and finishes with dp.eq.right /
# dp.eq.left, which need nothing but "one side is zero". In between, a zero
# factor kills its product: mul_zero for a zero on the right, computation for a
# zero on the left.

def R.Rat.dp.eq.right(U, V, z):
  %Equal.sym(Nat, V, 0n, z) : {I.Int{U, _} == R.Rat.num(U, _) : I.Int}
  %Equal.sym(Nat, Nat.sub(U, 0n), U, N.sub_zero(U)) : {I.Int{U, 0n} == I.Int{_, Nat.sub(0n, U)} : I.Int}
  %Equal.sym(Nat, Nat.sub(0n, U), 0n, N.sub_zero_left(U)) : {I.Int{U, 0n} == I.Int{U, _} : I.Int}
  {==}

def R.Rat.dp.eq.left(U, V, z):
  %Equal.sym(Nat, U, 0n, z) : {I.Int{_, V} == R.Rat.num(_, V) : I.Int}
  %Equal.sym(Nat, Nat.sub(0n, V), 0n, N.sub_zero_left(V)) : {I.Int{0n, V} == I.Int{_, Nat.sub(V, 0n)} : I.Int}
  %Equal.sym(Nat, Nat.sub(V, 0n), V, N.sub_zero(V)) : {I.Int{0n, V} == I.Int{0n, _} : I.Int}
  {==}

def R.Rat.num.mul(c1, np1, nn1, e1, c2, np2, nn2, e2):
  match c1:
    case GT{}:
      match c2:
        case GT{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +P2 = Nat.sub(np2, nn2)
          +Q2 = Nat.sub(nn2, np2)
          +U = Nat.add(Nat.mul(P1, P2), Nat.mul(Q1, Q2))
          +V = Nat.add(Nat.mul(P1, Q2), Nat.mul(Q1, P2))
          +z1 = N.sub_of_lt(nn1, np1,
            N.cmp_lt_of_gt(np1, nn1, Equal.sym(Cmp, GT{}, Nat.cmp(np1, nn1), e1)))
          +z2 = N.sub_of_lt(nn2, np2,
            N.cmp_lt_of_gt(np2, nn2, Equal.sym(Cmp, GT{}, Nat.cmp(np2, nn2), e2)))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V, Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, P2)), 0n,
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(P1, w), Nat.mul(Q1, P2)),
                Q2, 0n, z2),
              Equal.trans(Nat,
                Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, P2)),
                Nat.add(0n, Nat.mul(Q1, P2)),
                0n,
                Equal.cong(Nat, Nat, w => Nat.add(w, Nat.mul(Q1, P2)),
                  Nat.mul(P1, 0n), 0n, N.mul_zero(P1)),
                Equal.cong(Nat, Nat, w => Nat.add(0n, Nat.mul(w, P2)),
                  Q1, 0n, z1))))
        case EQ{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +U = Nat.add(Nat.mul(P1, Nat.sub(np2, nn2)), Nat.mul(Q1, Nat.sub(nn2, np2)))
          +V = Nat.add(Nat.mul(P1, Nat.sub(nn2, np2)), Nat.mul(Q1, Nat.sub(np2, nn2)))
          +z2 = N.cmp_eq(np2, nn2, Equal.sym(Cmp, EQ{}, Nat.cmp(np2, nn2), e2))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V,
              Nat.add(Nat.mul(P1, Nat.sub(nn2, nn2)), Nat.mul(Q1, Nat.sub(nn2, nn2))),
              0n,
              Equal.cong(Nat, Nat,
                w => Nat.add(Nat.mul(P1, Nat.sub(nn2, w)), Nat.mul(Q1, Nat.sub(w, nn2))),
                np2, nn2, z2),
              Equal.trans(Nat,
                Nat.add(Nat.mul(P1, Nat.sub(nn2, nn2)), Nat.mul(Q1, Nat.sub(nn2, nn2))),
                Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, 0n)),
                0n,
                Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(P1, w), Nat.mul(Q1, w)),
                  Nat.sub(nn2, nn2), 0n,
                  N.sub_self(nn2)),
                Equal.trans(Nat,
                  Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, 0n)),
                  Nat.add(0n, Nat.mul(Q1, 0n)),
                  0n,
                  Equal.cong(Nat, Nat, w => Nat.add(w, Nat.mul(Q1, 0n)),
                    Nat.mul(P1, 0n), 0n, N.mul_zero(P1)),
                  Equal.cong(Nat, Nat, w => Nat.add(0n, w), Nat.mul(Q1, 0n), 0n,
                    N.mul_zero(Q1))))))
        case LT{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +P2 = Nat.sub(np2, nn2)
          +Q2 = Nat.sub(nn2, np2)
          +U = Nat.add(Nat.mul(P1, P2), Nat.mul(Q1, Q2))
          +V = Nat.add(Nat.mul(P1, Q2), Nat.mul(Q1, P2))
          +z1 = N.sub_of_lt(nn1, np1,
            N.cmp_lt_of_gt(np1, nn1, Equal.sym(Cmp, GT{}, Nat.cmp(np1, nn1), e1)))
          +z2 = N.sub_of_lt(np2, nn2, Equal.sym(Cmp, LT{}, Nat.cmp(np2, nn2), e2))
          R.Rat.dp.eq.left(U, V,
            Equal.trans(Nat, U, Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, Q2)), 0n,
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(P1, w), Nat.mul(Q1, Q2)),
                P2, 0n, z2),
              Equal.trans(Nat,
                Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, Q2)),
                Nat.add(0n, Nat.mul(Q1, Q2)),
                0n,
                Equal.cong(Nat, Nat, w => Nat.add(w, Nat.mul(Q1, Q2)),
                  Nat.mul(P1, 0n), 0n, N.mul_zero(P1)),
                Equal.cong(Nat, Nat, w => Nat.add(0n, Nat.mul(w, Q2)),
                  Q1, 0n, z1))))
    case EQ{}:
      match c2:
        case GT{}:
          +P2 = Nat.sub(np2, nn2)
          +Q2 = Nat.sub(nn2, np2)
          +U = Nat.add(Nat.mul(Nat.sub(np1, nn1), P2), Nat.mul(Nat.sub(nn1, np1), Q2))
          +V = Nat.add(Nat.mul(Nat.sub(np1, nn1), Q2), Nat.mul(Nat.sub(nn1, np1), P2))
          +z1 = N.cmp_eq(np1, nn1, Equal.sym(Cmp, EQ{}, Nat.cmp(np1, nn1), e1))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V,
              Nat.add(Nat.mul(Nat.sub(nn1, nn1), Q2), Nat.mul(Nat.sub(nn1, nn1), P2)),
              0n,
              Equal.cong(Nat, Nat,
                w => Nat.add(Nat.mul(Nat.sub(w, nn1), Q2), Nat.mul(Nat.sub(nn1, w), P2)),
                np1, nn1, z1),
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(w, Q2), Nat.mul(w, P2)),
                Nat.sub(nn1, nn1), 0n, N.sub_self(nn1))))
        case EQ{}:
          +U = Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(np2, nn2)),
                       Nat.mul(Nat.sub(nn1, np1), Nat.sub(nn2, np2)))
          +V = Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(nn2, np2)),
                       Nat.mul(Nat.sub(nn1, np1), Nat.sub(np2, nn2)))
          +z1 = N.cmp_eq(np1, nn1, Equal.sym(Cmp, EQ{}, Nat.cmp(np1, nn1), e1))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V,
              Nat.add(Nat.mul(Nat.sub(nn1, nn1), Nat.sub(nn2, np2)),
                      Nat.mul(Nat.sub(nn1, nn1), Nat.sub(np2, nn2))),
              0n,
              Equal.cong(Nat, Nat,
                w => Nat.add(Nat.mul(Nat.sub(w, nn1), Nat.sub(nn2, np2)),
                             Nat.mul(Nat.sub(nn1, w), Nat.sub(np2, nn2))),
                np1, nn1, z1),
              Equal.cong(Nat, Nat,
                w => Nat.add(Nat.mul(w, Nat.sub(nn2, np2)), Nat.mul(w, Nat.sub(np2, nn2))),
                Nat.sub(nn1, nn1), 0n, N.sub_self(nn1))))
        case LT{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +P2 = Nat.sub(np2, nn2)
          +Q2 = Nat.sub(nn2, np2)
          +U = Nat.add(Nat.mul(P1, P2), Nat.mul(Q1, Q2))
          +V = Nat.add(Nat.mul(P1, Q2), Nat.mul(Q1, P2))
          +z1 = N.cmp_eq(np1, nn1, Equal.sym(Cmp, EQ{}, Nat.cmp(np1, nn1), e1))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V,
              Nat.add(Nat.mul(Nat.sub(nn1, nn1), Q2), Nat.mul(Nat.sub(nn1, nn1), P2)),
              0n,
              Equal.cong(Nat, Nat,
                w => Nat.add(Nat.mul(Nat.sub(w, nn1), Q2), Nat.mul(Nat.sub(nn1, w), P2)),
                np1, nn1, z1),
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(w, Q2), Nat.mul(w, P2)),
                Nat.sub(nn1, nn1), 0n, N.sub_self(nn1))))
    case LT{}:
      match c2:
        case GT{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +P2 = Nat.sub(np2, nn2)
          +Q2 = Nat.sub(nn2, np2)
          +U = Nat.add(Nat.mul(P1, P2), Nat.mul(Q1, Q2))
          +V = Nat.add(Nat.mul(P1, Q2), Nat.mul(Q1, P2))
          +z1 = N.sub_of_lt(np1, nn1, Equal.sym(Cmp, LT{}, Nat.cmp(np1, nn1), e1))
          +z2 = N.sub_of_lt(nn2, np2,
            N.cmp_lt_of_gt(np2, nn2, Equal.sym(Cmp, GT{}, Nat.cmp(np2, nn2), e2)))
          R.Rat.dp.eq.left(U, V,
            Equal.trans(Nat, U, Nat.add(Nat.mul(0n, P2), Nat.mul(Q1, Q2)), 0n,
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(w, P2), Nat.mul(Q1, Q2)),
                P1, 0n, z1),
              Equal.trans(Nat,
                Nat.add(Nat.mul(0n, P2), Nat.mul(Q1, Q2)),
                Nat.add(0n, Nat.mul(Q1, 0n)),
                0n,
                Equal.cong(Nat, Nat, w => Nat.add(0n, Nat.mul(Q1, w)),
                  Q2, 0n, z2),
                Equal.cong(Nat, Nat, w => Nat.add(0n, w), Nat.mul(Q1, 0n), 0n,
                  N.mul_zero(Q1)))))
        case EQ{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +U = Nat.add(Nat.mul(P1, Nat.sub(np2, nn2)), Nat.mul(Q1, Nat.sub(nn2, np2)))
          +V = Nat.add(Nat.mul(P1, Nat.sub(nn2, np2)), Nat.mul(Q1, Nat.sub(np2, nn2)))
          +z2 = N.cmp_eq(np2, nn2, Equal.sym(Cmp, EQ{}, Nat.cmp(np2, nn2), e2))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V,
              Nat.add(Nat.mul(P1, Nat.sub(nn2, nn2)), Nat.mul(Q1, Nat.sub(nn2, nn2))),
              0n,
              Equal.cong(Nat, Nat,
                w => Nat.add(Nat.mul(P1, Nat.sub(nn2, w)), Nat.mul(Q1, Nat.sub(w, nn2))),
                np2, nn2, z2),
              Equal.trans(Nat,
                Nat.add(Nat.mul(P1, Nat.sub(nn2, nn2)), Nat.mul(Q1, Nat.sub(nn2, nn2))),
                Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, 0n)),
                0n,
                Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(P1, w), Nat.mul(Q1, w)),
                  Nat.sub(nn2, nn2), 0n,
                  N.sub_self(nn2)),
                Equal.trans(Nat,
                  Nat.add(Nat.mul(P1, 0n), Nat.mul(Q1, 0n)),
                  Nat.add(0n, Nat.mul(Q1, 0n)),
                  0n,
                  Equal.cong(Nat, Nat, w => Nat.add(w, Nat.mul(Q1, 0n)),
                    Nat.mul(P1, 0n), 0n, N.mul_zero(P1)),
                  Equal.cong(Nat, Nat, w => Nat.add(0n, w), Nat.mul(Q1, 0n), 0n,
                    N.mul_zero(Q1))))))
        case LT{}:
          +P1 = Nat.sub(np1, nn1)
          +Q1 = Nat.sub(nn1, np1)
          +P2 = Nat.sub(np2, nn2)
          +Q2 = Nat.sub(nn2, np2)
          +U = Nat.add(Nat.mul(P1, P2), Nat.mul(Q1, Q2))
          +V = Nat.add(Nat.mul(P1, Q2), Nat.mul(Q1, P2))
          +z1 = N.sub_of_lt(np1, nn1, Equal.sym(Cmp, LT{}, Nat.cmp(np1, nn1), e1))
          +z2 = N.sub_of_lt(np2, nn2, Equal.sym(Cmp, LT{}, Nat.cmp(np2, nn2), e2))
          R.Rat.dp.eq.right(U, V,
            Equal.trans(Nat, V, Nat.add(Nat.mul(0n, Q2), Nat.mul(Q1, P2)), 0n,
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(w, Q2), Nat.mul(Q1, P2)),
                P1, 0n, z1),
              Equal.trans(Nat,
                Nat.add(Nat.mul(0n, Q2), Nat.mul(Q1, P2)),
                Nat.add(0n, Nat.mul(Q1, 0n)),
                0n,
                Equal.cong(Nat, Nat, w => Nat.add(0n, Nat.mul(Q1, w)),
                  P2, 0n, z2),
                Equal.cong(Nat, Nat, w => Nat.add(0n, w), Nat.mul(Q1, 0n), 0n,
                  N.mul_zero(Q1)))))

# Rat.mul_assoc: the goal unfolds (Rat.mul and Rat.mk both destructure) to
#   mk(numof(M1)*zn, denof(M1)*zd) == mk(xn*numof(M2), xd*denof(M2))
# with M1 = mk(xn*yn, xd*yd) and M2 = mk(yn*zn, yd*zd), so the two sides are
# two normal forms whose *raw* cross product is the one mk.eqv.raw consumes:
#
#   - v1/v2 are mk.value on M1 and M2: numof(Mi)*di == Ri*denof(Mi), with Ri
#     the difference pair of the product's coordinates;
#   - s1/s2 are num.mul: Ri is that product (the sign analysis lives there);
#   - cr is Int.scale_cross: the two value equations scaled by the denominator
#     they share (yd) and reduced to the cross product of the composed
#     fraction -- (A*zn)*(xd*b) == (xn*B)*(a*zd), scaled by yd;
#   - w cancels that yd (Int.scale_cancel), which is the hypothesis mk.eqv.raw
#     wants, and the last call is the equality of the two normal forms.
#
# The positivity mk.value and mk.eqv.raw need of the denominators is
# div_pos_wit on each gcd (the dividend is a product of two successors, which
# is the 1n+ap spelling that law wants) and mul_pos on the product.
def R.Rat.mul_assoc(c1, np1, nn1, e1, dp1, c2, np2, nn2, e2, dp2, c3, np3, nn3, e3, dp3):
  +xd = Nat.add(1n, dp1)
  +yd = Nat.add(1n, dp2)
  +zd = Nat.add(1n, dp3)
  +xn = R.Rat.num(np1, nn1)
  +yn = R.Rat.num(np2, nn2)
  +zn = R.Rat.num(np3, nn3)
  +d1 = Nat.mul(xd, yd)
  +d2 = Nat.mul(yd, zd)
  +U1 = Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(np2, nn2)),
                Nat.mul(Nat.sub(nn1, np1), Nat.sub(nn2, np2)))
  +V1 = Nat.add(Nat.mul(Nat.sub(np1, nn1), Nat.sub(nn2, np2)),
                Nat.mul(Nat.sub(nn1, np1), Nat.sub(np2, nn2)))
  +U2 = Nat.add(Nat.mul(Nat.sub(np2, nn2), Nat.sub(np3, nn3)),
                Nat.mul(Nat.sub(nn2, np2), Nat.sub(nn3, np3)))
  +V2 = Nat.add(Nat.mul(Nat.sub(np2, nn2), Nat.sub(nn3, np3)),
                Nat.mul(Nat.sub(nn2, np2), Nat.sub(np3, nn3)))
  +g1 = R.Rat.g(U1, V1, d1)
  +g2 = R.Rat.g(U2, V2, d2)
  +M1 = R.Rat.mk(I.Int{U1, V1}, d1)
  +M2 = R.Rat.mk(I.Int{U2, V2}, d2)
  +A = R.Rat.numof(M1)
  +a = R.Rat.denof(M1)
  +B = R.Rat.numof(M2)
  +b = R.Rat.denof(M2)
  +R1 = R.Rat.num(U1, V1)
  +R2 = R.Rat.num(U2, V2)
  +pa1 = N.div_pos_wit(g1, Nat.add(dp2, Nat.mul(dp1, Nat.add(1n, dp2))),
    Pair.snd(N.Nat.divides(g1, R.Rat.mag(U1, V1)), N.Nat.divides(g1, d1),
      N.gcd_divides(R.Rat.mag(U1, V1), d1)))
  +pa2 = N.div_pos_wit(g2, Nat.add(dp3, Nat.mul(dp2, Nat.add(1n, dp3))),
    Pair.snd(N.Nat.divides(g2, R.Rat.mag(U2, V2)), N.Nat.divides(g2, d2),
      N.gcd_divides(R.Rat.mag(U2, V2), d2)))
  +p1 = N.mul_pos(a, zd, pa1, {==})
  +p2 = N.mul_pos(xd, b, {==}, pa2)
  +v1 = R.Rat.mk.value(Nat.cmp(U1, V1), U1, V1, d1, {==}, N.mul_pos(xd, yd, {==}, {==}))
  +v2 = R.Rat.mk.value(Nat.cmp(U2, V2), U2, V2, d2, {==}, N.mul_pos(yd, zd, {==}, {==}))
  +s1 = Equal.sym(I.Int, I.Int.mul(xn, yn), R1,
    R.Rat.num.mul(c1, np1, nn1, e1, c2, np2, nn2, e2))
  +s2 = Equal.sym(I.Int, I.Int.mul(yn, zn), R2,
    R.Rat.num.mul(c2, np2, nn2, e2, c3, np3, nn3, e3))
  +cr = I.Int.scale_cross(A, R1, B, R2, xn, yn, zn, a, b, xd, zd, dp2, v1, v2, s1, s2)
  +w = I.Int.scale.cancel(I.Int.mul(I.Int.mul(A, zn), I.Int.unit(Nat.mul(xd, b))),
    I.Int.mul(I.Int.mul(xn, B), I.Int.unit(Nat.mul(a, zd))), dp2, cr)
  R.Rat.mk.eqv.raw(I.Int.mul(A, zn), Nat.mul(a, zd), I.Int.mul(xn, B), Nat.mul(xd, b), p1, p2, w)

# Rat.neg_neg: neg on a constructor is mk of the swapped numerator, so the inner
# negation is M1 = mk(Int.neg(Rat.num(np,nn)), 1+dp), i.e. mk(Rat.num(nn,np),
# 1+dp) -- and that is one mk.fixed away from the canonical value
# Rat{Rat.num(nn,np), 1+dp}, because mag(nn,np) is mag(np,nn) with its two
# summands exchanged (add_comm), so the same gcd is 1. Negating that value gives
# mk(Rat.num(np,nn), 1+dp) back, and the second mk.fixed returns the original
# value. Both mk-headed intermediates are definitional; only the mag symmetry
# needs a proof, and it is the same one mk.fixed's own fill makes.
def R.Rat.neg_neg(c, np, nn, dp, e, g1):
  +d = Nat.add(1n, dp)
  +g1s = Equal.trans(Nat,
    N.Nat.gcd(R.Rat.mag(nn, np), d),
    N.Nat.gcd(R.Rat.mag(np, nn), d),
    1n,
    Equal.cong(Nat, Nat, u => N.Nat.gcd(u, d),
      R.Rat.mag(nn, np), R.Rat.mag(np, nn),
      N.add_comm(Nat.sub(nn, np), Nat.sub(np, nn))),
    g1)
  Equal.trans(R.Rat,
    R.Rat.neg(R.Rat.neg(R.Rat{R.Rat.num(np, nn), d})),
    R.Rat.neg(R.Rat{R.Rat.num(nn, np), d}),
    R.Rat{R.Rat.num(np, nn), d},
    Equal.cong(R.Rat, R.Rat, u => R.Rat.neg(u),
      R.Rat.mk(I.Int.neg(R.Rat.num(np, nn)), d),
      R.Rat{R.Rat.num(nn, np), d},
      R.Rat.mk.fixed(Nat.cmp(nn, np), nn, np, dp, {==}, g1s)),
    Equal.trans(R.Rat,
      R.Rat.neg(R.Rat{R.Rat.num(nn, np), d}),
      R.Rat.mk(R.Rat.num(np, nn), d),
      R.Rat{R.Rat.num(np, nn), d},
      {==},
      R.Rat.mk.fixed(c, np, nn, dp, e, g1)))

# The additive value equation
# ===========================
#
# Rat.add.value's fill is two proof-only helpers and the one mk.eqv.raw call
# that consumes what they build. Nothing in the block is a new Rat-level fact:
# the whole proof is Int-level ring permutation around the *value equations* of
# the two summands (Rat.mk.value), which is the only place the div/gcd-headed
# projection is ever read. That is the shape the additive laws were missing --
# the product case has its own shape law (Rat.num.mul), but a sum of difference
# pairs is not one-sided, so its cross product has to be assembled instead.

# Rat.add.piece: one summand of the additive cross product,
#
#   (A*g) * (e*f) == (u*f) * (h*g),
#
# from that summand's value equation A*e == r*h (mk.value's conclusion, with e
# its input denominator and h the quotient the gcd left) and the shape fact
# r == u (Rat.num of the raw coordinates against the raw pair itself). Every
# step is a ring permutation: the scale e*f splits with Int.scale.pair, A and e
# are brought next to each other with mul_assoc/mul_swap so that the value
# equation applies, and the two scales are recombined as h*g. Writing the scales
# as Int.unit(...) is what makes them movable at all -- as a value a scale is an
# Int, and Int.scale.pair is the law that splits it.
def Rat.add.piece(+A: I.Int, +r: I.Int, +u: I.Int, +e: Nat, +f: Nat, +g: Nat, +h: Nat,
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

# Rat.add.cross: the cross product itself, one piece per summand and one
# Int.mul_add_left step at each end to take the sum in and out of the product.
# The two summands' pieces are mirror images -- (A, e=xd, g=k2, h=k1) against
# (B, e=yd, g=k1, h=k2) -- so the second piece needs the shared denominator and
# the merged scale re-spelled by Nat.mul_comm before and after it; both are one
# congruence over the Nat inside an Int.unit.
def Rat.add.cross(+A: I.Int, +B: I.Int, +r1: I.Int, +u1: I.Int, +r2: I.Int, +u2: I.Int,
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
  %Equal.sym(I.Int, I.Int.mul(AK, D), I.Int.mul(U1, K), Rat.add.piece(A, r1, u1, xd, yd, k2, k1, v1, s1))
    : {I.Int.add(_, I.Int.mul(BK, D)) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, D, I.Int.unit(Nat.mul(yd, xd)),
      Equal.cong(Nat, I.Int, w => I.Int.unit(w), Nat.mul(xd, yd), Nat.mul(yd, xd), N.mul_comm(xd, yd)))
    : {I.Int.add(I.Int.mul(U1, K), I.Int.mul(BK, _)) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(BK, I.Int.unit(Nat.mul(yd, xd))), I.Int.mul(U2, I.Int.unit(Nat.mul(k2, k1))),
      Rat.add.piece(B, r2, u2, yd, xd, k1, k2, v2, s2))
    : {I.Int.add(I.Int.mul(U1, K), _) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %Equal.sym(I.Int, I.Int.unit(Nat.mul(k2, k1)), K,
      Equal.cong(Nat, I.Int, w => I.Int.unit(w), Nat.mul(k2, k1), Nat.mul(k1, k2), N.mul_comm(k2, k1)))
    : {I.Int.add(I.Int.mul(U1, K), I.Int.mul(U2, _)) == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  %I.Int.mul_add_left(U1, U2, K)
    : {_ == I.Int.mul(I.Int.add(U1, U2), K) : I.Int}
  {==}

# Rat.add.value: the goal's two sides are
#   add(mk(Rat.num(np1,nn1), xd), mk(Rat.num(np2,nn2), yd))   and   mk(T, d)
# with xd = 1+dp1, yd = 1+dp2, d = xd*yd and T the raw sum of the two scaled
# difference pairs. Rat.add destructures both arguments, and each is mk-headed
# and already reduced, so the left side is mk(nR, kR) with nR the two
# projections scaled by the other's denominator (k1, k2 the quotients the two
# gcds left) and kR = k1*k2 -- two normal forms, compared by exactly the cross
# product Rat.add.cross assembles. The four facts it is built from are:
#
#   v1/v2  mk.value on each summand: numof(Mi)*di == Rat.num(ai,bi)*ki, with
#          (ai, bi) = (sub(npi,nni), sub(nni,npi)) the coordinates mk saw;
#   s1/s2  Rat.num(ai,bi) == Int{ai,bi} -- the two sub_diags that collapse the
#          difference pair of a pair that is *already* a pair of truncations,
#          which is what makes the raw sum reachable at all (the same collapse
#          mk.fixed's fill makes, at the explicit comparisons);
#   pk1/pk2  the positivity of the two quotients, one div_pos_wit per summand at
#          the gcd spelling mk itself carries.
#
# The rest is Rat.mk.eqv.raw, with the positivity of kR (mul_pos of the two
# quotients) and of d (mul_pos of the two successors) as its two slots.
def R.Rat.add.value(np1, nn1, dp1, np2, nn2, dp2):
  +xd = Nat.add(1n, dp1)
  +yd = Nat.add(1n, dp2)
  +d = Nat.mul(xd, yd)
  +a1 = Nat.sub(np1, nn1)
  +b1 = Nat.sub(nn1, np1)
  +a2 = Nat.sub(np2, nn2)
  +b2 = Nat.sub(nn2, np2)
  +M1 = R.Rat.mk(I.Int{a1, b1}, xd)
  +M2 = R.Rat.mk(I.Int{a2, b2}, yd)
  +A = R.Rat.numof(M1)
  +B = R.Rat.numof(M2)
  +k1 = R.Rat.denof(M1)
  +k2 = R.Rat.denof(M2)
  +G1 = R.Rat.g(a1, b1, xd)
  +G2 = R.Rat.g(a2, b2, yd)
  +nR = I.Int.add(I.Int.mul(A, I.Int.unit(k2)), I.Int.mul(B, I.Int.unit(k1)))
  +kR = Nat.mul(k1, k2)
  +T = I.Int.add(I.Int.mul(I.Int{a1, b1}, I.Int.unit(yd)), I.Int.mul(I.Int{a2, b2}, I.Int.unit(xd)))
  +v1 = R.Rat.mk.value(Nat.cmp(a1, b1), a1, b1, xd, {==}, {==})
  +v2 = R.Rat.mk.value(Nat.cmp(a2, b2), a2, b2, yd, {==}, {==})
  +s1 = Equal.trans(I.Int, R.Rat.num(a1, b1), I.Int{a1, Nat.sub(b1, a1)}, I.Int{a1, b1},
    Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(b1, a1)}, Nat.sub(a1, b1), a1,
      N.sub_diag(Nat.cmp(np1, nn1), np1, nn1, {==})),
    Equal.cong(Nat, I.Int, u => I.Int{a1, u}, Nat.sub(b1, a1), b1,
      N.sub_diag(Nat.cmp(nn1, np1), nn1, np1, {==})))
  +s2 = Equal.trans(I.Int, R.Rat.num(a2, b2), I.Int{a2, Nat.sub(b2, a2)}, I.Int{a2, b2},
    Equal.cong(Nat, I.Int, u => I.Int{u, Nat.sub(b2, a2)}, Nat.sub(a2, b2), a2,
      N.sub_diag(Nat.cmp(np2, nn2), np2, nn2, {==})),
    Equal.cong(Nat, I.Int, u => I.Int{a2, u}, Nat.sub(b2, a2), b2,
      N.sub_diag(Nat.cmp(nn2, np2), nn2, np2, {==})))
  +pk1 = N.div_pos_wit(G1, dp1,
    Pair.snd(N.Nat.divides(G1, R.Rat.mag(a1, b1)), N.Nat.divides(G1, xd), N.gcd_divides(R.Rat.mag(a1, b1), xd)))
  +pk2 = N.div_pos_wit(G2, dp2,
    Pair.snd(N.Nat.divides(G2, R.Rat.mag(a2, b2)), N.Nat.divides(G2, yd), N.gcd_divides(R.Rat.mag(a2, b2), yd)))
  R.Rat.mk.eqv.raw(nR, kR, T, d,
    N.mul_pos(k1, k2, pk1, pk2),
    N.mul_pos(xd, yd, {==}, {==}),
    Rat.add.cross(A, B, R.Rat.num(a1, b1), I.Int{a1, b1}, R.Rat.num(a2, b2), I.Int{a2, b2}, xd, yd, k1, k2, v1, v2, s1, s2))

# The mixed value equation
# ========================
#
# Rat.add.value.mixed's cross product is one helper and nothing else: the whole
# proof is the *value equation* mk.value gives for the mk summand, scaled by the
# square of the second summand's denominator and carried through the two sums by
# the ring laws. No truncation reasoning and no case split -- because the mk
# summand's numerator is named by the presentation's own truncations (sub(np,nn),
# sub(nn,np)), which is exactly the spelling mk.value's conclusion is stated in.
#
# The two Nat reorderings the helper needs are the associativity/commutativity
# shuffles that put the scaled value equation next to the scale the goal carries.

# Rat.add.mixed.cross: the cross product mk.eqv.raw consumes in
# Rat.add.value.mixed, from the value equation v of the mk summand:
#
#   (A*Y + C*k1) * (d*Y)  ==  (R*Y + C*d) * (k1*Y)
#
# Both sides are read as "one summand scaled by the other's denominator" --
# A and R are the mk summand's numerator (projection and difference pair, the
# two sides of v) and C is the constructor summand's. The proof pushes each outer
# scale into its sum (mul_add_left), turns the two scales of each product into
# one (scale.pair, read backwards), applies v scaled by Y*Y to the first summand
# of each side, and reorders the pure-Nat scales of the second (mul_comm and
# mul_assoc inside Int.unit).
def Rat.add.mixed.cross(+A: I.Int, +R: I.Int, +C: I.Int, +d: Nat, +Yd: Nat, +k1: Nat,
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

# Rat.add.value.mixed: the goal's two sides are
#   add(mk(Rat.num(np1,nn1), d), Rat{Int{Zp,Zn}, D})   and   mk(T, dT)
# with P1 = sub(np1,nn1), Q1 = sub(nn1,np1), C = Int{Zp,Zn}, dT = d*D and T the
# raw sum of the two scaled pairs. Both arguments of the add are constructors
# once unfolded, so the left side is mk(nL, dL) with nL the two projections
# scaled by the *other* denominator (k1 = denof(M1) for the mk summand, D for the
# constructor) and dL = k1*D -- two normal forms compared by exactly the cross
# product Rat.add.mixed.cross assembles from the value equation v. The three
# facts it is built from:
#
#   v   mk.value on the mk summand: numof(M1)*d == Rat.num(P1,Q1)*k1, which is
#       already the difference-pair spelling the goal's T uses -- one sub_diag
#       per coordinate (ev) puts the raw pair Int{P1,Q1} there;
#   pd  the law's own positivity hypothesis (mk.value's);
#   pq  the law's second one: mk.eqv.raw needs the *output* denominator positive,
#       and pos_witness-style derivation is not available for a general d (the
#       witness type would have to be re-spelled), exactly as Rat.mk_idem.raw
#       documents.
#   pD  and the third: the *second* summand's denominator is now a general D, so
#       its positivity is a hypothesis too (it used to be 1+dp2, positive by
#       computation).
#
# The mk.eqv.raw call is the whole fill: no coprimality, no case split on the
# gcds, and no scale of the goal itself.
def R.Rat.add.value.mixed(np1, nn1, d, pd, pq, Zp, Zn, D, pD):
  +P1 = Nat.sub(np1, nn1)
  +Q1 = Nat.sub(nn1, np1)
  +M1 = R.Rat.mk(I.Int{P1, Q1}, d)
  +A = R.Rat.numof(M1)
  +k1 = R.Rat.denof(M1)
  +nL = I.Int.add(I.Int.mul(A, I.Int.unit(D)), I.Int.mul(I.Int{Zp, Zn}, I.Int.unit(k1)))
  +dL = Nat.mul(k1, D)
  +T = I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(D)), I.Int.mul(I.Int{Zp, Zn}, I.Int.unit(d)))
  +dT = Nat.mul(d, D)
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
    N.mul_pos(k1, D, pq, pD),
    N.mul_pos(d, D, pd, pD),
    Rat.add.mixed.cross(A, I.Int{P1, Q1}, I.Int{Zp, Zn}, d, D, k1, v))
# probe: Rat.neg_add -- -(x + y) = -x + -y for the canonical presentation.
# Rat.neg_add: the goal is
#   neg(add(Rat{Rat.num(np1,nn1), xd}, Rat{Rat.num(np2,nn2), yd}))   against
#   add(neg(Rat{Rat.num(np1,nn1), xd}), neg(Rat{Rat.num(np2,nn2), yd}))
# with xd = 1+dp1, yd = 1+dp2. The chain runs up the right-hand side and back
# down the left one:
#
#   av   Rat.add.value at the two negated pieces -- both are mk of a swapped
#        difference pair, which is exactly that law's shape -- giving mk(T, d)
#        with T the raw sum of the two scaled pairs;
#   teq  T == Int.neg(S): the coordinates differ only in the order of the two
#        summands *inside* each of the four sums (Int.neg swaps the pair's
#        sides, and Int.mul keeps the order of the sides it is handed), so it
#        is four Nat.add commutations under the constructor;
#   v    Rat.mk.value on the inner sum M1 = mk(S,d), whose raw coordinates are
#        (Sp, Sn) -- the two coordinates of S as mk destructures them;
#   nv   the negated value equation: Int.neg_mul moves the negation inside, and
#        Int.neg(Rat.num(Sp,Sn)) is Rat.num(Sn,Sp) by definition;
#   eqv  Rat.mk.eqv.raw at that cross product, rep Rat.mk.rep at the same
#        value -- so the left-hand side is mk(nL, dL) up to the definition of
#        Rat.neg, which is where the chain can stop.
def R.Rat.neg_add(np1, nn1, dp1, np2, nn2, dp2):
  +xd = Nat.add(1n, dp1)
  +yd = Nat.add(1n, dp2)
  +d = Nat.mul(xd, yd)
  +a1 = Nat.sub(np1, nn1)
  +b1 = Nat.sub(nn1, np1)
  +a2 = Nat.sub(np2, nn2)
  +b2 = Nat.sub(nn2, np2)
  +xn = R.Rat.num(np1, nn1)
  +yn = R.Rat.num(np2, nn2)
  +S = I.Int.add(I.Int.mul(xn, I.Int.unit(yd)), I.Int.mul(yn, I.Int.unit(xd)))
  +Sp = Nat.add(Nat.add(Nat.mul(a1, yd), Nat.mul(b1, 0n)), Nat.add(Nat.mul(a2, xd), Nat.mul(b2, 0n)))
  +Sn = Nat.add(Nat.add(Nat.mul(a1, 0n), Nat.mul(b1, yd)), Nat.add(Nat.mul(a2, 0n), Nat.mul(b2, xd)))
  +M1 = R.Rat.mk(S, d)
  +nL = I.Int.neg(R.Rat.numof(M1))
  +dL = R.Rat.denof(M1)
  +G = R.Rat.g(Sp, Sn, d)
  +T = I.Int.add(I.Int.mul(I.Int{b1, a1}, I.Int.unit(yd)), I.Int.mul(I.Int{b2, a2}, I.Int.unit(xd)))
  +X1 = Nat.add(Nat.mul(b1, yd), Nat.mul(a1, 0n))
  +X2 = Nat.add(Nat.mul(b2, xd), Nat.mul(a2, 0n))
  +Y1 = Nat.add(Nat.mul(b1, 0n), Nat.mul(a1, yd))
  +Y2 = Nat.add(Nat.mul(b2, 0n), Nat.mul(a2, xd))
  +A1 = Nat.add(Nat.mul(a1, 0n), Nat.mul(b1, yd))
  +A2 = Nat.add(Nat.mul(a2, 0n), Nat.mul(b2, xd))
  +B1 = Nat.add(Nat.mul(a1, yd), Nat.mul(b1, 0n))
  +B2 = Nat.add(Nat.mul(a2, xd), Nat.mul(b2, 0n))
  +C1 = Nat.add(X1, X2)
  +C2 = Nat.add(Y1, Y2)
  +eC1 = Equal.trans(Nat, C1, Nat.add(A1, X2), Sn,
    Equal.cong(Nat, Nat, w => Nat.add(w, X2), X1, A1,
      N.add_comm(Nat.mul(b1, yd), Nat.mul(a1, 0n))),
    Equal.cong(Nat, Nat, w => Nat.add(A1, w), X2, A2,
      N.add_comm(Nat.mul(b2, xd), Nat.mul(a2, 0n))))
  +eC2 = Equal.trans(Nat, C2, Nat.add(B1, Y2), Sp,
    Equal.cong(Nat, Nat, w => Nat.add(w, Y2), Y1, B1,
      N.add_comm(Nat.mul(b1, 0n), Nat.mul(a1, yd))),
    Equal.cong(Nat, Nat, w => Nat.add(B1, w), Y2, B2,
      N.add_comm(Nat.mul(b2, 0n), Nat.mul(a2, xd))))
  +teq = Equal.trans(I.Int, T, I.Int{Sn, C2}, I.Int{Sn, Sp},
    Equal.cong(Nat, I.Int, w => I.Int{w, C2}, C1, Sn, eC1),
    Equal.cong(Nat, I.Int, w => I.Int{Sn, w}, C2, Sp, eC2))
  +v = R.Rat.mk.value(Nat.cmp(Sp, Sn), Sp, Sn, d, {==}, N.mul_pos(xd, yd, {==}, {==}))
  +nv = Equal.trans(I.Int,
    I.Int.mul(I.Int.neg(R.Rat.numof(M1)), I.Int.unit(d)),
    I.Int.neg(I.Int.mul(R.Rat.numof(M1), I.Int.unit(d))),
    I.Int.mul(R.Rat.num(Sn, Sp), I.Int.unit(dL)),
    Equal.sym(I.Int, I.Int.neg(I.Int.mul(R.Rat.numof(M1), I.Int.unit(d))),
      I.Int.mul(I.Int.neg(R.Rat.numof(M1)), I.Int.unit(d)),
      I.Int.neg_mul(R.Rat.numof(M1), I.Int.unit(d))),
    Equal.trans(I.Int,
      I.Int.neg(I.Int.mul(R.Rat.numof(M1), I.Int.unit(d))),
      I.Int.neg(I.Int.mul(R.Rat.num(Sp, Sn), I.Int.unit(dL))),
      I.Int.mul(R.Rat.num(Sn, Sp), I.Int.unit(dL)),
      Equal.cong(I.Int, I.Int, u => I.Int.neg(u),
        I.Int.mul(R.Rat.numof(M1), I.Int.unit(d)),
        I.Int.mul(R.Rat.num(Sp, Sn), I.Int.unit(dL)), v),
      I.Int.neg_mul(R.Rat.num(Sp, Sn), I.Int.unit(dL))))
  +eqv = R.Rat.mk.eqv.raw(nL, dL, R.Rat.num(Sn, Sp), d,
    N.div_pos_wit(G, Nat.add(dp2, Nat.mul(dp1, Nat.add(1n, dp2))),
      Pair.snd(N.Nat.divides(G, R.Rat.mag(Sp, Sn)), N.Nat.divides(G, d), N.gcd_divides(R.Rat.mag(Sp, Sn), d))),
    N.mul_pos(xd, yd, {==}, {==}),
    nv)
  Equal.trans(R.Rat,
    R.Rat.mk(nL, dL),
    R.Rat.mk(T, d),
    R.Rat.add(R.Rat.neg(R.Rat{R.Rat.num(np1, nn1), xd}), R.Rat.neg(R.Rat{R.Rat.num(np2, nn2), yd})),
    Equal.trans(R.Rat,
      R.Rat.mk(nL, dL),
      R.Rat.mk(R.Rat.num(Sn, Sp), d),
      R.Rat.mk(T, d),
      eqv,
      Equal.trans(R.Rat,
        R.Rat.mk(R.Rat.num(Sn, Sp), d),
        R.Rat.mk(I.Int.neg(S), d),
        R.Rat.mk(T, d),
        R.Rat.mk.rep(Sn, Sp, d),
        Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, d), I.Int.neg(S), T, Equal.sym(I.Int, T, I.Int.neg(S), teq)))),
    Equal.sym(R.Rat,
      R.Rat.add(R.Rat.neg(R.Rat{R.Rat.num(np1, nn1), xd}), R.Rat.neg(R.Rat{R.Rat.num(np2, nn2), yd})),
      R.Rat.mk(T, d),
      R.Rat.add.value(nn1, np1, dp1, nn2, np2, dp2)))

# The Nat cross sum for Rat.add_assoc
# ===================================
#
# Rat.add_assoc's conclusion is an equality of two mk's over the *same*
# denominator D = Xd*(Yd*Zd), and Rat.mk.eqv.val closes it at the cross sum
#
#     TLp*D + TRn*D == TRp*D + TLn*D
#
# where TLp/TLn are the coordinates of the left mk's numerator and TRp/TRn the
# right one's: TLp = P1*Zd + a3*(Xd*Yd) and TRn = Q2*Xd + b1*(Yd*Zd), with
# (P1,Q1) the truncation pair of the left inner sum's raw coordinates and
# (P2,Q2) the right one's. Everything here is Nat arithmetic on those
# coordinates: no div, no gcd, no Rat.
#
# The derivation is the one PROVING.md records: Nat.sub_cross at each inner
# sum gives P1 + V1 = Q1 + U1 and P2 + V2 = Q2 + U2, scaled by Zd*D and Xd*D
# respectively and distributed, so that the two equations share their padding
# (the second summand's contribution, which is the only one both sums carry);
# Nat.cross_add combines them criss-cross, and its conclusion groups the four
# scaled products by *instance* rather than by the pairs mk.eqv.val names --
# so one four-term exchange (exch4) and two reassociations (foldA/foldB) turn
# it into the cross sum above. The scale factors are chosen so that the two
# paddings are the same product up to the order of the factors Xd and Zd,
# which pad settles.
#
# split is the scaled-and-distributed form of a sub_cross instance (with the
# padding respelled), flip2 exchanges the two summands inside an inner sum
# (instance 2 needs its own padding piece first), and d3/xy are the two
# denominator shorthands the statement is written with.

def Rat.nat.pad(+b: Nat, +Xd: Nat, +Zd: Nat, +D: Nat)
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

def Rat.nat.exch4(+x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat)
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

def Rat.nat.split(+P: Nat, +Q: Nat, +vg: Nat, +vp: Nat, +ug: Nat, +up: Nat, +s: Nat, +T: Nat, +T2: Nat,
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

# Rat.nat.d3(Xd,Yd,Zd) = Xd*(Yd*Zd): the common denominator the cross sum is scaled by.
def Rat.nat.d3(+Xd: Nat, +Yd: Nat, +Zd: Nat) -> Nat:
  Nat.mul(Xd, Nat.mul(Yd, Zd))

# Rat.nat.xy(Xd,Yd) = Xd*Yd: the first inner sum's denominator.
def Rat.nat.xy(+Xd: Nat, +Yd: Nat) -> Nat:
  Nat.mul(Xd, Yd)

# flip2: exchange the two summands inside each side's inner sum.
def Rat.nat.flip2(+P: Nat, +Q: Nat, +vp: Nat, +vg: Nat, +up: Nat, +ug: Nat,
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

# foldA: (c1*(Zd*D) + (c2*Yd)*(Xd*D)) = (c1*Zd + c2*(Xd*Yd)) * D
def Rat.nat.foldA(+c1: Nat, +c2: Nat, +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.add(Nat.mul(c1, Nat.mul(Zd, Rat.nat.d3(Xd, Yd, Zd))),
            Nat.mul(Nat.mul(c2, Yd), Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd))))
      == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}:
  %N.mul_assoc(c1, Zd, Rat.nat.d3(Xd, Yd, Zd))
    : {Nat.add(_, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd))))
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd))),
      Nat.mul(c2, Nat.mul(Yd, Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd)))),
      N.mul_assoc(c2, Yd, Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd))))
    : {Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.trans(Nat,
      Nat.mul(Rat.nat.xy(Xd, Yd), Rat.nat.d3(Xd, Yd, Zd)),
      Nat.mul(Nat.mul(Yd, Xd), Rat.nat.d3(Xd, Yd, Zd)),
      Nat.mul(Yd, Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd))),
      Equal.cong(Nat, Nat, v => Nat.mul(v, Rat.nat.d3(Xd, Yd, Zd)), Rat.nat.xy(Xd, Yd), Nat.mul(Yd, Xd), N.mul_comm(Xd, Yd)),
      N.mul_assoc(Yd, Xd, Rat.nat.d3(Xd, Yd, Zd)))
    : {Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.nat.d3(Xd, Yd, Zd)), Nat.mul(c2, _))
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %N.mul_assoc(c2, Rat.nat.xy(Xd, Yd), Rat.nat.d3(Xd, Yd, Zd))
    : {Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(c1, Zd), Rat.nat.d3(Xd, Yd, Zd)),
        Nat.mul(Nat.mul(c2, Rat.nat.xy(Xd, Yd)), Rat.nat.d3(Xd, Yd, Zd))),
      Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)),
      N.mul_add_left(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd)), Rat.nat.d3(Xd, Yd, Zd)))
    : {_ == Nat.mul(Nat.add(Nat.mul(c1, Zd), Nat.mul(c2, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  {==}

# foldB: (c1*(Xd*D) + (c2*Yd)*(Zd*D)) = (c1*Xd + c2*(Yd*Zd)) * D
def Rat.nat.foldB(+c1: Nat, +c2: Nat, +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.add(Nat.mul(c1, Nat.mul(Xd, Rat.nat.d3(Xd, Yd, Zd))),
            Nat.mul(Nat.mul(c2, Yd), Nat.mul(Zd, Rat.nat.d3(Xd, Yd, Zd))))
      == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}:
  %N.mul_assoc(c1, Xd, Rat.nat.d3(Xd, Yd, Zd))
    : {Nat.add(_, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Zd, Rat.nat.d3(Xd, Yd, Zd))))
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(c2, Yd), Nat.mul(Zd, Rat.nat.d3(Xd, Yd, Zd))),
      Nat.mul(c2, Nat.mul(Yd, Nat.mul(Zd, Rat.nat.d3(Xd, Yd, Zd)))),
      N.mul_assoc(c2, Yd, Nat.mul(Zd, Rat.nat.d3(Xd, Yd, Zd))))
    : {Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %N.mul_assoc(Yd, Zd, Rat.nat.d3(Xd, Yd, Zd))
    : {Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.nat.d3(Xd, Yd, Zd)), Nat.mul(c2, _))
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %N.mul_assoc(c2, Nat.mul(Yd, Zd), Rat.nat.d3(Xd, Yd, Zd))
    : {Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.nat.d3(Xd, Yd, Zd)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(c1, Xd), Rat.nat.d3(Xd, Yd, Zd)),
        Nat.mul(Nat.mul(c2, Nat.mul(Yd, Zd)), Rat.nat.d3(Xd, Yd, Zd))),
      Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)),
      N.mul_add_left(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd)), Rat.nat.d3(Xd, Yd, Zd)))
    : {_ == Nat.mul(Nat.add(Nat.mul(c1, Xd), Nat.mul(c2, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)) : Nat}
  {==}

# cross4: the cross sum mk.eqv.val consumes, from the two sub_cross instances.
def Rat.nat.cross4(+P1: Nat, +Q1: Nat, +P2: Nat, +Q2: Nat,
           +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +a3: Nat, +b3: Nat,
           +Xd: Nat, +Yd: Nat, +Zd: Nat,
           e1: {Nat.add(P1, Nat.add(Nat.mul(b1, Yd), Nat.mul(b2, Xd)))
                == Nat.add(Q1, Nat.add(Nat.mul(a1, Yd), Nat.mul(a2, Xd))) : Nat},
           e2: {Nat.add(P2, Nat.add(Nat.mul(b2, Zd), Nat.mul(b3, Yd)))
                == Nat.add(Q2, Nat.add(Nat.mul(a2, Zd), Nat.mul(a3, Yd))) : Nat})
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Zd), Nat.mul(a3, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd)),
           Nat.mul(Nat.add(Nat.mul(Q2, Xd), Nat.mul(b1, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(P2, Xd), Nat.mul(a1, Nat.mul(Yd, Zd))), Rat.nat.d3(Xd, Yd, Zd)),
                 Nat.mul(Nat.add(Nat.mul(Q1, Zd), Nat.mul(b3, Rat.nat.xy(Xd, Yd))), Rat.nat.d3(Xd, Yd, Zd))) : Nat}:
  +D = Rat.nat.d3(Xd, Yd, Zd)
  +s1 = Nat.mul(Zd, D)
  +s2 = Nat.mul(Xd, D)
  +A = Nat.add(Nat.mul(P1, s1), Nat.mul(Nat.mul(b1, Yd), s1))
  +A2 = Nat.add(Nat.mul(Q1, s1), Nat.mul(Nat.mul(a1, Yd), s1))
  +B = Nat.add(Nat.mul(P2, s2), Nat.mul(Nat.mul(b3, Yd), s2))
  +B2 = Nat.add(Nat.mul(Q2, s2), Nat.mul(Nat.mul(a3, Yd), s2))
  +Tb = Nat.mul(Nat.mul(b2, Zd), s2)
  +Ta = Nat.mul(Nat.mul(a2, Zd), s2)
  +e2f = Rat.nat.flip2(P2, Q2, Nat.mul(b2, Zd), Nat.mul(b3, Yd), Nat.mul(a2, Zd), Nat.mul(a3, Yd), e2)
  +h1 = Rat.nat.split(P1, Q1, Nat.mul(b1, Yd), Nat.mul(b2, Xd), Nat.mul(a1, Yd), Nat.mul(a2, Xd),
    s1, Tb, Ta, e1, Rat.nat.pad(b2, Xd, Zd, D), Rat.nat.pad(a2, Xd, Zd, D))
  +h2 = Rat.nat.split(P2, Q2, Nat.mul(b3, Yd), Nat.mul(b2, Zd), Nat.mul(a3, Yd), Nat.mul(a2, Zd),
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
  +xf = Rat.nat.exch4(x1, x2, x3, x4)
  +yf = Rat.nat.exch4(y1, y2, y3, y4)
  +r1 = Nat.mul(Nat.add(Nat.mul(P1, Zd), Nat.mul(a3, Rat.nat.xy(Xd, Yd))), D)
  +r2 = Nat.mul(Nat.add(Nat.mul(Q2, Xd), Nat.mul(b1, Nat.mul(Yd, Zd))), D)
  +r3 = Nat.mul(Nat.add(Nat.mul(P2, Xd), Nat.mul(a1, Nat.mul(Yd, Zd))), D)
  +r4 = Nat.mul(Nat.add(Nat.mul(Q1, Zd), Nat.mul(b3, Rat.nat.xy(Xd, Yd))), D)
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
          Rat.nat.foldA(P1, a3, Xd, Yd, Zd)),
        Equal.cong(Nat, Nat, u => Nat.add(r1, u), Nat.add(x2, x3), r2,
          Rat.nat.foldB(Q2, b1, Xd, Yd, Zd))))
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
          Rat.nat.foldA(Q1, b3, Xd, Yd, Zd)),
        Equal.trans(Nat,
          Nat.add(r4, Nat.add(y2, y3)),
          Nat.add(r4, r3),
          Nat.add(r3, r4),
          Equal.cong(Nat, Nat, u => Nat.add(r4, u), Nat.add(y2, y3), r3,
            Rat.nat.foldB(P2, a1, Xd, Yd, Zd)),
          N.add_comm(r4, r3))))
  Equal.trans(Nat,
    Nat.add(r1, r2),
    Nat.add(A, B2),
    Nat.add(r3, r4),
    Equal.sym(Nat, Nat.add(A, B2), Nat.add(r1, r2), lc),
    Equal.trans(Nat, Nat.add(A, B2), Nat.add(A2, B), Nat.add(r3, r4), c, rc))

# Rat.add_assoc: the chain runs up the left side and back down the right one.
#
#   eXY/eYZ  the two inner sums, re-spelled from the raw pair the operation
#            writes (each summand's difference pair scaled by the other's unit)
#            to the clean coordinates (U,V) -- one Int.mul_scale per summand,
#            under one cong on mk's argument;
#   L1-L2    carry that through the outer add (one cong) and turn the mk-headed
#            summand into mk(Rat.num(P1,Q1), d1) with Rat.mk.trunc -- the
#            presentation Rat.add.value.mixed is stated over;
#   L3       the mixed value law: the outer sum is mk of the raw sum of the two
#            scaled pairs, over the product d1*Zd;
#   L4       the raw sum collapses to the explicit pair Int{TLp,TLn} (two
#            sub_diag instances at the inner sum's own comparisons, then one
#            Int.mul_scale per summand) and the denominator to D = Xd*(Yd*Zd)
#            (one Nat.mul_assoc);
#   R0-R4    the right-hand side, mirrored: Rat.add_comm puts the mk-headed
#            summand first, and then the same four steps;
#   val      Rat.mk.eqv.val at the cross sum, with pD = mul_pos of the two
#            successive factors as both denominators' positivity.
#
# The two mixed-law calls take their positivity slots from the outside (that
# law is stated for a general mk denominator): pd is mul_pos of the two
# successors, and pq is div_pos_wit at the gcd spelling mk itself carries with
# the witness Nat.gcd_divides gives -- exactly as Rat.mul_assoc's fill
# supplies its two.
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
  +D = Rat.nat.d3(Xd, Yd, Zd)
  +TLp = Nat.add(Nat.mul(P1, Zd), Nat.mul(a3, Rat.nat.xy(Xd, Yd)))
  +TLn = Nat.add(Nat.mul(Q1, Zd), Nat.mul(b3, Rat.nat.xy(Xd, Yd)))
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
  +L3 = R.Rat.add.value.mixed(P1, Q1, d1, pd1, pq1,
    Nat.sub(np3, nn3), Nat.sub(nn3, np3), Zd, {==})
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
  +R3 = R.Rat.add.value.mixed(P2, Q2, d2, pd2, pq2,
    Nat.sub(np1, nn1), Nat.sub(nn1, np1), Xd, {==})
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
  +Hn = Rat.nat.cross4(P1, Q1, P2, Q2, a1, b1, a2, b2, a3, b3, Xd, Yd, Zd, ee1, ee2)
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

# Rat.add_exchange: three steps, no Nat arithmetic. add_comm moves the
# mk-headed inner sum to the front, add_assoc (read backwards, i.e. as this
# law's own statement with the summands in the order y, z, x) reassociates,
# and one congruence carries add_comm under the outer sum.
def R.Rat.add_exchange(np1, nn1, dp1, np2, nn2, dp2, np3, nn3, dp3):
  +Xd = Nat.add(1n, dp1)
  +Yd = Nat.add(1n, dp2)
  +Zd = Nat.add(1n, dp3)
  Equal.trans(R.Rat,
    R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd},
              R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
    R.Rat.add(R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
              R.Rat{R.Rat.num(np1, nn1), Xd}),
    R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd},
              R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
    R.Rat.add_comm(R.Rat{R.Rat.num(np1, nn1), Xd},
      R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
                R.Rat{R.Rat.num(np1, nn1), Xd}),
      R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd},
                R.Rat.add(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd})),
      R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd},
                R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
      R.Rat.add_assoc(np2, nn2, dp2, np3, nn3, dp3, np1, nn1, dp1),
      Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat{R.Rat.num(np2, nn2), Yd}, u),
        R.Rat.add(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd}),
        R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
        R.Rat.add_comm(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd}))))


# --- work in progress: mul_distrib ---

# value.coords.pos / .neg: the value equation of a scaled difference pair, read
# at its two Nat coordinates.
def Rat.value.coords.pos(+ap: Nat, +an: Nat, +rp: Nat, +rn: Nat, +d: Nat, +b: Nat,
            v: {I.Int{Nat.add(Nat.mul(ap, d), Nat.mul(an, 0n)),
                      Nat.add(Nat.mul(ap, 0n), Nat.mul(an, d))}
                == I.Int{Nat.add(Nat.mul(rp, b), Nat.mul(rn, 0n)),
                         Nat.add(Nat.mul(rp, 0n), Nat.mul(rn, b))} : I.Int})
  -> {Nat.add(Nat.mul(ap, d), Nat.mul(an, 0n)) == Nat.add(Nat.mul(rp, b), Nat.mul(rn, 0n)) : Nat}:
  I.Int.eq.pos(Nat.add(Nat.mul(ap, d), Nat.mul(an, 0n)), Nat.add(Nat.mul(ap, 0n), Nat.mul(an, d)),
    Nat.add(Nat.mul(rp, b), Nat.mul(rn, 0n)), Nat.add(Nat.mul(rp, 0n), Nat.mul(rn, b)), v)

def Rat.value.coords.neg(+ap: Nat, +an: Nat, +rp: Nat, +rn: Nat, +d: Nat, +b: Nat,
            v: {I.Int{Nat.add(Nat.mul(ap, d), Nat.mul(an, 0n)),
                      Nat.add(Nat.mul(ap, 0n), Nat.mul(an, d))}
                == I.Int{Nat.add(Nat.mul(rp, b), Nat.mul(rn, 0n)),
                         Nat.add(Nat.mul(rp, 0n), Nat.mul(rn, b))} : I.Int})
  -> {Nat.add(Nat.mul(ap, 0n), Nat.mul(an, d)) == Nat.add(Nat.mul(rp, 0n), Nat.mul(rn, b)) : Nat}:
  I.Int.eq.neg(Nat.add(Nat.mul(ap, d), Nat.mul(an, 0n)), Nat.add(Nat.mul(ap, 0n), Nat.mul(an, d)),
    Nat.add(Nat.mul(rp, b), Nat.mul(rn, 0n)), Nat.add(Nat.mul(rp, 0n), Nat.mul(rn, b)), v)


# value.scaled: the value equation of a scaled difference pair, multiplied by a
# positive unit C and read at one of its two coordinates. The equations are
# *unfolded* on purpose: `Int.mul(pair, unit d)` reduces as far as its arguments
# allow, so when the pair is substituted into a congruence body the result is
# the coordinate pair Int{add(mul(xp,d), mul(xn,0)), add(mul(xp,0), mul(xn,d))}
# -- not the folded Int{mul(xp,d), mul(xn,d)} that Int.mul_scale names. Both
# spellings appear below, each where it is the one the next step wants.
def Rat.value.scaled(+xp: Nat, +xn: Nat, +yp: Nat, +yn: Nat, +d: Nat, +b: Nat, +C: Nat,
            v: {I.Int{Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d))}
                == I.Int{Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b))} : I.Int})
  -> {I.Int{Nat.add(Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), C), Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), 0n)),
            Nat.add(Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), 0n), Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), C))}
      == I.Int{Nat.add(Nat.mul(Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), C), Nat.mul(Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b)), 0n)),
               Nat.add(Nat.mul(Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), 0n), Nat.mul(Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b)), C))} : I.Int}:
  Equal.cong(I.Int, I.Int, u => I.Int.mul(u, I.Int.unit(C)),
    I.Int{Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d))},
    I.Int{Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b))}, v)

# nat.coord.term: the surviving term of a coordinate, with its zero addend off
# -- the one rewrite both coordinates need first, kept separate because it is a
# plain instantiation of Nat.add_zero and because spelling it here keeps the
# two coordinate laws short.
def Rat.nat.coord.term(+x: Nat)
  -> {Nat.add(x, 0n) == x : Nat}:
  N.add_zero(x)

# nat.zero.add: 0 + x = x, read *backwards* from add_zero. `Nat.add` matches on
# its first argument, so `Nat.add(0n, x)` is stuck and `add_zero` (stated over
# the *other* order) does not reach it; the two steps are add_comm and
# add_zero. The value is a plain equation, so the lands are just their
# orientations: `Equal.sym` is handed the evidence in *its* order (`(a, b)` with
# `e : {a == b}`) and yields `{b == a}`, which is what running the chain
# backwards needs.
def Rat.nat.zero.add(+x: Nat)
  -> {Nat.add(0n, x) == x : Nat}:
  Equal.trans(Nat, Nat.add(0n, x), Nat.add(x, 0n), x,
    N.add_comm(0n, x), N.add_zero(x))

# nat.coord.first: the first coordinate of a *scaled* difference pair, with its
# zero product and zero addend off: mul(xp, mul(d, C)).
#
# Why `Equal.trans` and `Equal.cong` rather than `%`: the collapse of the
# surviving term's own zero product is the documented `%`-hole trap. `%` with
# the evidence `{mul(xp, 0n) == 0n}` demands the goal WITH that zero still in it
# as the annotation's endpoint, while the goal `Equal.trans` is being handed is
# already the collapsed `mul(xp, mul(d,C))` -- so the check fails with
# `expected : <goal>` against `observed : <the same goal, zero removed>`. The
# collapse is reached here through a `cong` on the product's *right* factor (a
# lambda body, so no annotation is involved) and only then collapsed; a bare
# `%` over the product context cannot express it. The lambda's type arguments
# are written out (`Nat, I.Int`, not `I.Int, I.Int`) as everywhere else.
#
# The zero products do not reduce (`Nat.mul` matches on its first argument, a
# variable), so they are laws; the first coordinate's stuck one is the *right*
# factor of the surviving product and its collapse is a `cong` on `u => mul(A,u)`
# -- `mul_zero` is stated `mul(x,0n) == 0n`, i.e. already in the orientation the
# goal wants, so no `Equal.sym` is needed there.
def Rat.nat.coord.first(+xp: Nat, +xn: Nat, +d: Nat, +C: Nat)
  -> {Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), C) == Nat.mul(xp, Nat.mul(d, C)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), C),
    Nat.mul(Nat.add(Nat.mul(xp, d), 0n), C),
    Nat.mul(xp, Nat.mul(d, C)),
    Equal.cong(Nat, Nat, u => Nat.mul(u, C), Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)),
      Nat.add(Nat.mul(xp, d), 0n),
      Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(xp, d), u), Nat.mul(xn, 0n), 0n,
        N.mul_zero(xn))),
    Equal.trans(Nat,
      Nat.mul(Nat.add(Nat.mul(xp, d), 0n), C),
      Nat.mul(Nat.mul(xp, d), C),
      Nat.mul(xp, Nat.mul(d, C)),
      Equal.cong(Nat, Nat, u => Nat.mul(u, C), Nat.add(Nat.mul(xp, d), 0n),
        Nat.mul(xp, d), Rat.nat.coord.term(Nat.mul(xp, d))),
      N.mul_assoc(xp, d, C)))

# nat.coord.second: the second coordinate of a scaled difference pair, with the
# zero product of the *first* addend and its zero addend off: mul(xn, mul(d, C)).
# The stuck zero is now the left factor of `mul(mul(xp,0n), C)`, so it comes off
# with `muL_zero` written in the evidence's own orientation (`0n == mul(xp,0n)`,
# via `Equal.sym`) under a `cong` on that product -- the mirror of
# nat.coord.first's `mul`-right hole, and the same reason (`%` would leave the
# zero in the endpoint it compares against).
def Rat.nat.coord.second(+xp: Nat, +xn: Nat, +d: Nat, +C: Nat)
  -> {Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), C) == Nat.mul(xn, Nat.mul(d, C)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), C),
    Nat.mul(Nat.mul(xn, d), C),
    Nat.mul(xn, Nat.mul(d, C)),
    Equal.cong(Nat, Nat, u => Nat.mul(u, C), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)),
      Nat.mul(xn, d),
      Equal.trans(Nat, Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), Nat.add(0n, Nat.mul(xn, d)),
        Nat.mul(xn, d),
        Equal.cong(Nat, Nat, u => Nat.add(u, Nat.mul(xn, d)), Nat.mul(xp, 0n), 0n,
          N.mul_zero(xp)),
        Rat.nat.zero.add(Nat.mul(xn, d)))),
    N.mul_assoc(xn, d, C))

# value.scaled.pos / .neg: the scaled value equation read at one of its two Nat
# coordinates, with the coordinate normalised to the scale-first product both
# sides of the composing laws are written in. The Int equation `v` reduces to
# the coordinate equation by Int.eq.pos / Int.eq.neg, and the normalisation is
# the two Nat laws above -- one per side, so four calls and three `cong`s: the
# three congs carry the rewrite under the *other* coordinate of the constructor
# (which the normalisation does not touch) and under the outer `Int` equality.
# Nothing here is specific to mul_distrib; a law whose value equation is scaled
# and then read coordinate-wise needs exactly this pair.
def Rat.value.scaled.pos(+xp: Nat, +xn: Nat, +yp: Nat, +yn: Nat, +d: Nat, +b: Nat, +C: Nat,
            v: {I.Int{Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d))}
                == I.Int{Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b))} : I.Int})
  -> {Nat.mul(xp, Nat.mul(d, C)) == Nat.mul(yp, Nat.mul(b, C)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(xp, Nat.mul(d, C)),
    Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), C),
    Nat.mul(yp, Nat.mul(b, C)),
    Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), C),
      Nat.mul(xp, Nat.mul(d, C)), Rat.nat.coord.first(xp, xn, d, C)),
    Equal.trans(Nat,
      Nat.mul(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), C),
      Nat.mul(Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), C),
      Nat.mul(yp, Nat.mul(b, C)),
      Equal.cong(Nat, Nat, u => Nat.mul(u, C),
        Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)),
        I.Int.eq.pos(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)),
          Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b)), v)),
      Rat.nat.coord.first(yp, yn, b, C)))

def Rat.value.scaled.neg(+xp: Nat, +xn: Nat, +yp: Nat, +yn: Nat, +d: Nat, +b: Nat, +C: Nat,
            v: {I.Int{Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d))}
                == I.Int{Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b))} : I.Int})
  -> {Nat.mul(xn, Nat.mul(d, C)) == Nat.mul(yn, Nat.mul(b, C)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(xn, Nat.mul(d, C)),
    Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), C),
    Nat.mul(yn, Nat.mul(b, C)),
    Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), C),
      Nat.mul(xn, Nat.mul(d, C)), Rat.nat.coord.second(xp, xn, d, C)),
    Equal.trans(Nat,
      Nat.mul(Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), C),
      Nat.mul(Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b)), C),
      Nat.mul(yn, Nat.mul(b, C)),
      Equal.cong(Nat, Nat, u => Nat.mul(u, C),
        Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b)),
        I.Int.eq.neg(Nat.add(Nat.mul(xp, d), Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d)),
          Nat.add(Nat.mul(yp, b), Nat.mul(yn, 0n)), Nat.add(Nat.mul(yp, 0n), Nat.mul(yn, b)), v)),
      Rat.nat.coord.second(yp, yn, b, C)))

# The Nat block for Rat.mul_distrib
# =================================
#
# Rat.mul_distrib is closed by three mk.eqv.val comparisons -- the left-hand
# side against a "value-cleared" U_L, U_L against the right-hand side's own
# unreduced sum U_R, and U_R against the right-hand side, which is one
# Rat.add.value away.  The last one needs no arithmetic at all; the first needs
# the inner sum's two value-equation coordinates (Rat.mk.value); the middle one
# is the pure Nat identity PROVING.md records as (T):
#
#     (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd == P1*Zd + P3*Yd + a1*Q2 + b1*P2
#
# Everything in this section is Nat arithmetic only -- no div, no gcd, no Rat.
# The route to (T) is the padded-hypotheses one: the inner sum's cross sum
# P2 + V2 = Q2 + U2, scaled by a1 and by b1 and combined by the swap shuffle,
# shares its padding with the two product pairs' cross sums scaled by Zd and
# Yd, so Nat.cross_add combines them criss-cross; the two "gather" facts put
# the multipliers next to the inner pair's coordinates on the way in.
#
# Rat.nat.distrib is oblivious to the one-sidedness of the coordinate pairs: it
# needs only the three cross sums and the two gather facts as hypotheses.
# Rat.nat.swap: (A + B) + (t + s) = (A + t) + (B + s)
def Rat.nat.swap(+A: Nat, +B: Nat, +t: Nat, +s: Nat)
  -> {Nat.add(Nat.add(A, B), Nat.add(t, s)) == Nat.add(Nat.add(A, t), Nat.add(B, s)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(A, B), Nat.add(t, s)), Nat.add(A, Nat.add(B, Nat.add(t, s))),
      N.add_assoc(A, B, Nat.add(t, s)))
    : {_ == Nat.add(Nat.add(A, t), Nat.add(B, s)) : Nat}
  %N.add_assoc(B, t, s)
    : {Nat.add(A, _) == Nat.add(Nat.add(A, t), Nat.add(B, s)) : Nat}
  %Equal.sym(Nat, Nat.add(B, t), Nat.add(t, B), N.add_comm(B, t))
    : {Nat.add(A, Nat.add(_, s)) == Nat.add(Nat.add(A, t), Nat.add(B, s)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(t, B), s), Nat.add(t, Nat.add(B, s)), N.add_assoc(t, B, s))
    : {Nat.add(A, _) == Nat.add(Nat.add(A, t), Nat.add(B, s)) : Nat}
  %N.add_assoc(A, t, Nat.add(B, s))
    : {_ == Nat.add(Nat.add(A, t), Nat.add(B, s)) : Nat}
  {==}

# Rat.nat.add2: two equations with their own paddings combine.
def Rat.nat.add2(+A: Nat, +t: Nat, +A2: Nat, +t2: Nat, +B: Nat, +s: Nat, +B2: Nat, +s2: Nat,
            e1: {Nat.add(A, t) == Nat.add(A2, t2) : Nat},
            e2: {Nat.add(B, s) == Nat.add(B2, s2) : Nat})
  -> {Nat.add(Nat.add(A, B), Nat.add(t, s)) == Nat.add(Nat.add(A2, B2), Nat.add(t2, s2)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(A, B), Nat.add(t, s)), Nat.add(Nat.add(A, t), Nat.add(B, s)),
      Rat.nat.swap(A, B, t, s))
    : {_ == Nat.add(Nat.add(A2, B2), Nat.add(t2, s2)) : Nat}
  %Equal.sym(Nat, Nat.add(A, t), Nat.add(A2, t2), e1)
    : {Nat.add(_, Nat.add(B, s)) == Nat.add(Nat.add(A2, B2), Nat.add(t2, s2)) : Nat}
  %Equal.sym(Nat, Nat.add(B, s), Nat.add(B2, s2), e2)
    : {Nat.add(Nat.add(A2, t2), _) == Nat.add(Nat.add(A2, B2), Nat.add(t2, s2)) : Nat}
  %Rat.nat.swap(A2, B2, t2, s2)
    : {_ == Nat.add(Nat.add(A2, B2), Nat.add(t2, s2)) : Nat}
  {==}

# Rat.nat.scale.eq: multiply a sum equation by c, distributed on both sides.
def Rat.nat.scale.eq(+c: Nat, +X: Nat, +Y: Nat, +X2: Nat, +Y2: Nat,
            e: {Nat.add(X, Y) == Nat.add(X2, Y2) : Nat})
  -> {Nat.add(Nat.mul(c, X), Nat.mul(c, Y)) == Nat.add(Nat.mul(c, X2), Nat.mul(c, Y2)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.mul(c, X), Nat.mul(c, Y)), Nat.mul(c, Nat.add(X, Y)),
      N.mul_distrib(c, X, Y))
    : {_ == Nat.add(Nat.mul(c, X2), Nat.mul(c, Y2)) : Nat}
  %Equal.sym(Nat, Nat.add(X, Y), Nat.add(X2, Y2), e)
    : {Nat.mul(c, _) == Nat.add(Nat.mul(c, X2), Nat.mul(c, Y2)) : Nat}
  %N.mul_distrib(c, X2, Y2)
    : {_ == Nat.add(Nat.mul(c, X2), Nat.mul(c, Y2)) : Nat}
  {==}

# Rat.nat.scale.eq.r: the right-scaled twin of Rat.nat.scale.eq.
def Rat.nat.scale.eq.r(+c: Nat, +X: Nat, +Y: Nat, +X2: Nat, +Y2: Nat,
            e: {Nat.add(X, Y) == Nat.add(X2, Y2) : Nat})
  -> {Nat.add(Nat.mul(X, c), Nat.mul(Y, c)) == Nat.add(Nat.mul(X2, c), Nat.mul(Y2, c)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.mul(X, c), Nat.mul(Y, c)), Nat.mul(Nat.add(X, Y), c),
      N.mul_add_left(X, Y, c))
    : {_ == Nat.add(Nat.mul(X2, c), Nat.mul(Y2, c)) : Nat}
  %Equal.sym(Nat, Nat.add(X, Y), Nat.add(X2, Y2), e)
    : {Nat.mul(_, c) == Nat.add(Nat.mul(X2, c), Nat.mul(Y2, c)) : Nat}
  %N.mul_add_left(X2, Y2, c)
    : {_ == Nat.add(Nat.mul(X2, c), Nat.mul(Y2, c)) : Nat}
  {==}

# Rat.nat.gather: a*(u*Zd + v*Yd) + b*(p*Zd + q*Yd) = (a*u + b*p)*Zd + (a*v + b*q)*Yd
def Rat.nat.gather(+a: Nat, +b: Nat, +u: Nat, +v: Nat, +p: Nat, +q: Nat, +Zd: Nat, +Yd: Nat)
  -> {Nat.add(Nat.mul(a, Nat.add(Nat.mul(u, Zd), Nat.mul(v, Yd))),
            Nat.mul(b, Nat.add(Nat.mul(p, Zd), Nat.mul(q, Yd))))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                 Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}:
  %N.mul_distrib(a, Nat.mul(u, Zd), Nat.mul(v, Yd))
    : {Nat.add(_, Nat.mul(b, Nat.add(Nat.mul(p, Zd), Nat.mul(q, Yd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %N.mul_distrib(b, Nat.mul(p, Zd), Nat.mul(q, Yd))
    : {Nat.add(Nat.add(Nat.mul(a, Nat.mul(u, Zd)), Nat.mul(a, Nat.mul(v, Yd))), _)
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %N.mul_assoc(a, u, Zd)
    : {Nat.add(Nat.add(_, Nat.mul(a, Nat.mul(v, Yd))),
               Nat.add(Nat.mul(b, Nat.mul(p, Zd)), Nat.mul(b, Nat.mul(q, Yd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %N.mul_assoc(a, v, Yd)
    : {Nat.add(Nat.add(Nat.mul(Nat.mul(a, u), Zd), _),
               Nat.add(Nat.mul(b, Nat.mul(p, Zd)), Nat.mul(b, Nat.mul(q, Yd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %N.mul_assoc(b, p, Zd)
    : {Nat.add(Nat.add(Nat.mul(Nat.mul(a, u), Zd), Nat.mul(Nat.mul(a, v), Yd)),
               Nat.add(_, Nat.mul(b, Nat.mul(q, Yd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %N.mul_assoc(b, q, Yd)
    : {Nat.add(Nat.add(Nat.mul(Nat.mul(a, u), Zd), Nat.mul(Nat.mul(a, v), Yd)),
               Nat.add(Nat.mul(Nat.mul(b, p), Zd), _))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(a, u), Zd), Nat.mul(Nat.mul(a, v), Yd)),
                          Nat.add(Nat.mul(Nat.mul(b, p), Zd), Nat.mul(Nat.mul(b, q), Yd))),
      Nat.add(Nat.add(Nat.mul(Nat.mul(a, u), Zd), Nat.mul(Nat.mul(b, p), Zd)),
              Nat.add(Nat.mul(Nat.mul(a, v), Yd), Nat.mul(Nat.mul(b, q), Yd))),
      Rat.nat.swap(Nat.mul(Nat.mul(a, u), Zd), Nat.mul(Nat.mul(a, v), Yd),
             Nat.mul(Nat.mul(b, p), Zd), Nat.mul(Nat.mul(b, q), Yd)))
    : {_ == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                    Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(a, u), Zd), Nat.mul(Nat.mul(b, p), Zd)),
      Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
      N.mul_add_left(Nat.mul(a, u), Nat.mul(b, p), Zd))
    : {Nat.add(_, Nat.add(Nat.mul(Nat.mul(a, v), Yd), Nat.mul(Nat.mul(b, q), Yd)))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(a, v), Yd), Nat.mul(Nat.mul(b, q), Yd)),
      Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd),
      N.mul_add_left(Nat.mul(a, v), Nat.mul(b, q), Yd))
    : {Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd), _)
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, p)), Zd),
                  Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, q)), Yd)) : Nat}
  {==}

# Rat.nat.distrib: (T) -- the Nat identity at the heart of Rat.mul_distrib:
#   (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd == P1*Zd + P3*Yd + a1*Q2 + b1*P2
# from the three cross sums of the pairs and the two "gather" facts that put
# the multipliers a1, b1 next to the second pair's coordinates.
def Rat.nat.distrib(+U1: Nat, +V1: Nat, +U2: Nat, +V2: Nat, +U3: Nat, +V3: Nat,
           +P1: Nat, +Q1: Nat, +P2: Nat, +Q2: Nat, +P3: Nat, +Q3: Nat,
           +a1: Nat, +b1: Nat, +Zd: Nat, +Yd: Nat,
           e1: {Nat.add(P1, V1) == Nat.add(Q1, U1) : Nat},
           +e2: {Nat.add(P2, V2) == Nat.add(Q2, U2) : Nat},
           +e3: {Nat.add(P3, V3) == Nat.add(Q3, U3) : Nat},
           ea: {Nat.add(Nat.mul(a1, U2), Nat.mul(b1, V2)) == Nat.add(Nat.mul(U1, Zd), Nat.mul(U3, Yd)) : Nat},
           eb: {Nat.add(Nat.mul(a1, V2), Nat.mul(b1, U2)) == Nat.add(Nat.mul(V1, Zd), Nat.mul(V3, Yd)) : Nat})
  -> {Nat.add(Nat.add(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Q1, Zd)), Nat.mul(Q3, Yd))
      == Nat.add(Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(P3, Yd)), Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}:
  +X = Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2))
  +XA = Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2))
  +YB = Nat.add(Nat.mul(P1, Zd), Nat.mul(P3, Yd))
  +YW = Nat.add(Nat.mul(Q1, Zd), Nat.mul(Q3, Yd))
  +VW = Nat.add(Nat.mul(V1, Zd), Nat.mul(V3, Yd))
  +UW = Nat.add(Nat.mul(U1, Zd), Nat.mul(U3, Yd))
  +f2a = Rat.nat.scale.eq(a1, P2, V2, Q2, U2, e2)
  +f2b = Rat.nat.scale.eq(b1, P2, V2, Q2, U2, e2)
  +hx = Rat.nat.add2(Nat.mul(a1, P2), Nat.mul(a1, V2), Nat.mul(a1, Q2), Nat.mul(a1, U2),
               Nat.mul(b1, Q2), Nat.mul(b1, U2), Nat.mul(b1, P2), Nat.mul(b1, V2),
               f2a, Equal.sym(Nat, Nat.add(Nat.mul(b1, P2), Nat.mul(b1, V2)),
                                   Nat.add(Nat.mul(b1, Q2), Nat.mul(b1, U2)), f2b))
  +ex = Equal.cong(Nat, Nat, u => Nat.add(X, u), Nat.add(Nat.mul(a1, V2), Nat.mul(b1, U2)), VW, eb)
  +ey = Equal.cong(Nat, Nat, u => Nat.add(XA, u), Nat.add(Nat.mul(a1, U2), Nat.mul(b1, V2)), UW, ea)
  +h1 = Equal.trans(Nat,
      Nat.add(X, VW),
      Nat.add(X, Nat.add(Nat.mul(a1, V2), Nat.mul(b1, U2))),
      Nat.add(XA, UW),
      Equal.sym(Nat, Nat.add(X, Nat.add(Nat.mul(a1, V2), Nat.mul(b1, U2))), Nat.add(X, VW), ex),
      Equal.trans(Nat,
        Nat.add(X, Nat.add(Nat.mul(a1, V2), Nat.mul(b1, U2))),
        Nat.add(XA, Nat.add(Nat.mul(a1, U2), Nat.mul(b1, V2))),
        Nat.add(XA, UW),
        hx, ey))
  +h2 = Rat.nat.add2(Nat.mul(P1, Zd), Nat.mul(V1, Zd), Nat.mul(Q1, Zd), Nat.mul(U1, Zd),
               Nat.mul(P3, Yd), Nat.mul(V3, Yd), Nat.mul(Q3, Yd), Nat.mul(U3, Yd),
               Rat.nat.scale.eq.r(Zd, P1, V1, Q1, U1, e1), Rat.nat.scale.eq.r(Yd, P3, V3, Q3, U3, e3))
  +c = N.cross_add(X, XA, YB, YW, VW, UW, h1, h2)
  %Equal.sym(Nat, Nat.add(Nat.add(X, Nat.mul(Q1, Zd)), Nat.mul(Q3, Yd)), Nat.add(X, YW),
      N.add_assoc(X, Nat.mul(Q1, Zd), Nat.mul(Q3, Yd)))
    : {_ == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  %Equal.sym(Nat, Nat.add(X, YW), Nat.add(XA, YB), c)
    : {_ == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  %Equal.sym(Nat, Nat.add(XA, YB), Nat.add(Nat.add(Nat.mul(a1, Q2), Nat.mul(P1, Zd)),
                                          Nat.add(Nat.mul(b1, P2), Nat.mul(P3, Yd))),
      Rat.nat.swap(Nat.mul(a1, Q2), Nat.mul(b1, P2), Nat.mul(P1, Zd), Nat.mul(P3, Yd)))
    : {_ == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(a1, Q2), Nat.mul(P1, Zd)), Nat.add(Nat.mul(P1, Zd), Nat.mul(a1, Q2)),
      N.add_comm(Nat.mul(a1, Q2), Nat.mul(P1, Zd)))
    : {Nat.add(_, Nat.add(Nat.mul(b1, P2), Nat.mul(P3, Yd)))
       == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(b1, P2), Nat.mul(P3, Yd)), Nat.add(Nat.mul(P3, Yd), Nat.mul(b1, P2)),
      N.add_comm(Nat.mul(b1, P2), Nat.mul(P3, Yd)))
    : {Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(a1, Q2)), _)
       == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(a1, Q2)),
                          Nat.add(Nat.mul(P3, Yd), Nat.mul(b1, P2))), Nat.add(YB, Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2))),
      Rat.nat.swap(Nat.mul(P1, Zd), Nat.mul(a1, Q2), Nat.mul(P3, Yd), Nat.mul(b1, P2)))
    : {_ == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  %N.add_assoc(YB, Nat.mul(a1, Q2), Nat.mul(b1, P2))
    : {_ == Nat.add(Nat.add(YB, Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat}
  {==}

# Rat.nat.pair.scale: (c1*x1 + c2*x2)*(d2*Xd) = (c1*y1 + c2*y2)*(Xd*m2), from the two
# scaled coordinates x1*(d2*Xd) = y1*(m2*Xd), x2*(d2*Xd) = y2*(m2*Xd).
def Rat.nat.pair.scale(+c1: Nat, +c2: Nat, +x1: Nat, +x2: Nat, +y1: Nat, +y2: Nat,
           +m2: Nat, +Xd: Nat, +d2: Nat,
           +e1: {Nat.mul(x1, Nat.mul(d2, Xd)) == Nat.mul(y1, Nat.mul(m2, Xd)) : Nat},
           +e2: {Nat.mul(x2, Nat.mul(d2, Xd)) == Nat.mul(y2, Nat.mul(m2, Xd)) : Nat})
  -> {Nat.mul(Nat.add(Nat.mul(c1, x1), Nat.mul(c2, x2)), Nat.mul(d2, Xd))
      == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}:
  %N.mul_add_left(Nat.mul(c1, x1), Nat.mul(c2, x2), Nat.mul(d2, Xd))
    : {_ == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(c1, x1), Nat.mul(d2, Xd)), Nat.mul(c1, Nat.mul(x1, Nat.mul(d2, Xd))),
      N.mul_assoc(c1, x1, Nat.mul(d2, Xd)))
    : {Nat.add(_, Nat.mul(Nat.mul(c2, x2), Nat.mul(d2, Xd)))
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x1, Nat.mul(d2, Xd)), Nat.mul(y1, Nat.mul(m2, Xd)), e1)
    : {Nat.add(Nat.mul(c1, _), Nat.mul(Nat.mul(c2, x2), Nat.mul(d2, Xd)))
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.mul(m2, Xd), Nat.mul(Xd, m2), N.mul_comm(m2, Xd))
    : {Nat.add(Nat.mul(c1, Nat.mul(y1, _)), Nat.mul(Nat.mul(c2, x2), Nat.mul(d2, Xd)))
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %N.mul_assoc(c1, y1, Nat.mul(Xd, m2))
    : {Nat.add(_, Nat.mul(Nat.mul(c2, x2), Nat.mul(d2, Xd)))
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(c2, x2), Nat.mul(d2, Xd)), Nat.mul(c2, Nat.mul(x2, Nat.mul(d2, Xd))),
      N.mul_assoc(c2, x2, Nat.mul(d2, Xd)))
    : {Nat.add(Nat.mul(Nat.mul(c1, y1), Nat.mul(Xd, m2)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x2, Nat.mul(d2, Xd)), Nat.mul(y2, Nat.mul(m2, Xd)), e2)
    : {Nat.add(Nat.mul(Nat.mul(c1, y1), Nat.mul(Xd, m2)), Nat.mul(c2, _))
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.mul(m2, Xd), Nat.mul(Xd, m2), N.mul_comm(m2, Xd))
    : {Nat.add(Nat.mul(Nat.mul(c1, y1), Nat.mul(Xd, m2)), Nat.mul(c2, Nat.mul(y2, _)))
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %N.mul_assoc(c2, y2, Nat.mul(Xd, m2))
    : {Nat.add(Nat.mul(Nat.mul(c1, y1), Nat.mul(Xd, m2)), _)
       == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(c1, y1), Nat.mul(Xd, m2)),
                          Nat.mul(Nat.mul(c2, y2), Nat.mul(Xd, m2))),
      Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)),
      N.mul_add_left(Nat.mul(c1, y1), Nat.mul(c2, y2), Nat.mul(Xd, m2)))
    : {_ == Nat.mul(Nat.add(Nat.mul(c1, y1), Nat.mul(c2, y2)), Nat.mul(Xd, m2)) : Nat}
  {==}

# Rat.nat.cross1: mk.eqv.val's hypothesis for LHS against U_L.
def Rat.nat.cross1(+a1: Nat, +b1: Nat, +q2p: Nat, +q2n: Nat, +P2: Nat, +Q2: Nat,
           +m2: Nat, +Xd: Nat, +d2: Nat,
           +e2p: {Nat.mul(q2p, Nat.mul(d2, Xd)) == Nat.mul(P2, Nat.mul(m2, Xd)) : Nat},
           +e2n: {Nat.mul(q2n, Nat.mul(d2, Xd)) == Nat.mul(Q2, Nat.mul(m2, Xd)) : Nat})
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(a1, q2p), Nat.mul(b1, q2n)), Nat.mul(d2, Xd)),
             Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Xd, m2)))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)),
                 Nat.mul(Nat.add(Nat.mul(a1, q2n), Nat.mul(b1, q2p)), Nat.mul(d2, Xd))) : Nat}:
  +hT1 = Rat.nat.pair.scale(a1, b1, q2p, q2n, P2, Q2, m2, Xd, d2, e2p, e2n)
  +hT4 = Rat.nat.pair.scale(a1, b1, q2n, q2p, Q2, P2, m2, Xd, d2, e2n, e2p)
  Equal.trans(Nat,
    Nat.add(Nat.mul(Nat.add(Nat.mul(a1, q2p), Nat.mul(b1, q2n)), Nat.mul(d2, Xd)),
            Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Xd, m2))),
    Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)),
            Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Xd, m2))),
    Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)),
            Nat.mul(Nat.add(Nat.mul(a1, q2n), Nat.mul(b1, q2p)), Nat.mul(d2, Xd))),
    Equal.cong(Nat, Nat,
      u => Nat.add(u, Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Xd, m2))),
      Nat.mul(Nat.add(Nat.mul(a1, q2p), Nat.mul(b1, q2n)), Nat.mul(d2, Xd)),
      Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)), hT1),
    Equal.sym(Nat,
      Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)),
              Nat.mul(Nat.add(Nat.mul(a1, q2n), Nat.mul(b1, q2p)), Nat.mul(d2, Xd))),
      Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)),
              Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Xd, m2))),
      Equal.cong(Nat, Nat,
        u => Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Xd, m2)), u),
        Nat.mul(Nat.add(Nat.mul(a1, q2n), Nat.mul(b1, q2p)), Nat.mul(d2, Xd)),
        Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Xd, m2)), hT4)))

# Rat.nat.dist4: ((A + B) + C) + D, scaled by F, distributed into its four products.
def Rat.nat.dist4(+A: Nat, +B: Nat, +C: Nat, +D: Nat, +F: Nat)
  -> {Nat.mul(Nat.add(Nat.add(Nat.add(A, B), C), D), F)
      == Nat.add(Nat.add(Nat.add(Nat.mul(A, F), Nat.mul(B, F)), Nat.mul(C, F)), Nat.mul(D, F)) : Nat}:
  %N.mul_add_left(Nat.add(Nat.add(A, B), C), D, F)
    : {_ == Nat.add(Nat.add(Nat.add(Nat.mul(A, F), Nat.mul(B, F)), Nat.mul(C, F)), Nat.mul(D, F)) : Nat}
  %N.mul_add_left(Nat.add(A, B), C, F)
    : {Nat.add(_, Nat.mul(D, F))
       == Nat.add(Nat.add(Nat.add(Nat.mul(A, F), Nat.mul(B, F)), Nat.mul(C, F)), Nat.mul(D, F)) : Nat}
  %N.mul_add_left(A, B, F)
    : {Nat.add(Nat.add(_, Nat.mul(C, F)), Nat.mul(D, F))
       == Nat.add(Nat.add(Nat.add(Nat.mul(A, F), Nat.mul(B, F)), Nat.mul(C, F)), Nat.mul(D, F)) : Nat}
  {==}

# Rat.nat.align.zd: the Z-paired coordinate's scaled product, re-associated from the
# (T)-side grouping to the (U_L, U_R) grouping.  Pure comm/assoc.
def Rat.nat.align.zd(+x: Nat, +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.mul(Nat.mul(x, Zd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))
      == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(x, Zd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.mul(x, Nat.mul(Zd, Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      N.mul_assoc(x, Zd, Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
    : {_ == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(Zd, Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))
    : {Nat.mul(x, _) == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(Zd, Xd, Yd)
    : {Nat.mul(x, Nat.mul(_, Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Zd, Xd), Nat.mul(Xd, Zd), N.mul_comm(Zd, Xd))
    : {Nat.mul(x, Nat.mul(Nat.mul(_, Yd), Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Xd, Zd), Yd), Nat.mul(Yd, Nat.mul(Xd, Zd)), N.mul_comm(Nat.mul(Xd, Zd), Yd))
    : {Nat.mul(x, Nat.mul(_, Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Xd, Zd), Nat.mul(Zd, Xd), N.mul_comm(Xd, Zd))
    : {Nat.mul(x, Nat.mul(Nat.mul(Yd, _), Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(Yd, Zd, Xd)
    : {Nat.mul(x, Nat.mul(_, Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Nat.mul(Yd, Zd), Xd), Nat.mul(Xd, Zd)),
      Nat.mul(Nat.mul(Xd, Zd), Nat.mul(Nat.mul(Yd, Zd), Xd)),
      N.mul_comm(Nat.mul(Nat.mul(Yd, Zd), Xd), Nat.mul(Xd, Zd)))
    : {Nat.mul(x, _) == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(x, Nat.mul(Xd, Zd), Nat.mul(Nat.mul(Yd, Zd), Xd))
    : {_ == Nat.mul(Nat.mul(x, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  {==}

# Rat.nat.align.yd: the Y-paired coordinate's twin.
def Rat.nat.align.yd(+x: Nat, +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.mul(Nat.mul(x, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))
      == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(x, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.mul(x, Nat.mul(Yd, Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      N.mul_assoc(x, Yd, Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
    : {_ == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(Yd, Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))
    : {Nat.mul(x, _) == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(Yd, Xd, Yd)
    : {Nat.mul(x, Nat.mul(_, Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Yd, Xd), Nat.mul(Xd, Yd), N.mul_comm(Yd, Xd))
    : {Nat.mul(x, Nat.mul(Nat.mul(_, Yd), Nat.mul(Xd, Zd)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Nat.mul(Xd, Yd), Yd), Nat.mul(Xd, Zd)),
      Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Yd, Nat.mul(Xd, Zd))),
      N.mul_assoc(Nat.mul(Xd, Yd), Yd, Nat.mul(Xd, Zd)))
    : {Nat.mul(x, _) == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %Equal.sym(Nat, Nat.mul(Xd, Zd), Nat.mul(Zd, Xd), N.mul_comm(Xd, Zd))
    : {Nat.mul(x, Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Yd, _)))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(Yd, Zd, Xd)
    : {Nat.mul(x, Nat.mul(Nat.mul(Xd, Yd), _))
       == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  %N.mul_assoc(x, Nat.mul(Xd, Yd), Nat.mul(Nat.mul(Yd, Zd), Xd))
    : {_ == Nat.mul(Nat.mul(x, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)) : Nat}
  {==}

# Rat.nat.tl.scaled: the (T) left side, scaled by d1*d3, rewritten into the
# (U_L, U_R) grouping: ULp*(d1*d3) + URn*(d2*Xd).
def Rat.nat.tl.scaled(+a1: Nat, +b1: Nat, +P2: Nat, +Q2: Nat, +Q1: Nat, +Q3: Nat,
           +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.mul(Nat.add(Nat.add(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Q1, Zd)), Nat.mul(Q3, Yd)),
            Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                 Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                         Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}:
  %Equal.sym(Nat,
      Nat.mul(Nat.add(Nat.add(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Q1, Zd)), Nat.mul(Q3, Yd)),
              Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                             Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                       Nat.mul(Nat.mul(Q1, Zd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
              Nat.mul(Nat.mul(Q3, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      Rat.nat.dist4(Nat.mul(a1, P2), Nat.mul(b1, Q2), Nat.mul(Q1, Zd), Nat.mul(Q3, Yd),
        Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
    : {_ == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                    Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                            Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Q1, Zd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.mul(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
      Rat.nat.align.zd(Q1, Xd, Yd, Zd))
    : {Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                               Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                     _),
              Nat.mul(Nat.mul(Q3, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                  Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Q3, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.mul(Nat.mul(Q3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
      Rat.nat.align.yd(Q3, Xd, Yd, Zd))
    : {Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                               Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                     Nat.mul(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
              _)
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                  Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                                               Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                                     Nat.mul(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
                            Nat.mul(Nat.mul(Q3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
      Nat.add(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                      Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
              Nat.add(Nat.mul(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                      Nat.mul(Nat.mul(Q3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)))),
      N.add_assoc(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                          Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                  Nat.mul(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                  Nat.mul(Nat.mul(Q3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))))
    : {_ == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                    Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                            Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                          Nat.mul(Nat.mul(Q3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
      Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
              Nat.mul(Nat.mul(Yd, Zd), Xd)),
      N.mul_add_left(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)))
    : {Nat.add(Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                        Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))), _)
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                  Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(a1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                          Nat.mul(Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      N.mul_add_left(Nat.mul(a1, P2), Nat.mul(b1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
    : {Nat.add(_, Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd)))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                  Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd))) : Nat}
  {==}

# Rat.nat.tr.scaled: the (T) right side, scaled the same way: URp*(d2*Xd) + ULn*(d1*d3).
def Rat.nat.tr.scaled(+a1: Nat, +b1: Nat, +P1: Nat, +P2: Nat, +P3: Nat, +Q1: Nat, +Q2: Nat, +Q3: Nat,
           +Xd: Nat, +Yd: Nat, +Zd: Nat)
  -> {Nat.mul(Nat.add(Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(P3, Yd)), Nat.mul(a1, Q2)), Nat.mul(b1, P2)),
            Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                         Nat.mul(Nat.mul(Yd, Zd), Xd)),
                 Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                         Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}:
  +Q0 = Nat.mul(Q1, Nat.mul(Xd, Zd))
  %Equal.sym(Nat,
      Nat.mul(Nat.add(Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(P3, Yd)), Nat.mul(a1, Q2)), Nat.mul(b1, P2)),
              Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(P1, Zd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                             Nat.mul(Nat.mul(P3, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                       Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
              Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      Rat.nat.dist4(Nat.mul(P1, Zd), Nat.mul(P3, Yd), Nat.mul(a1, Q2), Nat.mul(b1, P2),
        Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
    : {_ == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                            Nat.mul(Nat.mul(Yd, Zd), Xd)),
                    Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                            Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(P1, Zd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.mul(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
      Rat.nat.align.zd(P1, Xd, Yd, Zd))
    : {Nat.add(Nat.add(Nat.add(_, Nat.mul(Nat.mul(P3, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                       Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
              Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd)),
                  Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                          Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(P3, Yd), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      Nat.mul(Nat.mul(P3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
      Rat.nat.align.yd(P3, Xd, Yd, Zd))
    : {Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)), _),
                       Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
              Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd)),
                  Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                          Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                                               Nat.mul(Nat.mul(P3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
                                     Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
                            Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      Nat.add(Nat.add(Nat.mul(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                      Nat.mul(Nat.mul(P3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
              Nat.add(Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                      Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))),
      N.add_assoc(Nat.add(Nat.mul(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                          Nat.mul(Nat.mul(P3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
                  Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                  Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))))
    : {_ == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                            Nat.mul(Nat.mul(Yd, Zd), Xd)),
                    Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                            Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(Nat.mul(Yd, Zd), Xd)),
                          Nat.mul(Nat.mul(P3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd))),
      Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
              Nat.mul(Nat.mul(Yd, Zd), Xd)),
      N.mul_add_left(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd)), Nat.mul(Nat.mul(Yd, Zd), Xd)))
    : {Nat.add(_, Nat.add(Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                          Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))))
       == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd)),
                  Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                          Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.mul(a1, Q2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
                          Nat.mul(Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))),
      Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
      N.mul_add_left(Nat.mul(a1, Q2), Nat.mul(b1, P2), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))))
    : {Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                       Nat.mul(Nat.mul(Yd, Zd), Xd)), _)
       == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                          Nat.mul(Nat.mul(Yd, Zd), Xd)),
                  Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                          Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}
  {==}

# Rat.nat.cross2: mk.eqv.val's hypothesis for U_L against U_R, from (T) scaled by
# d1*d3 (the U_R denominator).  No value equation: the two sides are pure ring
# reassociations of (T)'s two sides.
def Rat.nat.cross2(+a1: Nat, +b1: Nat, +P1: Nat, +Q1: Nat, +P2: Nat, +Q2: Nat, +P3: Nat, +Q3: Nat,
           +Xd: Nat, +Yd: Nat, +Zd: Nat,
           t: {Nat.add(Nat.add(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Q1, Zd)), Nat.mul(Q3, Yd))
               == Nat.add(Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(P3, Yd)), Nat.mul(a1, Q2)), Nat.mul(b1, P2)) : Nat})
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))),
             Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                     Nat.mul(Nat.mul(Yd, Zd), Xd)))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                         Nat.mul(Nat.mul(Yd, Zd), Xd)),
                 Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)),
                         Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd)))) : Nat}:
  +tL = Nat.add(Nat.add(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), Nat.mul(Q1, Zd)), Nat.mul(Q3, Yd))
  +tR = Nat.add(Nat.add(Nat.add(Nat.mul(P1, Zd), Nat.mul(P3, Yd)), Nat.mul(a1, Q2)), Nat.mul(b1, P2))
  +dRu = Nat.mul(Nat.mul(Xd, Yd), Nat.mul(Xd, Zd))
  +tl = Rat.nat.tl.scaled(a1, b1, P2, Q2, Q1, Q3, Xd, Yd, Zd)
  +tr = Rat.nat.tr.scaled(a1, b1, P1, P2, P3, Q1, Q2, Q3, Xd, Yd, Zd)
  Equal.trans(Nat,
    Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), dRu),
            Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                    Nat.mul(Nat.mul(Yd, Zd), Xd))),
    Nat.mul(tL, dRu),
    Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                    Nat.mul(Nat.mul(Yd, Zd), Xd)),
            Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), dRu)),
    Equal.sym(Nat, Nat.mul(tL, dRu),
      Nat.add(Nat.mul(Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2)), dRu),
              Nat.mul(Nat.add(Nat.mul(Q1, Nat.mul(Xd, Zd)), Nat.mul(Q3, Nat.mul(Xd, Yd))),
                      Nat.mul(Nat.mul(Yd, Zd), Xd))), tl),
    Equal.trans(Nat,
      Nat.mul(tL, dRu),
      Nat.mul(tR, dRu),
      Nat.add(Nat.mul(Nat.add(Nat.mul(P1, Nat.mul(Xd, Zd)), Nat.mul(P3, Nat.mul(Xd, Yd))),
                      Nat.mul(Nat.mul(Yd, Zd), Xd)),
              Nat.mul(Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2)), dRu)),
      Equal.cong(Nat, Nat, u => Nat.mul(u, dRu), tL, tR, t),
      tr))

# Rat.mul_distrib
# ===============
#
# The chain runs up the left side and back down the right one:
#
#   eYZ/L1   the inner sum re-spelled from the raw pair the operation writes
#            (each summand's difference pair scaled by the other's unit) to the
#            clean coordinates (U2,V2) -- one Int.mul_scale per summand under
#            one cong on mk's argument -- and carried through the outer mul;
#   v2       Rat.mk.value at M2, read at both coordinates and scaled by Xd:
#            the two equations Rat.nat.cross1 consumes;
#   val1     Rat.mk.eqv.val at the cross sum, the left-hand side against U_L;
#   T        the pure Nat identity (T) -- three Nat.sub_cross instances plus the
#            two gather facts (the multipliers next to the inner pair);
#   val2     Rat.mk.eqv.val again, U_L against U_R over d1*d3;
#   r1-r3    U_R against the right-hand side: Rat.mk.rep backwards on each
#            summand (denominators rewritten to the successor spelling
#            Rat.add.value is stated over, by pos_witness), Rat.add.value, and
#            Int.mul_scale plus the two denominators back.
#
# The positivity slots are the products of successors (mul_pos) and the inner
# quotient (div_pos_wit on the witness Nat.gcd_divides returns), exactly as
# Rat.add_assoc supplies its two. No coprimality, no case split, no comparison
# parameter.
def R.Rat.mul_distrib(np1, nn1, dp1, np2, nn2, dp2, np3, nn3, dp3):
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
  +U1 = Nat.add(Nat.mul(a1, a2), Nat.mul(b1, b2))
  +V1 = Nat.add(Nat.mul(a1, b2), Nat.mul(b1, a2))
  +U3 = Nat.add(Nat.mul(a1, a3), Nat.mul(b1, b3))
  +V3 = Nat.add(Nat.mul(a1, b3), Nat.mul(b1, a3))
  +U2 = Nat.add(Nat.mul(a2, Zd), Nat.mul(a3, Yd))
  +V2 = Nat.add(Nat.mul(b2, Zd), Nat.mul(b3, Yd))
  +d1 = Nat.mul(Xd, Yd)
  +d2 = Nat.mul(Yd, Zd)
  +d3 = Nat.mul(Xd, Zd)
  +M1 = R.Rat.mk(I.Int{U1, V1}, d1)
  +M2 = R.Rat.mk(I.Int{U2, V2}, d2)
  +M3 = R.Rat.mk(I.Int{U3, V3}, d3)
  +P1 = Nat.sub(U1, V1)
  +Q1 = Nat.sub(V1, U1)
  +P2 = Nat.sub(U2, V2)
  +Q2 = Nat.sub(V2, U2)
  +P3 = Nat.sub(U3, V3)
  +Q3 = Nat.sub(V3, U3)
  +G2 = R.Rat.g(U2, V2, d2)
  +m2 = Nat.div(d2, G2)
  +q2p = Nat.div(P2, G2)
  +q2n = Nat.div(Q2, G2)
  +TLp = Nat.add(Nat.mul(a1, q2p), Nat.mul(b1, q2n))
  +TLn = Nat.add(Nat.mul(a1, q2n), Nat.mul(b1, q2p))
  +ULp = Nat.add(Nat.mul(a1, P2), Nat.mul(b1, Q2))
  +ULn = Nat.add(Nat.mul(a1, Q2), Nat.mul(b1, P2))
  +URp = Nat.add(Nat.mul(P1, d3), Nat.mul(P3, d1))
  +URn = Nat.add(Nat.mul(Q1, d3), Nat.mul(Q3, d1))
  +dLu = Nat.mul(d2, Xd)
  +dRu = Nat.mul(d1, d3)
  +UL = R.Rat.mk(I.Int{ULp, ULn}, dLu)
  +UR = R.Rat.mk(I.Int{URp, URn}, dRu)
  +rawYZ = I.Int.add(I.Int.mul(yn, I.Int.unit(Zd)), I.Int.mul(zn, I.Int.unit(Yd)))
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
  +L1 = Equal.cong(R.Rat, R.Rat, u => R.Rat.mul(R.Rat{xn, Xd}, u),
    R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd}), M2, eYZ)
  +pd2 = N.mul_pos(Yd, Zd, {==}, {==})
  +v2 = R.Rat.mk.value(Nat.cmp(U2, V2), U2, V2, d2, {==}, pd2)
  +e2p = Rat.value.scaled.pos(q2p, q2n, P2, Q2, d2, m2, Xd, v2)
  +e2n = Rat.value.scaled.neg(q2p, q2n, P2, Q2, d2, m2, Xd, v2)
  +cross1f = Rat.nat.cross1(a1, b1, q2p, q2n, P2, Q2, m2, Xd, d2, e2p, e2n)
  +pq2 = N.div_pos_wit(G2, Nat.add(dp3, Nat.mul(dp2, Nat.add(1n, dp3))),
    Pair.snd(N.Nat.divides(G2, R.Rat.mag(U2, V2)), N.Nat.divides(G2, d2),
             N.gcd_divides(R.Rat.mag(U2, V2), d2)))
  +posL = N.mul_pos(Xd, m2, {==}, pq2)
  +posLu = N.mul_pos(d2, Xd, pd2, {==})
  +val1 = R.Rat.mk.eqv.val(TLp, TLn, Nat.mul(Xd, m2), posL, ULp, ULn, dLu, posLu, cross1f)
  +ee1 = N.sub_cross(Nat.cmp(U1, V1), U1, V1, {==})
  +ee2 = N.sub_cross(Nat.cmp(U2, V2), U2, V2, {==})
  +ee3 = N.sub_cross(Nat.cmp(U3, V3), U3, V3, {==})
  +ea = Rat.nat.gather(a1, b1, a2, a3, b2, b3, Zd, Yd)
  +eb = Rat.nat.gather(a1, b1, b2, b3, a2, a3, Zd, Yd)
  +T = Rat.nat.distrib(U1, V1, U2, V2, U3, V3, P1, Q1, P2, Q2, P3, Q3, a1, b1, Zd, Yd,
    ee1, ee2, ee3, ea, eb)
  +cross2f = Rat.nat.cross2(a1, b1, P1, Q1, P2, Q2, P3, Q3, Xd, Yd, Zd, T)
  +pd1 = N.mul_pos(Xd, Yd, {==}, {==})
  +pd3 = N.mul_pos(Xd, Zd, {==}, {==})
  +posRu = N.mul_pos(d1, d3, pd1, pd3)
  +val2 = R.Rat.mk.eqv.val(ULp, ULn, dLu, posLu, URp, URn, dRu, posRu, cross2f)
  +ds1 = Nat.add(1n, Nat.sub(d1, 1n))
  +ds3 = Nat.add(1n, Nat.sub(d3, 1n))
  +e1s = Equal.sym(Nat, d1, ds1, N.pos_witness(d1, pd1))
  +e3s = Equal.sym(Nat, d3, ds3, N.pos_witness(d3, pd3))
  +hM1 = Equal.trans(R.Rat,
    M1,
    R.Rat.mk(R.Rat.num(U1, V1), d1),
    R.Rat.mk(R.Rat.num(U1, V1), ds1),
    Equal.sym(R.Rat, R.Rat.mk(R.Rat.num(U1, V1), d1), M1, R.Rat.mk.rep(U1, V1, d1)),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(R.Rat.num(U1, V1), u), d1, ds1, N.pos_witness(d1, pd1)))
  +hM3 = Equal.trans(R.Rat,
    M3,
    R.Rat.mk(R.Rat.num(U3, V3), d3),
    R.Rat.mk(R.Rat.num(U3, V3), ds3),
    Equal.sym(R.Rat, R.Rat.mk(R.Rat.num(U3, V3), d3), M3, R.Rat.mk.rep(U3, V3, d3)),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(R.Rat.num(U3, V3), u), d3, ds3, N.pos_witness(d3, pd3)))
  +r1 = Equal.trans(R.Rat,
    R.Rat.add(M1, M3),
    R.Rat.add(R.Rat.mk(R.Rat.num(U1, V1), ds1), M3),
    R.Rat.add(R.Rat.mk(R.Rat.num(U1, V1), ds1), R.Rat.mk(R.Rat.num(U3, V3), ds3)),
    Equal.cong(R.Rat, R.Rat, u => R.Rat.add(u, M3), M1, R.Rat.mk(R.Rat.num(U1, V1), ds1), hM1),
    Equal.cong(R.Rat, R.Rat, u => R.Rat.add(R.Rat.mk(R.Rat.num(U1, V1), ds1), u), M3,
      R.Rat.mk(R.Rat.num(U3, V3), ds3), hM3))
  +r2 = R.Rat.add.value(U1, V1, Nat.sub(d1, 1n), U3, V3, Nat.sub(d3, 1n))
  +argA0 = I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(ds3)), I.Int.mul(I.Int{P3, Q3}, I.Int.unit(ds1)))
  +argA1 = I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(d3)), I.Int.mul(I.Int{P3, Q3}, I.Int.unit(ds1)))
  +argA2 = I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(d3)), I.Int.mul(I.Int{P3, Q3}, I.Int.unit(d1)))
  +r3i = Equal.trans(I.Int,
    argA0,
    argA2,
    I.Int{URp, URn},
    Equal.trans(I.Int,
      argA0,
      argA1,
      argA2,
      Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(I.Int{P3, Q3}, I.Int.unit(ds1))),
        I.Int.mul(I.Int{P1, Q1}, I.Int.unit(ds3)), I.Int.mul(I.Int{P1, Q1}, I.Int.unit(d3)),
        Equal.cong(I.Int, I.Int, u => I.Int.mul(I.Int{P1, Q1}, u), I.Int.unit(ds3), I.Int.unit(d3),
          Equal.cong(Nat, I.Int, v => I.Int{v, 0n}, ds3, d3, e3s))),
      Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int.mul(I.Int{P1, Q1}, I.Int.unit(d3)), u),
        I.Int.mul(I.Int{P3, Q3}, I.Int.unit(ds1)), I.Int.mul(I.Int{P3, Q3}, I.Int.unit(d1)),
        Equal.cong(I.Int, I.Int, u => I.Int.mul(I.Int{P3, Q3}, u), I.Int.unit(ds1), I.Int.unit(d1),
          Equal.cong(Nat, I.Int, v => I.Int{v, 0n}, ds1, d1, e1s)))),
    Equal.trans(I.Int,
      argA2,
      I.Int.add(I.Int{Nat.mul(P1, d3), Nat.mul(Q1, d3)}, I.Int.mul(I.Int{P3, Q3}, I.Int.unit(d1))),
      I.Int{URp, URn},
      Equal.cong(I.Int, I.Int, u => I.Int.add(u, I.Int.mul(I.Int{P3, Q3}, I.Int.unit(d1))),
        I.Int.mul(I.Int{P1, Q1}, I.Int.unit(d3)), I.Int{Nat.mul(P1, d3), Nat.mul(Q1, d3)},
        I.Int.mul_scale(P1, Q1, d3)),
      Equal.cong(I.Int, I.Int, u => I.Int.add(I.Int{Nat.mul(P1, d3), Nat.mul(Q1, d3)}, u),
        I.Int.mul(I.Int{P3, Q3}, I.Int.unit(d1)), I.Int{Nat.mul(P3, d1), Nat.mul(Q3, d1)},
        I.Int.mul_scale(P3, Q3, d1))))
  +r3d = Equal.trans(Nat,
    Nat.mul(ds1, ds3),
    Nat.mul(d1, ds3),
    Nat.mul(d1, d3),
    Equal.cong(Nat, Nat, u => Nat.mul(u, ds3), ds1, d1, e1s),
    Equal.cong(Nat, Nat, u => Nat.mul(d1, u), ds3, d3, e3s))
  +r3 = Equal.trans(R.Rat,
    R.Rat.mk(argA0, Nat.mul(ds1, ds3)),
    R.Rat.mk(I.Int{URp, URn}, Nat.mul(ds1, ds3)),
    UR,
    Equal.cong(I.Int, R.Rat, u => R.Rat.mk(u, Nat.mul(ds1, ds3)), argA0, I.Int{URp, URn}, r3i),
    Equal.cong(Nat, R.Rat, u => R.Rat.mk(I.Int{URp, URn}, u), Nat.mul(ds1, ds3), dRu, r3d))
  +eR = Equal.trans(R.Rat,
    R.Rat.add(M1, M3),
    R.Rat.add(R.Rat.mk(R.Rat.num(U1, V1), ds1), R.Rat.mk(R.Rat.num(U3, V3), ds3)),
    UR,
    r1,
    Equal.trans(R.Rat,
      R.Rat.add(R.Rat.mk(R.Rat.num(U1, V1), ds1), R.Rat.mk(R.Rat.num(U3, V3), ds3)),
      R.Rat.mk(argA0, Nat.mul(ds1, ds3)),
      UR,
      r2, r3))
  Equal.trans(R.Rat,
    R.Rat.mul(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd})),
    R.Rat.mk(I.Int{TLp, TLn}, Nat.mul(Xd, m2)),
    R.Rat.add(R.Rat.mul(R.Rat{xn, Xd}, R.Rat{yn, Yd}), R.Rat.mul(R.Rat{xn, Xd}, R.Rat{zn, Zd})),
    Equal.trans(R.Rat,
      R.Rat.mul(R.Rat{xn, Xd}, R.Rat.add(R.Rat{yn, Yd}, R.Rat{zn, Zd})),
      R.Rat.mul(R.Rat{xn, Xd}, M2),
      R.Rat.mk(I.Int{TLp, TLn}, Nat.mul(Xd, m2)),
      L1,
      {==}),
    Equal.trans(R.Rat,
      R.Rat.mk(I.Int{TLp, TLn}, Nat.mul(Xd, m2)),
      UL,
      R.Rat.add(R.Rat.mul(R.Rat{xn, Xd}, R.Rat{yn, Yd}), R.Rat.mul(R.Rat{xn, Xd}, R.Rat{zn, Zd})),
      val1,
      Equal.trans(R.Rat,
        UL,
        UR,
        R.Rat.add(R.Rat.mul(R.Rat{xn, Xd}, R.Rat{yn, Yd}), R.Rat.mul(R.Rat{xn, Xd}, R.Rat{zn, Zd})),
        val2,
        Equal.sym(R.Rat,
          R.Rat.add(R.Rat.mul(R.Rat{xn, Xd}, R.Rat{yn, Yd}), R.Rat.mul(R.Rat{xn, Xd}, R.Rat{zn, Zd})),
          UR, eR))))

# Rat.mul_add_left: three steps and two congruences. mul_comm moves z in front
# of the sum so that mul_distrib applies, and the two products come back in the
# order the statement names -- one congruence each, under the outer add.
def R.Rat.mul_add_left(np1, nn1, dp1, np2, nn2, dp2, np3, nn3, dp3):
  +Xd = Nat.add(1n, dp1)
  +Yd = Nat.add(1n, dp2)
  +Zd = Nat.add(1n, dp3)
  Equal.trans(R.Rat,
    R.Rat.mul(R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np2, nn2), Yd}),
              R.Rat{R.Rat.num(np3, nn3), Zd}),
    R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd},
              R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np2, nn2), Yd})),
    R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
              R.Rat.mul(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
    R.Rat.mul_comm(R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np2, nn2), Yd}),
                   R.Rat{R.Rat.num(np3, nn3), Zd}),
    Equal.trans(R.Rat,
      R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd},
                R.Rat.add(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np2, nn2), Yd})),
      R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd}),
                R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np2, nn2), Yd})),
      R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
                R.Rat.mul(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
      R.Rat.mul_distrib(np3, nn3, dp3, np1, nn1, dp1, np2, nn2, dp2),
      Equal.trans(R.Rat,
        R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd}),
                  R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np2, nn2), Yd})),
        R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
                  R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np2, nn2), Yd})),
        R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
                  R.Rat.mul(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd})),
        Equal.cong(R.Rat, R.Rat,
          u => R.Rat.add(u, R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np2, nn2), Yd})),
          R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd}),
          R.Rat.mul(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
          R.Rat.mul_comm(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np1, nn1), Xd})),
        Equal.cong(R.Rat, R.Rat,
          u => R.Rat.add(R.Rat.mul(R.Rat{R.Rat.num(np1, nn1), Xd}, R.Rat{R.Rat.num(np3, nn3), Zd}), u),
          R.Rat.mul(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np2, nn2), Yd}),
          R.Rat.mul(R.Rat{R.Rat.num(np2, nn2), Yd}, R.Rat{R.Rat.num(np3, nn3), Zd}),
          R.Rat.mul_comm(R.Rat{R.Rat.num(np3, nn3), Zd}, R.Rat{R.Rat.num(np2, nn2), Yd})))))
