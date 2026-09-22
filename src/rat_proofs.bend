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
