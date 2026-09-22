import Base
import ./int.bend as I
import ./nat.bend as N
import ./nat_proofs.bend as NP

# Int proofs
# ==========
#
# Fills every law of int.bend. Nat evidence is called through N (the
# nat.bend alias); the nat_proofs.bend import is what fills those laws (the
# fill attaches to the nat.bend module, so N.<lemma> resolves).
#
# Every proof below is a rewrite chain over the two Nat coordinates: there is
# no case analysis on sign anywhere, because Int.add / Int.mul are
# constructors and never stuck. `int.bend` states the orientation each lemma
# is used in, so most steps need no Equal.sym.

def I.Int.add_comm(x, y):
  match x y:
    case I.Int{xp, xn} I.Int{yp, yn}:
      %N.add_comm(xp, yp) : {I.Int{Nat.add(xp, yp), Nat.add(xn, yn)} == I.Int{_, Nat.add(yn, xn)} : I.Int}
      %N.add_comm(xn, yn) : {I.Int{Nat.add(xp, yp), Nat.add(xn, yn)} == I.Int{Nat.add(xp, yp), _} : I.Int}
      {==}

def I.Int.add_assoc(x, y, z):
  match x y z:
    case I.Int{xp, xn} I.Int{yp, yn} I.Int{zp, zn}:
      %N.add_assoc(xp, yp, zp) : {I.Int{Nat.add(Nat.add(xp, yp), zp), Nat.add(Nat.add(xn, yn), zn)} == I.Int{_, Nat.add(xn, Nat.add(yn, zn))} : I.Int}
      %N.add_assoc(xn, yn, zn) : {I.Int{Nat.add(Nat.add(xp, yp), zp), Nat.add(Nat.add(xn, yn), zn)} == I.Int{Nat.add(Nat.add(xp, yp), zp), _} : I.Int}
      {==}

def I.Int.add_exchange(x, y, z):
  match x y z:
    case I.Int{xp, xn} I.Int{yp, yn} I.Int{zp, zn}:
      %N.add_exchange(xp, yp, zp) : {I.Int{Nat.add(xp, Nat.add(yp, zp)), Nat.add(xn, Nat.add(yn, zn))} == I.Int{_, Nat.add(yn, Nat.add(xn, zn))} : I.Int}
      %N.add_exchange(xn, yn, zn) : {I.Int{Nat.add(xp, Nat.add(yp, zp)), Nat.add(xn, Nat.add(yn, zn))} == I.Int{Nat.add(xp, Nat.add(yp, zp)), _} : I.Int}
      {==}

def I.Int.add_zero(x):
  match x:
    case I.Int{xp, xn}:
      %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{_, Nat.add(xn, 0n)} == I.Int{xp, xn} : I.Int}
      %Equal.sym(Nat, Nat.add(xn, 0n), xn, N.add_zero(xn)) : {I.Int{xp, _} == I.Int{xp, xn} : I.Int}
      {==}

def I.Int.zero_add(x):
  match x:
    case I.Int{xp, xn}:
      {==}

def I.Int.neg_invol(x):
  match x:
    case I.Int{xp, xn}:
      {==}

def I.Int.neg_add(x, y):
  match x y:
    case I.Int{xp, xn} I.Int{yp, yn}:
      {==}

def I.Int.neg_mul(x, y):
  match x y:
    case I.Int{xp, xn} I.Int{yp, yn}:
      %N.add_comm(Nat.mul(xp, yn), Nat.mul(xn, yp)) : {I.Int{Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn))} == I.Int{_, Nat.add(Nat.mul(xn, yn), Nat.mul(xp, yp))} : I.Int}
      %N.add_comm(Nat.mul(xp, yp), Nat.mul(xn, yn)) : {I.Int{Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn))} == I.Int{Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), _} : I.Int}
      {==}

def I.Int.sub_eq_add_neg(x, y):
  match x y:
    case I.Int{xp, xn} I.Int{yp, yn}:
      {==}

def I.Int.mul_comm(x, y):
  match x y:
    case I.Int{xp, xn} I.Int{yp, yn}:
      %N.mul_comm(xp, yp) : {I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp))} == I.Int{Nat.add(_, Nat.mul(yn, xn)), Nat.add(Nat.mul(yp, xn), Nat.mul(yn, xp))} : I.Int}
      %N.mul_comm(xn, yn) : {I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp))} == I.Int{Nat.add(Nat.mul(xp, yp), _), Nat.add(Nat.mul(yp, xn), Nat.mul(yn, xp))} : I.Int}
      %N.mul_comm(xn, yp) : {I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp))} == I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(_, Nat.mul(yn, xp))} : I.Int}
      %N.mul_comm(xp, yn) : {I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp))} == I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xn, yp), _)} : I.Int}
      %N.add_comm(Nat.mul(xp, yn), Nat.mul(xn, yp)) : {I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp))} == I.Int{Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), _} : I.Int}
      {==}

# The two Nat halves of Int.mul_assoc, spelled out so each chain only ever
# mentions one coordinate. See the law comments in int.bend.
def I.Int.mul_assoc.pos(xp, xn, yp, yn, zp, zn):
  %N.mul_add_left(Nat.mul(xp, yp), Nat.mul(xn, yn), zp) : {Nat.add(_, Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zn)) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %N.mul_add_left(Nat.mul(xp, yn), Nat.mul(xn, yp), zn) : {Nat.add(Nat.add(Nat.mul(Nat.mul(xp, yp), zp), Nat.mul(Nat.mul(xn, yn), zp)), _) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xp, yp), zp), Nat.mul(xp, Nat.mul(yp, zp)), N.mul_assoc(xp, yp, zp)) : {Nat.add(Nat.add(_, Nat.mul(Nat.mul(xn, yn), zp)), Nat.add(Nat.mul(Nat.mul(xp, yn), zn), Nat.mul(Nat.mul(xn, yp), zn))) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xn, yn), zp), Nat.mul(xn, Nat.mul(yn, zp)), N.mul_assoc(xn, yn, zp)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), _), Nat.add(Nat.mul(Nat.mul(xp, yn), zn), Nat.mul(Nat.mul(xn, yp), zn))) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xp, yn), zn), Nat.mul(xp, Nat.mul(yn, zn)), N.mul_assoc(xp, yn, zn)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zp))), Nat.add(_, Nat.mul(Nat.mul(xn, yp), zn))) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xn, yp), zn), Nat.mul(xn, Nat.mul(yp, zn)), N.mul_assoc(xn, yp, zn)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zp))), Nat.add(Nat.mul(xp, Nat.mul(yn, zn)), _)) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %N.mul_distrib(xp, Nat.mul(yp, zp), Nat.mul(yn, zn)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zp))), Nat.add(Nat.mul(xp, Nat.mul(yn, zn)), Nat.mul(xn, Nat.mul(yp, zn)))) == Nat.add(_, Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))) : Nat}
  %N.mul_distrib(xn, Nat.mul(yp, zn), Nat.mul(yn, zp)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zp))), Nat.add(Nat.mul(xp, Nat.mul(yn, zn)), Nat.mul(xn, Nat.mul(yp, zn)))) == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xp, Nat.mul(yn, zn))), _) : Nat}
  %N.add_assoc_rev(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zp)), Nat.add(Nat.mul(xp, Nat.mul(yn, zn)), Nat.mul(xn, Nat.mul(yp, zn)))) : {_ == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xp, Nat.mul(yn, zn))), Nat.add(Nat.mul(xn, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zp)))) : Nat}
  %N.add_exchange(Nat.mul(xp, Nat.mul(yn, zn)), Nat.mul(xn, Nat.mul(yn, zp)), Nat.mul(xn, Nat.mul(yp, zn))) : {Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), _) == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xp, Nat.mul(yn, zn))), Nat.add(Nat.mul(xn, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zp)))) : Nat}
  %N.add_comm(Nat.mul(xn, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zp))) : {Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.add(Nat.mul(xp, Nat.mul(yn, zn)), _)) == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xp, Nat.mul(yn, zn))), Nat.add(Nat.mul(xn, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zp)))) : Nat}
  %N.add_assoc(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xp, Nat.mul(yn, zn)), Nat.add(Nat.mul(xn, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zp)))) : {_ == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zp)), Nat.mul(xp, Nat.mul(yn, zn))), Nat.add(Nat.mul(xn, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zp)))) : Nat}
  {==}

def I.Int.mul_assoc.neg(xp, xn, yp, yn, zp, zn):
  %N.mul_add_left(Nat.mul(xp, yp), Nat.mul(xn, yn), zn) : {Nat.add(_, Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zp)) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %N.mul_add_left(Nat.mul(xp, yn), Nat.mul(xn, yp), zp) : {Nat.add(Nat.add(Nat.mul(Nat.mul(xp, yp), zn), Nat.mul(Nat.mul(xn, yn), zn)), _) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xp, yp), zn), Nat.mul(xp, Nat.mul(yp, zn)), N.mul_assoc(xp, yp, zn)) : {Nat.add(Nat.add(_, Nat.mul(Nat.mul(xn, yn), zn)), Nat.add(Nat.mul(Nat.mul(xp, yn), zp), Nat.mul(Nat.mul(xn, yp), zp))) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xn, yn), zn), Nat.mul(xn, Nat.mul(yn, zn)), N.mul_assoc(xn, yn, zn)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), _), Nat.add(Nat.mul(Nat.mul(xp, yn), zp), Nat.mul(Nat.mul(xn, yp), zp))) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xp, yn), zp), Nat.mul(xp, Nat.mul(yn, zp)), N.mul_assoc(xp, yn, zp)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zn))), Nat.add(_, Nat.mul(Nat.mul(xn, yp), zp))) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(xn, yp), zp), Nat.mul(xn, Nat.mul(yp, zp)), N.mul_assoc(xn, yp, zp)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zn))), Nat.add(Nat.mul(xp, Nat.mul(yn, zp)), _)) == Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %N.mul_distrib(xp, Nat.mul(yp, zn), Nat.mul(yn, zp)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zn))), Nat.add(Nat.mul(xp, Nat.mul(yn, zp)), Nat.mul(xn, Nat.mul(yp, zp)))) == Nat.add(_, Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))) : Nat}
  %N.mul_distrib(xn, Nat.mul(yp, zp), Nat.mul(yn, zn)) : {Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zn))), Nat.add(Nat.mul(xp, Nat.mul(yn, zp)), Nat.mul(xn, Nat.mul(yp, zp)))) == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xp, Nat.mul(yn, zp))), _) : Nat}
  %N.add_assoc_rev(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xn, Nat.mul(yn, zn)), Nat.add(Nat.mul(xp, Nat.mul(yn, zp)), Nat.mul(xn, Nat.mul(yp, zp)))) : {_ == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xp, Nat.mul(yn, zp))), Nat.add(Nat.mul(xn, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zn)))) : Nat}
  %N.add_exchange(Nat.mul(xp, Nat.mul(yn, zp)), Nat.mul(xn, Nat.mul(yn, zn)), Nat.mul(xn, Nat.mul(yp, zp))) : {Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), _) == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xp, Nat.mul(yn, zp))), Nat.add(Nat.mul(xn, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zn)))) : Nat}
  %N.add_comm(Nat.mul(xn, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zn))) : {Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.add(Nat.mul(xp, Nat.mul(yn, zp)), _)) == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xp, Nat.mul(yn, zp))), Nat.add(Nat.mul(xn, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zn)))) : Nat}
  %N.add_assoc(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xp, Nat.mul(yn, zp)), Nat.add(Nat.mul(xn, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zn)))) : {_ == Nat.add(Nat.add(Nat.mul(xp, Nat.mul(yp, zn)), Nat.mul(xp, Nat.mul(yn, zp))), Nat.add(Nat.mul(xn, Nat.mul(yp, zp)), Nat.mul(xn, Nat.mul(yn, zn)))) : Nat}
  {==}

def I.Int.mul_assoc(x, y, z):
  match x y z:
    case I.Int{xp, xn} I.Int{yp, yn} I.Int{zp, zn}:
      %Equal.sym(Nat,
        Nat.add(Nat.mul(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), zp), Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zn)),
        Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))),
        I.Int.mul_assoc.pos(xp, xn, yp, yn, zp, zn))
        : {I.Int{_, Nat.add(Nat.mul(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), zn), Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zp))} == I.Int{Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))), Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))))} : I.Int}
      %Equal.sym(Nat,
        Nat.add(Nat.mul(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), zn), Nat.mul(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), zp)),
        Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn)))),
        I.Int.mul_assoc.neg(xp, xn, yp, yn, zp, zn))
        : {I.Int{Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))), _} == I.Int{Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))), Nat.mul(xn, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp)))), Nat.add(Nat.mul(xp, Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))), Nat.mul(xn, Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))))} : I.Int}
      {==}

def I.Int.mul_swap(a, b, c):
  Equal.trans(I.Int,
    I.Int.mul(I.Int.mul(a, b), c),
    I.Int.mul(a, I.Int.mul(b, c)),
    I.Int.mul(I.Int.mul(a, c), b),
    I.Int.mul_assoc(a, b, c),
    Equal.trans(I.Int,
      I.Int.mul(a, I.Int.mul(b, c)),
      I.Int.mul(a, I.Int.mul(c, b)),
      I.Int.mul(I.Int.mul(a, c), b),
      Equal.cong(I.Int, I.Int, v => I.Int.mul(a, v),
        I.Int.mul(b, c), I.Int.mul(c, b), I.Int.mul_comm(b, c)),
      Equal.sym(I.Int,
        I.Int.mul(I.Int.mul(a, c), b),
        I.Int.mul(a, I.Int.mul(c, b)),
        I.Int.mul_assoc(a, c, b))))

# The two sides of mul_distrib bracket the same four products differently --
# (a + c) + (b + d) on the left, (a + b) + (c + d) on the right, with
# a = xp*yp, b = xn*yn, c = xp*zp, d = xn*zn (and the neg half with
# e = xp*yn, f = xn*yp, g = xp*zn, h = xn*zp). Three rewrites walk each.
# Int.mul_scale: unfold the product and take the two zero products off. Nat.mul
# matches on its first argument, so mul(xn, 0) is stuck while the add(0, ..) its
# sibling leaves behind reduces: one mul_zero and one add_zero per coordinate.
def I.Int.mul_scale(xp, xn, d):
  %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int{Nat.add(Nat.mul(xp, d), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d))} == I.Int{Nat.mul(xp, d), Nat.mul(xn, d)} : I.Int}
  %Equal.sym(Nat, Nat.add(Nat.mul(xp, d), 0n), Nat.mul(xp, d), N.add_zero(Nat.mul(xp, d))) : {I.Int{_, Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, d))} == I.Int{Nat.mul(xp, d), Nat.mul(xn, d)} : I.Int}
  %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int{Nat.mul(xp, d), Nat.add(_, Nat.mul(xn, d))} == I.Int{Nat.mul(xp, d), Nat.mul(xn, d)} : I.Int}
  {==}

def I.Int.mul_distrib(x, y, z):
  match x y z:
    case I.Int{xp, xn} I.Int{yp, yn} I.Int{zp, zn}:
      %N.mul_distrib(xp, yp, zp) : {I.Int{Nat.add(_, Nat.mul(xn, Nat.add(yn, zn))), Nat.add(Nat.mul(xp, Nat.add(yn, zn)), Nat.mul(xn, Nat.add(yp, zp)))} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.mul_distrib(xn, yn, zn) : {I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xp, zp)), _), Nat.add(Nat.mul(xp, Nat.add(yn, zn)), Nat.mul(xn, Nat.add(yp, zp)))} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.mul_distrib(xp, yn, zn) : {I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xp, zp)), Nat.add(Nat.mul(xn, yn), Nat.mul(xn, zn))), Nat.add(_, Nat.mul(xn, Nat.add(yp, zp)))} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.mul_distrib(xn, yp, zp) : {I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xp, zp)), Nat.add(Nat.mul(xn, yn), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xp, zn)), _)} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.add_assoc_rev(Nat.mul(xp, yp), Nat.mul(xp, zp), Nat.add(Nat.mul(xn, yn), Nat.mul(xn, zn))) : {I.Int{_, Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xp, zn)), Nat.add(Nat.mul(xn, yp), Nat.mul(xn, zp)))} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.add_exchange(Nat.mul(xn, yn), Nat.mul(xp, zp), Nat.mul(xn, zn)) : {I.Int{Nat.add(Nat.mul(xp, yp), _), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xp, zn)), Nat.add(Nat.mul(xn, yp), Nat.mul(xn, zp)))} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.add_assoc(Nat.mul(xp, yp), Nat.mul(xn, yn), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))) : {I.Int{_, Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xp, zn)), Nat.add(Nat.mul(xn, yp), Nat.mul(xn, zp)))} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.add_assoc_rev(Nat.mul(xp, yn), Nat.mul(xp, zn), Nat.add(Nat.mul(xn, yp), Nat.mul(xn, zp))) : {I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), _} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.add_exchange(Nat.mul(xn, yp), Nat.mul(xp, zn), Nat.mul(xn, zp)) : {I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.mul(xp, yn), _)} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      %N.add_assoc(Nat.mul(xp, yn), Nat.mul(xn, yp), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp))) : {I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), _} == I.Int{Nat.add(Nat.add(Nat.mul(xp, yp), Nat.mul(xn, yn)), Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))), Nat.add(Nat.add(Nat.mul(xp, yn), Nat.mul(xn, yp)), Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp)))} : I.Int}
      {==}

def I.Int.mul_add_left(x, y, z):
  Equal.trans(I.Int,
    I.Int.mul(I.Int.add(x, y), z),
    I.Int.mul(z, I.Int.add(x, y)),
    I.Int.add(I.Int.mul(x, z), I.Int.mul(y, z)),
    I.Int.mul_comm(I.Int.add(x, y), z),
    Equal.trans(I.Int,
      I.Int.mul(z, I.Int.add(x, y)),
      I.Int.add(I.Int.mul(z, x), I.Int.mul(z, y)),
      I.Int.add(I.Int.mul(x, z), I.Int.mul(y, z)),
      I.Int.mul_distrib(z, x, y),
      Equal.trans(I.Int,
        I.Int.add(I.Int.mul(z, x), I.Int.mul(z, y)),
        I.Int.add(I.Int.mul(x, z), I.Int.mul(z, y)),
        I.Int.add(I.Int.mul(x, z), I.Int.mul(y, z)),
        Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.mul(z, y)),
          I.Int.mul(z, x), I.Int.mul(x, z), I.Int.mul_comm(z, x)),
        Equal.cong(I.Int, I.Int, v => I.Int.add(I.Int.mul(x, z), v),
          I.Int.mul(z, y), I.Int.mul(y, z), I.Int.mul_comm(z, y)))))

def I.Int.mul_zero(x):
  match x:
    case I.Int{xp, xn}:
      %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int{Nat.add(_, Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 0n))} == I.Int{0n, 0n} : I.Int}
      %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int{Nat.add(0n, Nat.mul(xn, 0n)), Nat.add(_, Nat.mul(xn, 0n))} == I.Int{0n, 0n} : I.Int}
      %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int{Nat.add(0n, _), Nat.add(0n, Nat.mul(xn, 0n))} == I.Int{0n, 0n} : I.Int}
      %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int{Nat.add(0n, 0n), Nat.add(0n, _)} == I.Int{0n, 0n} : I.Int}
      {==}

def I.Int.mul_one(x):
  match x:
    case I.Int{xp, xn}:
      %N.mul_one(xp) : {I.Int{Nat.add(_, Nat.mul(xn, 0n)), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n))} == I.Int{xp, xn} : I.Int}
      %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int{Nat.add(xp, _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n))} == I.Int{xp, xn} : I.Int}
      %N.mul_one(xn) : {I.Int{Nat.add(xp, 0n), Nat.add(Nat.mul(xp, 0n), _)} == I.Int{xp, xn} : I.Int}
      %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int{Nat.add(xp, 0n), Nat.add(_, xn)} == I.Int{xp, xn} : I.Int}
      %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{_, Nat.add(0n, xn)} == I.Int{xp, xn} : I.Int}
      {==}

def I.Int.one_mul(x):
  match x:
    case I.Int{xp, xn}:
      %Equal.sym(Nat, Nat.add(Nat.add(xp, 0n), 0n), xp,
        Equal.trans(Nat, Nat.add(Nat.add(xp, 0n), 0n), Nat.add(xp, 0n), xp,
          N.add_zero(Nat.add(xp, 0n)), N.add_zero(xp)))
        : {I.Int{_, Nat.add(Nat.add(xn, 0n), 0n)} == I.Int{xp, xn} : I.Int}
      %Equal.sym(Nat, Nat.add(Nat.add(xn, 0n), 0n), xn,
        Equal.trans(Nat, Nat.add(Nat.add(xn, 0n), 0n), Nat.add(xn, 0n), xn,
          N.add_zero(Nat.add(xn, 0n)), N.add_zero(xn)))
        : {I.Int{xp, _} == I.Int{xp, xn} : I.Int}
      {==}

def I.Int.canon.pos(a, e):
  %Equal.sym(Cmp, Nat.cmp(a, 0n), GT{}, e) : {I.Int.canon.go(_, a, 0n) == I.Int{a, 0n} : I.Int}
  %Equal.sym(Nat, Nat.sub(a, 0n), a, N.sub_zero(a)) : {I.Int{_, 0n} == I.Int{a, 0n} : I.Int}
  {==}

def I.Int.canon.neg(a, e):
  %Equal.sym(Cmp, Nat.cmp(0n, a), LT{}, e) : {I.Int.canon.go(_, 0n, a) == I.Int{0n, a} : I.Int}
  %Equal.sym(Nat, Nat.sub(a, 0n), a, N.sub_zero(a)) : {I.Int{0n, _} == I.Int{0n, a} : I.Int}
  {==}

def I.Int.canon.idem(c, xp, xn, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      I.Int.canon.pos(Nat.sub(xp, xn),
        Equal.trans(Cmp, Nat.cmp(Nat.sub(xp, xn), 0n), Nat.cmp(1n+Nat.sub(xp, 1n+xn), 0n), GT{},
          Equal.cong(Nat, Cmp, t => Nat.cmp(t, 0n), Nat.sub(xp, xn), 1n+Nat.sub(xp, 1n+xn),
            N.sub_pos(xp, xn, Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e))),
          {==}))
    case LT{}:
      I.Int.canon.neg(Nat.sub(xn, xp),
        Equal.trans(Cmp, Nat.cmp(0n, Nat.sub(xn, xp)), Nat.cmp(0n, 1n+Nat.sub(xn, 1n+xp)), LT{},
          Equal.cong(Nat, Cmp, t => Nat.cmp(0n, t), Nat.sub(xn, xp), 1n+Nat.sub(xn, 1n+xp),
            N.sub_pos(xn, xp, N.cmp_gt_of_lt(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e)))),
          {==}))

# Int.canon.scale.go: case on the comparison. The positive branch is the whole
# content -- scaling commutes with canon's own case split -- and the work per
# branch is bookkeeping:
#
#   1. Int.mul(x, Int{1+kp, 0}) reduces to Int{add(xp*(1+kp), xn*0),
#      add(xp*0, xn*(1+kp))}: the zeros are stuck (Nat.mul of two variables
#      does not reduce), so mul_zero and add_zero turn the state's two slots
#      into xp*(1+kp) and xn*(1+kp). Each of those rewrites fires in two
#      places at once (the cmp's argument and canon.go's own argument), which
#      is what the repeated `_` in the motives is for.
#   2. cmp_mul_right collapses cmp(xp*(1+kp), xn*(1+kp)) to cmp(xp, xn), and
#      the branch's own evidence e collapses that to the constructor just
#      matched -- so canon.go reduces to its branch value.
#   3. The right-hand side Int.mul(canon.go(c, ..), Int{1+kp, 0}) reduces to
#      the same branch value scaled, and mul_sub_right is what says the scaled
#      difference is the difference of the scaled slots (the Nats' own
#      right-scaled mul_sub; the left-scaled mul_sub is stated the other way
#      round, which is why the Nat inventory carries both).
#
# e is a + binder in the law because the GT and LT branches read it twice: once
# to collapse the comparison and once as mul_sub_right's hypothesis. An
# equation is Data, so a + equation binder costs nothing -- and unlike a +field
# of a Sigma it is not a dependent type, so the copy is unremarkable.
def I.Int.canon.scale.go(c, xp, xn, kp, e):
  match c:
    case EQ{}:
      %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int.canon.go(Nat.cmp(Nat.add(Nat.mul(xp, 1n+kp), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n+kp))), Nat.add(Nat.mul(xp, 1n+kp), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n+kp))) == I.Int.mul(I.Int.canon.go(EQ{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int.canon.go(Nat.cmp(Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.add(_, Nat.mul(xn, 1n+kp))), Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.add(_, Nat.mul(xn, 1n+kp))) == I.Int.mul(I.Int.canon.go(EQ{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.mul(xp, 1n+kp), N.add_zero(Nat.mul(xp, 1n+kp))) : {I.Int.canon.go(Nat.cmp(_, Nat.mul(xn, 1n+kp)), _, Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(EQ{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)), Nat.cmp(xp, xn), N.cmp_mul_right(xp, xn, kp)) : {I.Int.canon.go(_, Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(EQ{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %e : {I.Int.canon.go(_, Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(EQ{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      {==}
    case GT{}:
      %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int.canon.go(Nat.cmp(Nat.add(Nat.mul(xp, 1n+kp), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n+kp))), Nat.add(Nat.mul(xp, 1n+kp), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n+kp))) == I.Int.mul(I.Int.canon.go(GT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int.canon.go(Nat.cmp(Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.add(_, Nat.mul(xn, 1n+kp))), Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.add(_, Nat.mul(xn, 1n+kp))) == I.Int.mul(I.Int.canon.go(GT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.mul(xp, 1n+kp), N.add_zero(Nat.mul(xp, 1n+kp))) : {I.Int.canon.go(Nat.cmp(_, Nat.mul(xn, 1n+kp)), _, Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(GT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)), Nat.cmp(xp, xn), N.cmp_mul_right(xp, xn, kp)) : {I.Int.canon.go(_, Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(GT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %e : {I.Int.canon.go(_, Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(GT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.mul(Nat.sub(xp, xn), 0n), 0n, N.mul_zero(Nat.sub(xp, xn))) : {I.Int{Nat.sub(Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)), 0n} == I.Int{Nat.add(Nat.mul(Nat.sub(xp, xn), 1n+kp), Nat.mul(0n, 0n)), Nat.add(_, Nat.mul(0n, 1n+kp))} : I.Int}
      %Equal.sym(Nat, Nat.add(Nat.mul(Nat.sub(xp, xn), 1n+kp), 0n), Nat.mul(Nat.sub(xp, xn), 1n+kp), N.add_zero(Nat.mul(Nat.sub(xp, xn), 1n+kp))) : {I.Int{Nat.sub(Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)), 0n} == I.Int{_, Nat.add(0n, Nat.mul(0n, 1n+kp))} : I.Int}
      %N.mul_sub_right(xp, xn, 1n+kp, Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e)) : {I.Int{_, 0n} == I.Int{Nat.mul(Nat.sub(xp, xn), 1n+kp), 0n} : I.Int}
      {==}
    case LT{}:
      %Equal.sym(Nat, Nat.mul(xn, 0n), 0n, N.mul_zero(xn)) : {I.Int.canon.go(Nat.cmp(Nat.add(Nat.mul(xp, 1n+kp), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n+kp))), Nat.add(Nat.mul(xp, 1n+kp), _), Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n+kp))) == I.Int.mul(I.Int.canon.go(LT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.mul(xp, 0n), 0n, N.mul_zero(xp)) : {I.Int.canon.go(Nat.cmp(Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.add(_, Nat.mul(xn, 1n+kp))), Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.add(_, Nat.mul(xn, 1n+kp))) == I.Int.mul(I.Int.canon.go(LT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.add(Nat.mul(xp, 1n+kp), 0n), Nat.mul(xp, 1n+kp), N.add_zero(Nat.mul(xp, 1n+kp))) : {I.Int.canon.go(Nat.cmp(_, Nat.mul(xn, 1n+kp)), _, Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(LT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)), Nat.cmp(xp, xn), N.cmp_mul_right(xp, xn, kp)) : {I.Int.canon.go(_, Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(LT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %e : {I.Int.canon.go(_, Nat.mul(xp, 1n+kp), Nat.mul(xn, 1n+kp)) == I.Int.mul(I.Int.canon.go(LT{}, xp, xn), I.Int{1n+kp, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.mul(Nat.sub(xn, xp), 0n), 0n, N.mul_zero(Nat.sub(xn, xp))) : {I.Int{0n, Nat.sub(Nat.mul(xn, 1n+kp), Nat.mul(xp, 1n+kp))} == I.Int{Nat.add(Nat.mul(0n, 1n+kp), _), Nat.add(Nat.mul(0n, 0n), Nat.mul(Nat.sub(xn, xp), 1n+kp))} : I.Int}
      %N.mul_sub_right(xn, xp, 1n+kp, N.cmp_gt_of_lt(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e))) : {I.Int{0n, _} == I.Int{0n, Nat.mul(Nat.sub(xn, xp), 1n+kp)} : I.Int}
      {==}

# Int.canon.scale: destructure x and hand the comparison in. The call's
# conclusion is the goal up to conversion: Int.canon(Int{xp, xn}) reduces to
# canon.go(Nat.cmp(xp, xn), xp, xn), which is exactly what scale.go states.
def I.Int.canon.scale(x, kp):
  match x:
    case I.Int{+xp, +xn}:
      I.Int.canon.scale.go(Nat.cmp(xp, xn), xp, xn, kp, {==})

# Int.canon.eqv
# =============
#
# Int.proj.pos / Int.proj.neg: the two coordinates of an Int as functions. They
# exist for the J motive in Int.eq.pos / Int.eq.neg below (and for nothing
# else), so they live here with the other proof-only machinery. The fields are
# read with + patterns: both projections are called on the same Int.
def Int.proj.pos(x: I.Int) -> Nat:
  I.Int{+p, +n} = x
  p

def Int.proj.neg(x: I.Int) -> Nat:
  I.Int{+p, +n} = x
  n

# NatIsZero: Unit on 0n, Empty on a successor. The discrimination a
# "a successor is not zero" proof needs.
def NatIsZero(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

# Nat.succ_ne_zero: 0 = 1 + a is impossible. Stated over 0 on the left because
# that is the orientation the callers build (a truncated difference proved equal
# to 0, then sub_pos turned round).
def Nat.succ_ne_zero(a: Nat, e: {0n == 1n+a : Nat}) -> Empty:
  %e : NatIsZero(_)
  Unit{}

def I.Int.eq.pos(a, b, c, d, e):
  %e : {Int.proj.pos(I.Int{a, b}) == Int.proj.pos(_) : Nat}
  {==}

def I.Int.eq.neg(a, b, c, d, e):
  %e : {Int.proj.neg(I.Int{a, b}) == Int.proj.neg(_) : Nat}
  {==}

# Int.canon.eqv.fwd: case on the two comparisons and grind. The `_` in each
# motive marks the subterm the evidence's right side sits at, so a step that
# rewrites a difference inside a sum spells the sum around the hole; a motive
# that does not mention the subterm at all would rewrite nothing.
# Int.scale.pair: the right side unfolds to Int{add(p*q, 0), add(p*0, 0)}; the
# two zero products come off (mul_zero for the stuck one, computation for
# mul(0,q)) and add(0,0) is 0 by computation.
def I.Int.scale.pair(p, q):
  %Equal.sym(Nat, Nat.add(Nat.mul(p, q), 0n), Nat.mul(p, q), N.add_zero(Nat.mul(p, q))) : {I.Int{Nat.mul(p, q), 0n} == I.Int{_, Nat.add(Nat.mul(p, 0n), 0n)} : I.Int}
  %Equal.sym(Nat, Nat.mul(p, 0n), 0n, N.mul_zero(p)) : {I.Int{Nat.mul(p, q), 0n} == I.Int{Nat.mul(p, q), Nat.add(_, 0n)} : I.Int}
  {==}

# Int.scale.cancel: both sides of the hypothesis go to the coordinate pair
# Int.mul_scale names (one sym rewrite each), the two coordinates are read off
# with Int.eq.pos / Int.eq.neg, Nat.mul_right_cancel turns each into the
# unscaled coordinate equation, and the goal is those two equations carried
# back through the Int constructor with one cong each.
def I.Int.scale.cancel(u, v, kp, e):
  match u:
    case I.Int{up, un}:
      match v:
        case I.Int{vp, vn}:
          +ce = Equal.trans(I.Int,
            I.Int{Nat.mul(up, 1n+kp), Nat.mul(un, 1n+kp)},
            I.Int.mul(I.Int{up, un}, I.Int{1n+kp, 0n}),
            I.Int{Nat.mul(vp, 1n+kp), Nat.mul(vn, 1n+kp)},
            Equal.sym(I.Int, I.Int.mul(I.Int{up, un}, I.Int{1n+kp, 0n}),
              I.Int{Nat.mul(up, 1n+kp), Nat.mul(un, 1n+kp)},
              I.Int.mul_scale(up, un, 1n+kp)),
            Equal.trans(I.Int,
              I.Int.mul(I.Int{up, un}, I.Int{1n+kp, 0n}),
              I.Int.mul(I.Int{vp, vn}, I.Int{1n+kp, 0n}),
              I.Int{Nat.mul(vp, 1n+kp), Nat.mul(vn, 1n+kp)},
              e,
              I.Int.mul_scale(vp, vn, 1n+kp)))
          +eup = I.Int.eq.pos(Nat.mul(up, 1n+kp), Nat.mul(un, 1n+kp),
            Nat.mul(vp, 1n+kp), Nat.mul(vn, 1n+kp), ce)
          +eun = I.Int.eq.neg(Nat.mul(up, 1n+kp), Nat.mul(un, 1n+kp),
            Nat.mul(vp, 1n+kp), Nat.mul(vn, 1n+kp), ce)
          Equal.trans(I.Int,
            I.Int{up, un},
            I.Int{vp, un},
            I.Int{vp, vn},
            Equal.cong(Nat, I.Int, w => I.Int{w, un}, up, vp,
              N.mul_right_cancel(up, vp, kp, eup)),
            Equal.cong(Nat, I.Int, w => I.Int{vp, w}, un, vn,
              N.mul_right_cancel(un, vn, kp, eun)))

def I.Int.canon.eqv.fwd(c1, xp, xn, c2, yp, yn, e1, e2, e):
  match c1:
    case GT{}:
      match c2:
        case GT{}:
          %N.cmp_gt_sub_add(xp, xn, Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e1)) : {Nat.add(_, yn) == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.sub(xp, xn), Nat.sub(yp, yn), I.Int.eq.pos(Nat.sub(xp, xn), 0n, Nat.sub(yp, yn), 0n, e)) : {Nat.add(Nat.add(_, xn), yn) == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(Nat.sub(yp, yn), xn), yn), Nat.add(Nat.sub(yp, yn), Nat.add(xn, yn)), N.add_assoc(Nat.sub(yp, yn), xn, yn)) : {_ == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(xn, yn), Nat.add(yn, xn), N.add_comm(xn, yn)) : {Nat.add(Nat.sub(yp, yn), _) == Nat.add(yp, xn) : Nat}
          %N.add_assoc(Nat.sub(yp, yn), yn, xn) : {_ == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.sub(yp, yn), yn), yp, N.cmp_gt_sub_add(yp, yn, Equal.sym(Cmp, GT{}, Nat.cmp(yp, yn), e2))) : {Nat.add(_, xn) == Nat.add(yp, xn) : Nat}
          {==}
        case EQ{}:
          Empty.absurd({Nat.add(xp, yn) == Nat.add(yp, xn) : Nat},
            Nat.succ_ne_zero(Nat.sub(xp, 1n+xn),
              Equal.trans(Nat, 0n, Nat.sub(xp, xn), 1n+Nat.sub(xp, 1n+xn),
                Equal.sym(Nat, Nat.sub(xp, xn), 0n, I.Int.eq.pos(Nat.sub(xp, xn), 0n, 0n, 0n, e)),
                N.sub_pos(xp, xn, Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e1)))))
        case LT{}:
          Empty.absurd({Nat.add(xp, yn) == Nat.add(yp, xn) : Nat},
            Nat.succ_ne_zero(Nat.sub(xp, 1n+xn),
              Equal.trans(Nat, 0n, Nat.sub(xp, xn), 1n+Nat.sub(xp, 1n+xn),
                Equal.sym(Nat, Nat.sub(xp, xn), 0n, I.Int.eq.pos(Nat.sub(xp, xn), 0n, 0n, Nat.sub(yn, yp), e)),
                N.sub_pos(xp, xn, Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e1)))))
    case EQ{}:
      match c2:
        case GT{}:
          Empty.absurd({Nat.add(xp, yn) == Nat.add(yp, xn) : Nat},
            Nat.succ_ne_zero(Nat.sub(yp, 1n+yn),
              Equal.trans(Nat, 0n, Nat.sub(yp, yn), 1n+Nat.sub(yp, 1n+yn),
                I.Int.eq.pos(0n, 0n, Nat.sub(yp, yn), 0n, e),
                N.sub_pos(yp, yn, Equal.sym(Cmp, GT{}, Nat.cmp(yp, yn), e2)))))
        case EQ{}:
          %Equal.sym(Nat, xp, xn, N.cmp_eq(xp, xn, Equal.sym(Cmp, EQ{}, Nat.cmp(xp, xn), e1))) : {Nat.add(_, yn) == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(xn, yn), Nat.add(yn, xn), N.add_comm(xn, yn)) : {_ == Nat.add(yp, xn) : Nat}
          %N.cmp_eq(yp, yn, Equal.sym(Cmp, EQ{}, Nat.cmp(yp, yn), e2)) : {Nat.add(_, xn) == Nat.add(yp, xn) : Nat}
          {==}
        case LT{}:
          Empty.absurd({Nat.add(xp, yn) == Nat.add(yp, xn) : Nat},
            Nat.succ_ne_zero(Nat.sub(yn, 1n+yp),
              Equal.trans(Nat, 0n, Nat.sub(yn, yp), 1n+Nat.sub(yn, 1n+yp),
                I.Int.eq.neg(0n, 0n, 0n, Nat.sub(yn, yp), e),
                N.sub_pos(yn, yp, N.cmp_gt_of_lt(yp, yn, Equal.sym(Cmp, LT{}, Nat.cmp(yp, yn), e2))))))
    case LT{}:
      match c2:
        case GT{}:
          Empty.absurd({Nat.add(xp, yn) == Nat.add(yp, xn) : Nat},
            Nat.succ_ne_zero(Nat.sub(xn, 1n+xp),
              Equal.trans(Nat, 0n, Nat.sub(xn, xp), 1n+Nat.sub(xn, 1n+xp),
                Equal.sym(Nat, Nat.sub(xn, xp), 0n, I.Int.eq.neg(0n, Nat.sub(xn, xp), Nat.sub(yp, yn), 0n, e)),
                N.sub_pos(xn, xp, N.cmp_gt_of_lt(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e1))))))
        case EQ{}:
          Empty.absurd({Nat.add(xp, yn) == Nat.add(yp, xn) : Nat},
            Nat.succ_ne_zero(Nat.sub(xn, 1n+xp),
              Equal.trans(Nat, 0n, Nat.sub(xn, xp), 1n+Nat.sub(xn, 1n+xp),
                Equal.sym(Nat, Nat.sub(xn, xp), 0n, I.Int.eq.neg(0n, Nat.sub(xn, xp), 0n, 0n, e)),
                N.sub_pos(xn, xp, N.cmp_gt_of_lt(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e1))))))
        case LT{}:
          %N.cmp_lt_sub_add(yp, yn, Equal.sym(Cmp, LT{}, Nat.cmp(yp, yn), e2)) : {Nat.add(xp, _) == Nat.add(yp, xn) : Nat}
          %I.Int.eq.neg(0n, Nat.sub(xn, xp), 0n, Nat.sub(yn, yp), e) : {Nat.add(xp, Nat.add(_, yp)) == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(xp, Nat.add(Nat.sub(xn, xp), yp)), Nat.add(Nat.add(xp, Nat.sub(xn, xp)), yp), N.add_assoc_rev(xp, Nat.sub(xn, xp), yp)) : {_ == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(xp, Nat.sub(xn, xp)), Nat.add(Nat.sub(xn, xp), xp), N.add_comm(xp, Nat.sub(xn, xp))) : {Nat.add(_, yp) == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.sub(xn, xp), xp), xn, N.cmp_lt_sub_add(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e1))) : {Nat.add(_, yp) == Nat.add(yp, xn) : Nat}
          %Equal.sym(Nat, Nat.add(xn, yp), Nat.add(yp, xn), N.add_comm(xn, yp)) : {_ == Nat.add(yp, xn) : Nat}
          {==}

# Int.canon.eqv.bwd: the reverse of the quotient lemma. The branch structure is
# the case split on the two comparisons, and each branch is one law from
# nat.bend (cross_gt_gt / cross_cmp) plus a congruence -- the arithmetic all
# happened there, so nothing below is longer than a call.
#
# The goal in a branch has canon.go applied to a *constructor* comparison, so
# it reduces to the branch's Int: what the cong's endpoints spell is that
# reduced Int, and the Int equation the goal wants is exactly
# {Int{A, 0n} == Int{B, 0n}} (GT), {Int{0n, A} == Int{0n, B}} (LT) or
# {Int{0n, 0n} == Int{0n, 0n}} (EQ).
def I.Int.canon.eqv.bwd(c1, xp, xn, c2, yp, yn, e1, e2, e):
  match c1:
    case GT{}:
      match c2:
        case GT{}:
          Equal.cong(Nat, I.Int, u => I.Int{u, 0n},
            Nat.sub(xp, xn), Nat.sub(yp, yn),
            N.cross_gt_gt(xp, xn, yp, yn,
              Equal.sym(Cmp, GT{}, Nat.cmp(xp, xn), e1),
              Equal.sym(Cmp, GT{}, Nat.cmp(yp, yn), e2), e))
        case EQ{}:
          Empty.absurd({I.Int{Nat.sub(xp, xn), 0n} == I.Int{0n, 0n} : I.Int},
            N.gt_ne_eq(N.cross_cmp(GT{}, xp, xn, EQ{}, yp, yn, e1, e2, e)))
        case LT{}:
          Empty.absurd({I.Int{Nat.sub(xp, xn), 0n} == I.Int{0n, Nat.sub(yn, yp)} : I.Int},
            N.gt_ne_lt(N.cross_cmp(GT{}, xp, xn, LT{}, yp, yn, e1, e2, e)))
    case EQ{}:
      match c2:
        case GT{}:
          Empty.absurd({I.Int{0n, 0n} == I.Int{Nat.sub(yp, yn), 0n} : I.Int},
            N.eq_ne_gt(N.cross_cmp(EQ{}, xp, xn, GT{}, yp, yn, e1, e2, e)))
        case EQ{}:
          {==}
        case LT{}:
          Empty.absurd({I.Int{0n, 0n} == I.Int{0n, Nat.sub(yn, yp)} : I.Int},
            N.eq_ne_lt(N.cross_cmp(EQ{}, xp, xn, LT{}, yp, yn, e1, e2, e)))
    case LT{}:
      match c2:
        case GT{}:
          Empty.absurd({I.Int{0n, Nat.sub(xn, xp)} == I.Int{Nat.sub(yp, yn), 0n} : I.Int},
            N.lt_ne_gt(N.cross_cmp(LT{}, xp, xn, GT{}, yp, yn, e1, e2, e)))
        case EQ{}:
          Empty.absurd({I.Int{0n, Nat.sub(xn, xp)} == I.Int{0n, 0n} : I.Int},
            N.lt_ne_eq(N.cross_cmp(LT{}, xp, xn, EQ{}, yp, yn, e1, e2, e)))
        case LT{}:
          Equal.cong(Nat, I.Int, u => I.Int{0n, u},
            Nat.sub(xn, xp), Nat.sub(yn, yp),
            N.cross_gt_gt(xn, xp, yn, yp,
              N.cmp_gt_of_lt(xp, xn, Equal.sym(Cmp, LT{}, Nat.cmp(xp, xn), e1)),
              N.cmp_gt_of_lt(yp, yn, Equal.sym(Cmp, LT{}, Nat.cmp(yp, yn), e2)),
              Equal.trans(Nat, Nat.add(xn, yp), Nat.add(yp, xn), Nat.add(yn, xp),
                N.add_comm(xn, yp),
                Equal.trans(Nat, Nat.add(yp, xn), Nat.add(xp, yn), Nat.add(yn, xp),
                  Equal.sym(Nat, Nat.add(xp, yn), Nat.add(yp, xn), e),
                  N.add_comm(xp, yn)))))


# Int.scale_cross: one % step per rewrite, left to right, because the goal *is*
# the chain the two sides are rewritten onto each other along.
#
#   - 1-7 pull the yd out of the goal's left numerator and next to the factors
#     e1 knows about: the scale xd*b splits, the yd is swapped left past b and
#     xd, and the result is regrouped as (A*(xd*yd))*(zn*b);
#   - 8-9 are e1 and the regrouping that presents it as A*(xd*yd) == R1*a;
#   - 10 is s1, landing the left side on xn*yn*a*zn*b;
#   - 11-17 permute that onto the middle term e2 can consume, ((yn*zn)*b)*(xn*a);
#   - 18-19 are s2 and e2 the other way round;
#   - 20-30 take (B*(yd*zd))*(xn*a) apart into the goal's right side: split
#     yd*zd, recombine a*zd, and permute the factors into place.
#
# The rewrite orientation of each step is the `%` rule read literally: the
# evidence is {new == old}, so a step that left-nests (a*(b*c) -> (a*b)*c) uses
# mul_assoc as it stands and a step that right-nests uses it through Equal.sym;
# the swaps are the same story with mul_swap and mul_comm.
def I.Int.scale_cross(A, R1, B, R2, xn, yn, zn, a, b, xd, zd, dyp, e1, e2, s1, s2):
  +Yd = I.Int.unit(1n+dyp)
  +Xd = I.Int.unit(xd)
  +Zd = I.Int.unit(zd)
  +As = I.Int.unit(a)
  +Bs = I.Int.unit(b)
  +D1 = I.Int.unit(Nat.mul(xd, 1n+dyp))
  +D2 = I.Int.unit(Nat.mul(1n+dyp, zd))
  +Sa = I.Int.unit(Nat.mul(xd, b))
  +Sb = I.Int.unit(Nat.mul(a, zd))
  +XA = I.Int.mul(xn, As)
  +ZB = I.Int.mul(zn, Bs)
  +Y  = I.Int.mul(I.Int.mul(xn, B), Sb)
  %Equal.sym(I.Int, Sa, I.Int.mul(Xd, Bs), I.Int.scale.pair(xd, b)) : {I.Int.mul(I.Int.mul(I.Int.mul(A, zn), _), Yd) == I.Int.mul(Y, Yd) : I.Int}
  %I.Int.mul_assoc(I.Int.mul(A, zn), Xd, Bs) : {I.Int.mul(_, Yd) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(A, zn), Xd), Bs), Yd), I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(A, zn), Xd), Yd), Bs), I.Int.mul_swap(I.Int.mul(I.Int.mul(A, zn), Xd), Bs, Yd)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(A, zn), Xd), I.Int.mul(I.Int.mul(A, Xd), zn), I.Int.mul_swap(A, zn, Xd)) : {I.Int.mul(I.Int.mul(_, Yd), Bs) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(A, Xd), zn), Yd), I.Int.mul(I.Int.mul(I.Int.mul(A, Xd), Yd), zn), I.Int.mul_swap(I.Int.mul(A, Xd), zn, Yd)) : {I.Int.mul(_, Bs) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(A, Xd), Yd), zn), Bs), I.Int.mul(I.Int.mul(I.Int.mul(A, Xd), Yd), ZB), I.Int.mul_assoc(I.Int.mul(I.Int.mul(A, Xd), Yd), zn, Bs)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(A, Xd), Yd), I.Int.mul(A, I.Int.mul(Xd, Yd)), I.Int.mul_assoc(A, Xd, Yd)) : {I.Int.mul(_, ZB) == I.Int.mul(Y, Yd) : I.Int}
  %I.Int.scale.pair(xd, 1n+dyp) : {I.Int.mul(I.Int.mul(A, _), ZB) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(A, D1), I.Int.mul(R1, As), e1) : {I.Int.mul(_, ZB) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, R1, I.Int.mul(xn, yn), s1) : {I.Int.mul(I.Int.mul(_, As), ZB) == I.Int.mul(Y, Yd) : I.Int}
  %I.Int.mul_assoc(I.Int.mul(I.Int.mul(xn, yn), As), zn, Bs) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(xn, yn), I.Int.mul(yn, xn), I.Int.mul_comm(xn, yn)) : {I.Int.mul(I.Int.mul(I.Int.mul(_, As), zn), Bs) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(yn, xn), As), zn), I.Int.mul(I.Int.mul(I.Int.mul(yn, xn), zn), As), I.Int.mul_swap(I.Int.mul(yn, xn), As, zn)) : {I.Int.mul(_, Bs) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(yn, xn), zn), I.Int.mul(I.Int.mul(yn, zn), xn), I.Int.mul_swap(yn, xn, zn)) : {I.Int.mul(I.Int.mul(_, As), Bs) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(yn, zn), xn), As), Bs), I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(yn, zn), xn), Bs), As), I.Int.mul_swap(I.Int.mul(I.Int.mul(yn, zn), xn), As, Bs)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(yn, zn), xn), Bs), I.Int.mul(I.Int.mul(I.Int.mul(yn, zn), Bs), xn), I.Int.mul_swap(I.Int.mul(yn, zn), xn, Bs)) : {I.Int.mul(_, As) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(yn, zn), Bs), xn), As), I.Int.mul(I.Int.mul(I.Int.mul(yn, zn), Bs), XA), I.Int.mul_assoc(I.Int.mul(I.Int.mul(yn, zn), Bs), xn, As)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(yn, zn), Bs), I.Int.mul(R2, Bs),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(w, Bs), I.Int.mul(yn, zn), R2, Equal.sym(I.Int, R2, I.Int.mul(yn, zn), s2))) : {I.Int.mul(_, XA) == I.Int.mul(Y, Yd) : I.Int}
  %e2 : {I.Int.mul(_, XA) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, D2, I.Int.mul(Yd, Zd), I.Int.scale.pair(1n+dyp, zd)) : {I.Int.mul(I.Int.mul(B, _), XA) == I.Int.mul(Y, Yd) : I.Int}
  %I.Int.mul_assoc(B, Yd, Zd) : {I.Int.mul(_, XA) == I.Int.mul(Y, Yd) : I.Int}
  %I.Int.mul_assoc(I.Int.mul(I.Int.mul(B, Yd), Zd), xn, As) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), Zd), xn), As), I.Int.mul(I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), Zd), As), xn), I.Int.mul_swap(I.Int.mul(I.Int.mul(B, Yd), Zd), xn, As)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), Zd), As), I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), As), Zd), I.Int.mul_swap(I.Int.mul(B, Yd), Zd, As)) : {I.Int.mul(_, xn) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), As), Zd), I.Int.mul(I.Int.mul(B, Yd), I.Int.mul(As, Zd)), I.Int.mul_assoc(I.Int.mul(B, Yd), As, Zd)) : {I.Int.mul(_, xn) == I.Int.mul(Y, Yd) : I.Int}
  %I.Int.scale.pair(a, zd) : {I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), _), xn) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), Sb), xn), I.Int.mul(I.Int.mul(I.Int.mul(B, Yd), xn), Sb), I.Int.mul_swap(I.Int.mul(B, Yd), Sb, xn)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(B, Yd), xn), I.Int.mul(I.Int.mul(B, xn), Yd), I.Int.mul_swap(B, Yd, xn)) : {I.Int.mul(_, Sb) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(B, xn), I.Int.mul(xn, B), I.Int.mul_comm(B, xn)) : {I.Int.mul(I.Int.mul(_, Yd), Sb) == I.Int.mul(Y, Yd) : I.Int}
  %Equal.sym(I.Int, I.Int.mul(I.Int.mul(I.Int.mul(xn, B), Yd), Sb), I.Int.mul(I.Int.mul(I.Int.mul(xn, B), Sb), Yd), I.Int.mul_swap(I.Int.mul(xn, B), Yd, Sb)) : {_ == I.Int.mul(Y, Yd) : I.Int}
  {==}
