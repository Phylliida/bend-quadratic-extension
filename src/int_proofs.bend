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
