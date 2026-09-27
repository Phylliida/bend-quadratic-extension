import Base
import ./tower.bend as T
# not named in this file, but it is what fills rat.bend's laws, so the tower
# proofs file reports a complete closure rather than 229 outstanding ones
import ./rat_proofs.bend as RP

# Tower proofs
# ============
#
# Fills every law of tower.bend. depth.zero is a structural induction: the match
# refines the law at the branch, and the Ext branch calls the fill itself on the
# tail. The rest are definitional -- each side reduces to the same term -- which
# is what makes them worth having as statements: lift.zero is the level operation
# zero surviving the embedding, the property every later law leans on.

def T.Tower.zero.base(v):
  {==}

def T.Tower.depth.zero(t):
  match t:
    case T.Base{v}:
      {==}
    case T.Ext{re, im, d}:
      %Equal.sym(Nat, T.Tower.depth(T.Tower.zero(re)), T.Tower.depth(re),
          T.Tower.depth.zero(re))
        : {Nat.add(1n, _) == Nat.add(1n, T.Tower.depth(re)) : Nat}
      {==}

def T.Tower.depth.lift(t, d):
  {==}

def T.Tower.lift.zero(t, d):
  {==}
