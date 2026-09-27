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
    case T.Bad{}:
      {==}
    case T.Fuel{}:
      {==}

def T.Tower.depth.lift(t, d):
  {==}

def T.Tower.lift.zero(t, d):
  {==}

# Step 2: the level operations at spelled forms. Every one of these is its
# definition's own unfolding, so each fill is the same triviality -- what they buy
# is that later laws and callers can rewrite with them rather than re-deriving the
# shape, and that the shapes themselves are pinned down by a checked statement.

def T.Tower.add.base(d, a, b):
  {==}

def T.Tower.add.ext(d, rx, ix, dx, ry, iy, dy):
  {==}

def T.Tower.neg.ext(rx, ix, dx):
  {==}

def T.Tower.mul.base(g, d, a, b):
  {==}

# the sqrt(d) * sqrt(d) = d reduction, at a successor fuel
def T.Tower.mul.ext(g, d, rx, ix, dx, ry, iy, dy):
  {==}

def T.Tower.one.base(v):
  {==}

def T.Tower.one.ext(re, im, d):
  {==}
