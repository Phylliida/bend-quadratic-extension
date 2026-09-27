import Base
import ./tower.bend as T
# succ_inj (successor cancellation) and succ_add_ne (k = (1+b)+k is impossible)
# are the two nat facts the safety proofs run on
import ./nat.bend as N
import ./nat_proofs.bend as NN
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

def T.Tower.add.base(a, b, d):
  {==}

def T.Tower.add.ext(rx, ix, dx, ry, iy, dy, d):
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


# Safety: add preserves the level, and a clean call is a clean result
# ==================================================================
#
# Both fills are the same eight-arm induction. The four shape arms are the real
# work: Base/Base is definitional, and Ext/Ext recurses with the level relation
# for the re coordinates recovered from the outer hypothesis by successor
# cancellation, and the one for the im coordinates assembled from the evidence's
# own hri fields. The two mixed-shape arms are absurdity -- the equal-depth
# hypothesis contradicts the shapes -- and the four marker arms hand the marker's
# own evidence to Empty.absurd. Those four name their goal type instead of
# computing it, because add(d, Bad{}, y) does not reduce when y is still a
# variable.

# clean evidence transports across rad
# ===================================
#
# The radicand of a level is a part of the operand -- the third field of an Ext,
# the operand itself at a Base -- so the operand's evidence already contains the
# radicand's. This is why the safety fills need no extra hypothesis for the
# sub-level radicand the recursion now passes: they derive its evidence from the
# operand's own. Same shape as Tower.wf.zero: evidence, not equations, transport.

def TowerCleanRad(t: T.Tower, h: T.Tower.clean(t)) -> T.Tower.clean(T.Tower.rad(t)):
  match t:
    case T.Base{v}:
      h
    case T.Ext{re, im, d}:
      T.CleanExt{+cr, +ci, +cd, +hri} = h
      cd
    case T.Bad{}:
      h
    case T.Fuel{}:
      h

def T.Tower.add.depth(x, y, d, hx, hy, hd, h):
  match x y:
    case T.Base{a} T.Base{b}:
      {==}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      T.CleanExt{+hxr, +hxi, +hxd, +hxri} = hx
      T.CleanExt{+hyr, +hyi, +hyd, +hyri} = hy
      Equal.cong(Nat, Nat, u => Nat.add(1n, u),
        T.Tower.depth(T.Tower.add(rx, ry, T.Tower.rad(rx))), T.Tower.depth(rx),
        T.Tower.add.depth(rx, ry, T.Tower.rad(rx), hxr, hyr, TowerCleanRad(rx, hxr),
          N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)))
    case T.Base{a} T.Ext{ry, iy, dy}:
      {==}
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd({0n == Nat.add(1n, T.Tower.depth(rx)) : Nat},
        N.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
    case T.Bad{} _:
      Empty.absurd({T.Tower.depth(T.Tower.add(T.Bad{}, y, d)) == 0n : Nat}, hx)
    case T.Fuel{} _:
      Empty.absurd({T.Tower.depth(T.Tower.add(T.Fuel{}, y, d)) == 0n : Nat}, hx)
    case _ T.Bad{}:
      Empty.absurd({T.Tower.depth(T.Tower.add(x, T.Bad{}, d)) == T.Tower.depth(x) : Nat}, hy)
    case _ T.Fuel{}:
      Empty.absurd({T.Tower.depth(T.Tower.add(x, T.Fuel{}, d)) == T.Tower.depth(x) : Nat}, hy)

def T.Tower.add.clean(x, y, d, hx, hy, hd, h):
  match x y:
    case T.Base{a} T.Base{b}:
      T.CleanOk{}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      T.CleanExt{+hxr, +hxi, +hxd, +hxri} = hx
      T.CleanExt{+hyr, +hyi, +hyd, +hyri} = hy
      +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)
      +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
              Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
              Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                er, hyri))
      +cr = T.Tower.add.clean(rx, ry, T.Tower.rad(rx), hxr, hyr, TowerCleanRad(rx, hxr), er)
      +ci = T.Tower.add.clean(ix, iy, T.Tower.rad(rx), hxi, hyi, TowerCleanRad(rx, hxr), ei)
      +dr = T.Tower.add.depth(rx, ry, T.Tower.rad(rx), hxr, hyr, TowerCleanRad(rx, hxr), er)
      +di = T.Tower.add.depth(ix, iy, T.Tower.rad(rx), hxi, hyi, TowerCleanRad(rx, hxr), ei)
      T.CleanExt{cr, ci, hd,
        Equal.trans(Nat,
          T.Tower.depth(T.Tower.add(rx, ry, T.Tower.rad(rx))), T.Tower.depth(ix),
          T.Tower.depth(T.Tower.add(ix, iy, T.Tower.rad(rx))),
          Equal.trans(Nat, T.Tower.depth(T.Tower.add(rx, ry, T.Tower.rad(rx))),
            T.Tower.depth(rx), T.Tower.depth(ix), dr, hxri),
          Equal.sym(Nat, T.Tower.depth(T.Tower.add(ix, iy, T.Tower.rad(rx))), T.Tower.depth(ix), di))}
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd(Empty,
        N.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          0n, Nat.add(1n, T.Tower.depth(ry)), h)))
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd(Empty,
        N.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
    case T.Bad{} _:
      Empty.absurd(T.Tower.clean(T.Tower.add(T.Bad{}, y, d)), hx)
    case T.Fuel{} _:
      Empty.absurd(T.Tower.clean(T.Tower.add(T.Fuel{}, y, d)), hx)
    case _ T.Bad{}:
      Empty.absurd(T.Tower.clean(T.Tower.add(x, T.Bad{}, d)), hy)
    case _ T.Fuel{}:
      Empty.absurd(T.Tower.clean(T.Tower.add(x, T.Fuel{}, d)), hy)

def T.Tower.mul.fuel.base(g, d, a, b):
  T.CleanOk{}

def T.Tower.mul.fuel.zero(d, x, y):
  {==}
