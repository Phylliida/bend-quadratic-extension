import Base
import ./tower.bend as T
import ./tower_helpers.bend as TH
# succ_inj (successor cancellation) and succ_add_ne (k = (1+b)+k is impossible)
# are the two nat facts the safety proofs run on
import ./nat.bend as N
import ./nat_helpers.bend as NH
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

def T.Tower.add.base(a, b):
  {==}

def T.Tower.add.ext(rx, ix, dx, ry, iy, dy):
  {==}

def T.Tower.neg.ext(rx, ix, dx):
  {==}

def T.Tower.mul.base(g, a, b):
  {==}

# the sqrt(d) * sqrt(d) = d reduction, at a successor fuel
def T.Tower.mul.ext(g, rx, ix, dx, ry, iy, dy):
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

def T.Tower.add.depth(x, y, h):
  match x y:
    case T.Base{a} T.Base{b}:
      {==}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      Equal.cong(Nat, Nat, u => Nat.add(1n, u),
        T.Tower.depth(T.Tower.add(rx, ry)), T.Tower.depth(rx),
        T.Tower.add.depth(rx, ry,
          N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)))
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd({0n == Nat.add(1n, T.Tower.depth(rx)) : Nat},
        NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd({0n == Nat.add(1n, T.Tower.depth(rx)) : Nat},
        NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd({0n == Nat.add(1n, T.Tower.depth(rx)) : Nat},
        NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
    case T.Base{a} T.Ext{ry, iy, dy}:
      {==}
    case T.Base{a} T.Bad{}:
      {==}
    case T.Base{a} T.Fuel{}:
      {==}
    case T.Bad{} T.Base{b}:
      {==}
    case T.Bad{} T.Ext{ry, iy, dy}:
      {==}
    case T.Bad{} T.Bad{}:
      {==}
    case T.Bad{} T.Fuel{}:
      {==}
    case T.Fuel{} T.Base{b}:
      {==}
    case T.Fuel{} T.Ext{ry, iy, dy}:
      {==}
    case T.Fuel{} T.Bad{}:
      {==}
    case T.Fuel{} T.Fuel{}:
      {==}

def T.Tower.add.clean(x, y, hx, hy, h):
  match x y:
    case T.Base{a} T.Base{b}:
      T.CleanOk{}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
      T.CleanExt{+hyr, +hyi, +hyd, +hyri, +hyrd} = hy
      +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)
      +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
              Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
              Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                er, hyri))
      +cr = T.Tower.add.clean(rx, ry, hxr, hyr, er)
      +ci = T.Tower.add.clean(ix, iy, hxi, hyi, ei)
      +dr = T.Tower.add.depth(rx, ry, er)
      +di = T.Tower.add.depth(ix, iy, ei)
      T.CleanExt{cr, ci, hxd,
        Equal.trans(Nat,
          T.Tower.depth(T.Tower.add(rx, ry)), T.Tower.depth(ix),
          T.Tower.depth(T.Tower.add(ix, iy)),
          Equal.trans(Nat, T.Tower.depth(T.Tower.add(rx, ry)),
            T.Tower.depth(rx), T.Tower.depth(ix), dr, hxri),
          Equal.sym(Nat, T.Tower.depth(T.Tower.add(ix, iy)), T.Tower.depth(ix), di)),
        Equal.trans(Nat, T.Tower.depth(T.Tower.add(rx, ry)),
          T.Tower.depth(rx), T.Tower.depth(dx), dr, hxrd)}
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd(Empty,
        NH.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          0n, Nat.add(1n, T.Tower.depth(ry)), h)))
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd(Empty,
        NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
          Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
    case T.Bad{} _:
      Empty.absurd(T.Tower.clean(T.Tower.add(T.Bad{}, y)), hx)
    case T.Fuel{} _:
      Empty.absurd(T.Tower.clean(T.Tower.add(T.Fuel{}, y)), hx)
    case _ T.Bad{}:
      Empty.absurd(T.Tower.clean(T.Tower.add(x, T.Bad{})), hy)
    case _ T.Fuel{}:
      Empty.absurd(T.Tower.clean(T.Tower.add(x, T.Fuel{})), hy)

def TH.Tower.mul.fuel.base(g, a, b):
  T.CleanOk{}

def TH.Tower.mul.fuel.zero(x, y):
  {==}

# The product's two facts, in one induction
# =========================================
#
# The fuel match is forced, not stylistic. Bend wants a self-call's arguments to
# read left to right with each unchanged until one shrinks, and the third
# recursive call is mul(g, mul(g, ix, iy), dx) -- a computed product in the
# second slot. Matching the fuel parameter puts `g` in scope as a strict subterm
# of it, so the fuel shrinks in the first slot and every later argument is free.
# That is the same move Tower.mul's own definition makes, and it is why the law
# takes the fuel as a parameter instead of spelling the conclusion at `1n+g`.
#
# The Ext/Ext arm is the whole content. Four recursive calls at the smaller fuel
# hand back both facts about the four sub-products: M1 = mul(g, rx, ry),
# M2 = mul(g, mul(g, ix, iy), dx), M3 = mul(g, rx, iy) and M4 = mul(g, ix, ry).
# The third call is the one that needs the pair -- its first operand is a
# product, so its cleanliness is the second call's conclusion and its level
# relation is the second call's depth fact chained through the operands'
# hri/hrd fields. Each call also needs its own sufficiency equation: the fuel one
# level down is exactly 1n+depth(operand), which hf gives at this level and the
# match's succ_inj turns into the next level's.
#
# From there it is the add.clean assembly twice: each sum is clean by add.clean
# and sits at its first summand's level by add.depth, and the result's own level
# relations and depth are those two chains glued together.
#
# The marker and mixed-shape arms are absurdity, exactly as in add.clean: the
# mixed shapes contradict the equal-depth hypothesis, and a marker operand's own
# cleanliness evidence is Empty. They name their goal type in the statement's
# spelling, because mul with a variable in the second slot does not reduce.

def TH.Tower.mul.safe(f, x, y, hx, hy, h, hf):
  match f:
    case 0n:
      Empty.absurd(TH.Tower.Safe<x, T.Tower.mul(f, x, y)>,
        NH.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n), 0n,
          Nat.add(1n, T.Tower.depth(x)), hf)))
    case 1n+g:
      match x y:
        case T.Base{a} T.Base{b}:
          TH.SafeExt{T.CleanOk{}, {==}}
        case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
          T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
          T.CleanExt{+hyr, +hyi, +hyd, +hyri, +hyrd} = hy
          +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)
          +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
                  Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                    er, hyri))
          # the fuel, one level down: g == 1n+depth(rx)
          +ef = Equal.trans(Nat, Nat.add(1n, g), f,
                  Nat.add(1n, Nat.add(1n, T.Tower.depth(rx))), {==},
                  Equal.trans(Nat, f, Nat.add(1n, T.Tower.depth(x)),
                    Nat.add(1n, Nat.add(1n, T.Tower.depth(rx))), hf, {==}))
          +hf1 = N.succ_inj(g, Nat.add(1n, T.Tower.depth(rx)), ef)
          +hf2 = Equal.trans(Nat, g, Nat.add(1n, T.Tower.depth(rx)),
                  Nat.add(1n, T.Tower.depth(ix)), hf1,
                  Equal.cong(Nat, Nat, u => Nat.add(1n, u),
                    T.Tower.depth(rx), T.Tower.depth(ix), hxri))
          +cs1 = TH.Tower.safe.clean(g, rx, ry,
                  TH.Tower.mul.safe(g, rx, ry, hxr, hyr, er, hf1))
          +hd1 = TH.Tower.safe.depth(g, rx, ry,
                  TH.Tower.mul.safe(g, rx, ry, hxr, hyr, er, hf1))
          +cs2i = TH.Tower.safe.clean(g, ix, iy,
                  TH.Tower.mul.safe(g, ix, iy, hxi, hyi, ei, hf2))
          +hd2i = TH.Tower.safe.depth(g, ix, iy,
                  TH.Tower.mul.safe(g, ix, iy, hxi, hyi, ei, hf2))
          +e2 = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                  T.Tower.depth(ix), T.Tower.depth(dx), hd2i,
                  Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx),
                    T.Tower.depth(dx),
                    Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri), hxrd))
          +hf3 = Equal.trans(Nat, g, Nat.add(1n, T.Tower.depth(ix)),
                  Nat.add(1n, T.Tower.depth(T.Tower.mul(g, ix, iy))), hf2,
                  Equal.cong(Nat, Nat, u => Nat.add(1n, u),
                    T.Tower.depth(ix), T.Tower.depth(T.Tower.mul(g, ix, iy)),
                    Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                      T.Tower.depth(ix), hd2i)))
          +cs2 = TH.Tower.safe.clean(g, T.Tower.mul(g, ix, iy), dx,
                  TH.Tower.mul.safe(g, T.Tower.mul(g, ix, iy), dx, cs2i, hxd, e2, hf3))
          +hd2 = TH.Tower.safe.depth(g, T.Tower.mul(g, ix, iy), dx,
                  TH.Tower.mul.safe(g, T.Tower.mul(g, ix, iy), dx, cs2i, hxd, e2, hf3))
          +e3 = Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry),
                  T.Tower.depth(iy), er, hyri)
          +cs3 = TH.Tower.safe.clean(g, rx, iy,
                  TH.Tower.mul.safe(g, rx, iy, hxr, hyi, e3, hf1))
          +hd3 = TH.Tower.safe.depth(g, rx, iy,
                  TH.Tower.mul.safe(g, rx, iy, hxr, hyi, e3, hf1))
          +e4 = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx),
                  T.Tower.depth(ry),
                  Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri), er)
          +cs4 = TH.Tower.safe.clean(g, ix, ry,
                  TH.Tower.mul.safe(g, ix, ry, hxi, hyr, e4, hf2))
          +hd4 = TH.Tower.safe.depth(g, ix, ry,
                  TH.Tower.mul.safe(g, ix, ry, hxi, hyr, e4, hf2))
          +es = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)),
                  T.Tower.depth(rx),
                  T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)), hd1,
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ix),
                    T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                    hxri,
                    Equal.trans(Nat, T.Tower.depth(ix),
                      T.Tower.depth(T.Tower.mul(g, ix, iy)),
                      T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                      Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                        T.Tower.depth(ix), hd2i),
                      Equal.sym(Nat,
                        T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                        T.Tower.depth(T.Tower.mul(g, ix, iy)), hd2))))
          +et = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, iy)),
                  T.Tower.depth(rx), T.Tower.depth(T.Tower.mul(g, ix, ry)), hd3,
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ix),
                    T.Tower.depth(T.Tower.mul(g, ix, ry)),
                    hxri,
                    Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, ry)),
                      T.Tower.depth(ix), hd4)))
          +csA = T.Tower.add.clean(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx), cs1, cs2, es)
          +hdA = T.Tower.add.depth(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx), es)
          +csB = T.Tower.add.clean(T.Tower.mul(g, rx, iy),
                  T.Tower.mul(g, ix, ry), cs3, cs4, et)
          +hdB = T.Tower.add.depth(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry), et)
          +hdM1 = Equal.trans(Nat,
                  T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                  T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(rx), hdA, hd1)
          +hdM3 = Equal.trans(Nat,
                  T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                    T.Tower.mul(g, ix, ry))),
                  T.Tower.depth(T.Tower.mul(g, rx, iy)), T.Tower.depth(rx), hdB, hd3)
          TH.SafeExt{
            T.CleanExt{csA, csB, hxd,
              Equal.trans(Nat,
                T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                T.Tower.depth(T.Tower.mul(g, rx, ry)),
                T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                  T.Tower.mul(g, ix, ry))),
                hdA,
                Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)),
                  T.Tower.depth(rx),
                  T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                    T.Tower.mul(g, ix, ry))),
                  hd1,
                  Equal.sym(Nat,
                    T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry))),
                    T.Tower.depth(rx), hdM3))),
              Equal.trans(Nat,
                T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(dx), hdA,
                Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)),
                  T.Tower.depth(rx), T.Tower.depth(dx), hd1, hxrd))},
            Equal.cong(Nat, Nat, u => Nat.add(1n, u),
              T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
              T.Tower.depth(rx), hdM1)}
        case T.Base{a} T.Ext{ry, iy, dy}:
          Empty.absurd(TH.Tower.Safe<T.Base{a}, T.Tower.mul(f, T.Base{a},
              T.Ext{ry, iy, dy})>,
            NH.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
              0n, Nat.add(1n, T.Tower.depth(ry)), h)))
        case T.Ext{rx, ix, dx} T.Base{b}:
          Empty.absurd(TH.Tower.Safe<T.Ext{rx, ix, dx}, T.Tower.mul(f,
              T.Ext{rx, ix, dx}, T.Base{b})>,
            NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
              Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
        case T.Bad{} _:
          Empty.absurd(TH.Tower.Safe<T.Bad{}, T.Tower.mul(f, T.Bad{}, y)>, hx)
        case T.Fuel{} _:
          Empty.absurd(TH.Tower.Safe<T.Fuel{}, T.Tower.mul(f, T.Fuel{}, y)>, hx)
        case _ T.Bad{}:
          Empty.absurd(TH.Tower.Safe<x, T.Tower.mul(f, x, T.Bad{})>, hy)
        case _ T.Fuel{}:
          Empty.absurd(TH.Tower.Safe<x, T.Tower.mul(f, x, T.Fuel{})>, hy)

# The two readable laws are projections of the pair, at the exact fuel
def T.Tower.mul.depth(x, y, hx, hy, h):
  TH.Tower.safe.depth(Nat.add(1n, T.Tower.depth(x)), x, y,
    TH.Tower.mul.safe(Nat.add(1n, T.Tower.depth(x)), x, y, hx, hy, h, {==}))

def T.Tower.mul.clean(x, y, hx, hy, h):
  TH.Tower.safe.clean(Nat.add(1n, T.Tower.depth(x)), x, y,
    TH.Tower.mul.safe(Nat.add(1n, T.Tower.depth(x)), x, y, hx, hy, h, {==}))

# x - y = x + (-y): the definition's own unfolding, so the fill is {==}. Unfolding
# Tower.sub is all that happens here -- no operand evidence is involved, which is
# why this law of the identity block is provable while its neighbours wait on the
# coefficient facts recorded in PROVING round forty-seven.
def T.Tower.sub_eq_add_neg(x, y):
  {==}

# The fuel law's induction: clean, level and value at any fuel above the threshold
# ==============================================================================
#
# One induction returns all three facts because each recursive call needs one of
# the others: the third call multiplies `mul(g, ix, iy)` by dx, so it needs that
# product's *clean* evidence and its *depth*, and both are statements about the
# product at the fuel this call is made with -- exactly what the recursive
# instance hands back. The pair law of round forty-five could use the exact-fuel
# pair for that because there the fuel one level down is exactly sufficient; here
# it may be larger, so the facts have to come back at the larger fuel too.
#
# What is new after mul.safe is the fuel rewriting in the assembly. A recursive
# instance states its threshold product at *its own* first operand's threshold
# (1n+depth(rx) for the (rx,ry) instance, 1n+depth(ix) for the (ix,iy) one),
# while the goal wants the first operand's level throughout. So the goal's term
# has to be moved across an equality between two spelled fuels, which is
# congruence in mul's fuel slot -- a lambda over a `+`-marked parameter, measured
# legal in probe.cong.bend along with a lambda that builds a constructor.
#
# The mixed-shape and marker arms are absurdity, exactly as in mul.safe: a marker
# operand's own clean evidence is Empty, and two different shapes contradict the
# equal-depth hypothesis.
def TH.Tower.mul.above(f, x, y, hx, hy, h, hf):
  match f:
    case 0n:
      Empty.absurd(TH.Tower.Above<x, f, y>, NH.cmp_lt_zero(T.Tower.depth(x), hf))
    case 1n+g:
      match x y:
        case T.Base{a} T.Base{b}:
          TH.AboveExt{T.CleanOk{}, {==}, {==}}
        case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
          T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
          T.CleanExt{+hyr, +hyi, +hyd, +hyri, +hyrd} = hy
          +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)
          +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
                  Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                    er, hyri))
          # hf is consumed once here and copied into a reusable binder: the
          # hypothesis is wanted by the (rx,ry) and (rx,iy) instances and stands
          # as the second leg of the transport in hfi
          +hf1 = hf
          # the fuel hypothesis with its successor stripped: hf is
          # {cmp(1n+depth(rx), 1n+g) == LT}, which is {cmp(depth(rx), g) == LT}
          # by the checker's own reduction on Nat.cmp
          +hfi = Equal.trans(Cmp, Nat.cmp(T.Tower.depth(ix), g), Nat.cmp(T.Tower.depth(rx), g),
                  LT{},
                  Equal.sym(Cmp, Nat.cmp(T.Tower.depth(rx), g), Nat.cmp(T.Tower.depth(ix), g),
                    Equal.cong(Nat, Cmp, u => Nat.cmp(u, g), T.Tower.depth(rx),
                      T.Tower.depth(ix), hxri)),
                  hf1)
          # the four sub-products, each instance returning clean, level and value
          +a1 = TH.Tower.mul.above(g, rx, ry, hxr, hyr, er, hf1)
          +cs1 = TH.Tower.above.clean(g, rx, ry, a1)
          +hd1 = TH.Tower.above.depth(g, rx, ry, a1)
          +eq1 = TH.Tower.above.eq(g, rx, ry, a1)
          +a2 = TH.Tower.mul.above(g, ix, iy, hxi, hyi, ei, hfi)
          +cs2i = TH.Tower.above.clean(g, ix, iy, a2)
          +hd2i = TH.Tower.above.depth(g, ix, iy, a2)
          +eq2 = TH.Tower.above.eq(g, ix, iy, a2)
          +e2 = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                  T.Tower.depth(ix), T.Tower.depth(dx), hd2i,
                  Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(dx),
                    Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri), hxrd))
          +hf3 = Equal.trans(Cmp, Nat.cmp(T.Tower.depth(T.Tower.mul(g, ix, iy)), g),
                  Nat.cmp(T.Tower.depth(ix), g), LT{},
                  Equal.sym(Cmp, Nat.cmp(T.Tower.depth(ix), g),
                    Nat.cmp(T.Tower.depth(T.Tower.mul(g, ix, iy)), g),
                    Equal.cong(Nat, Cmp, u => Nat.cmp(u, g), T.Tower.depth(ix),
                      T.Tower.depth(T.Tower.mul(g, ix, iy)),
                      Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                        T.Tower.depth(ix), hd2i))),
                  hfi)
          +a3 = TH.Tower.mul.above(g, T.Tower.mul(g, ix, iy), dx, cs2i, hxd, e2, hf3)
          +cs2 = TH.Tower.above.clean(g, T.Tower.mul(g, ix, iy), dx, a3)
          +hd2 = TH.Tower.above.depth(g, T.Tower.mul(g, ix, iy), dx, a3)
          +eq3 = TH.Tower.above.eq(g, T.Tower.mul(g, ix, iy), dx, a3)
          +e3 = Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                  er, hyri)
          +a4 = TH.Tower.mul.above(g, rx, iy, hxr, hyi, e3, hf1)
          +cs3 = TH.Tower.above.clean(g, rx, iy, a4)
          +hd3 = TH.Tower.above.depth(g, rx, iy, a4)
          +eq4 = TH.Tower.above.eq(g, rx, iy, a4)
          +e4 = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(ry),
                  Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri), er)
          +a5 = TH.Tower.mul.above(g, ix, ry, hxi, hyr, e4, hfi)
          +cs4 = TH.Tower.above.clean(g, ix, ry, a5)
          +hd4 = TH.Tower.above.depth(g, ix, ry, a5)
          +eq5 = TH.Tower.above.eq(g, ix, ry, a5)
          # the two thresholds agree: depth(ix) with depth(rx), and the depth of
          # the im*im product with depth(rx) (which is hd2i then hxri)
          +eGi = Equal.cong(Nat, Nat, u => Nat.add(1n, u), T.Tower.depth(ix),
                  T.Tower.depth(rx), Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri))
          +eG1 = Equal.cong(Nat, Nat, u => Nat.add(1n, u),
                  T.Tower.depth(T.Tower.mul(g, ix, iy)), T.Tower.depth(rx),
                  Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)), T.Tower.depth(ix),
                    T.Tower.depth(rx), hd2i,
                    Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri)))
          +es = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)),
                  T.Tower.depth(rx),
                  T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)), hd1,
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ix),
                    T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                    hxri,
                    Equal.trans(Nat, T.Tower.depth(ix),
                      T.Tower.depth(T.Tower.mul(g, ix, iy)),
                      T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                      Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                        T.Tower.depth(ix), hd2i),
                      Equal.sym(Nat,
                        T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                        T.Tower.depth(T.Tower.mul(g, ix, iy)), hd2))))
          +et = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, iy)),
                  T.Tower.depth(rx), T.Tower.depth(T.Tower.mul(g, ix, ry)), hd3,
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ix),
                    T.Tower.depth(T.Tower.mul(g, ix, ry)),
                    hxri,
                    Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, ry)),
                      T.Tower.depth(ix), hd4)))
          +csA = T.Tower.add.clean(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx), cs1, cs2, es)
          +csB = T.Tower.add.clean(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry),
                  cs3, cs4, et)
          +hdA = T.Tower.add.depth(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx), es)
          +hdB = T.Tower.add.depth(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry), et)
          +hdM1 = Equal.trans(Nat,
                  T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                  T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(rx), hdA, hd1)
          +hdM3 = Equal.trans(Nat,
                  T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                    T.Tower.mul(g, ix, ry))),
                  T.Tower.depth(T.Tower.mul(g, rx, iy)), T.Tower.depth(rx), hdB, hd3)
          # the value field: the two coordinates, one fuel rewrite each where the
          # recursive instance's own threshold is not the first operand's
          +eq3a = Equal.trans(T.Tower, T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(T.Tower.mul(g, ix, iy))),
                    T.Tower.mul(g, ix, iy), dx),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), T.Tower.mul(g, ix, iy), dx),
                  eq3,
                  Equal.cong(Nat, T.Tower, u => T.Tower.mul(u, T.Tower.mul(g, ix, iy), dx),
                    Nat.add(1n, T.Tower.depth(T.Tower.mul(g, ix, iy))),
                    Nat.add(1n, T.Tower.depth(rx)), eG1))
          +eq2G = Equal.cong(Nat, T.Tower, u => T.Tower.mul(u, ix, iy),
                  Nat.add(1n, T.Tower.depth(ix)), Nat.add(1n, T.Tower.depth(rx)), eGi)
          +eq2s = Equal.trans(T.Tower, T.Tower.mul(g, ix, iy),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(ix)), ix, iy),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), eq2, eq2G)
          +eq3b = Equal.cong(T.Tower, T.Tower,
                  u => T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), u, dx),
                  T.Tower.mul(g, ix, iy),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), eq2s)
          +eqL2 = Equal.trans(T.Tower, T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), T.Tower.mul(g, ix, iy), dx),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx),
                  eq3a, eq3b)
          +eq5G = Equal.cong(Nat, T.Tower, u => T.Tower.mul(u, ix, ry),
                  Nat.add(1n, T.Tower.depth(ix)), Nat.add(1n, T.Tower.depth(rx)), eGi)
          +eqL4 = Equal.trans(T.Tower, T.Tower.mul(g, ix, ry),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(ix)), ix, ry),
                  T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, ry), eq5, eq5G)
          +eqA = Equal.trans(T.Tower,
                  T.Tower.add(T.Tower.mul(g, rx, ry),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                  T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                  T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx)),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Tower.add(u, T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                    T.Tower.mul(g, rx, ry),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry), eq1),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry), u),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx), eqL2))
          +eqB = Equal.trans(T.Tower,
                  T.Tower.add(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry)),
                  T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, iy),
                    T.Tower.mul(g, ix, ry)),
                  T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, iy),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, ry)),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Tower.add(u, T.Tower.mul(g, ix, ry)),
                    T.Tower.mul(g, rx, iy),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, iy), eq4),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, iy), u),
                    T.Tower.mul(g, ix, ry),
                    T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, ry), eqL4))
          +eqExt = Equal.trans(T.Tower,
                  T.Ext{T.Tower.add(T.Tower.mul(g, rx, ry),
                      T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                    T.Tower.add(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry)), dx},
                  T.Ext{T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                        T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx)),
                    T.Tower.add(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry)), dx},
                  T.Ext{T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                        T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx)),
                    T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, iy),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, ry)), dx},
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Ext{u, T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry)), dx},
                    T.Tower.add(T.Tower.mul(g, rx, ry),
                      T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                    T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                        T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx)), eqA),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Ext{T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, ry),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)),
                        T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, iy), dx)), u, dx},
                    T.Tower.add(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry)),
                    T.Tower.add(T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), rx, iy),
                      T.Tower.mul(Nat.add(1n, T.Tower.depth(rx)), ix, ry)), eqB))
          TH.AboveExt{
            T.CleanExt{csA, csB, hxd,
              Equal.trans(Nat,
                T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                T.Tower.depth(T.Tower.mul(g, rx, ry)),
                T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                  T.Tower.mul(g, ix, ry))),
                hdA,
                Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)),
                  T.Tower.depth(rx),
                  T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                    T.Tower.mul(g, ix, ry))),
                  hd1,
                  Equal.sym(Nat,
                    T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry))),
                    T.Tower.depth(rx), hdM3))),
              Equal.trans(Nat,
                T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                  T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(dx), hdA,
                Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)),
                  T.Tower.depth(rx), T.Tower.depth(dx), hd1, hxrd))},
            Equal.cong(Nat, Nat, u => Nat.add(1n, u),
              T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
              T.Tower.depth(rx), hdM1),
            eqExt}
        case T.Base{a} T.Ext{ry, iy, dy}:
          Empty.absurd(TH.Tower.Above<T.Base{a}, f, T.Ext{ry, iy, dy}>,
            NH.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
              0n, Nat.add(1n, T.Tower.depth(ry)), h)))
        case T.Ext{rx, ix, dx} T.Base{b}:
          Empty.absurd(TH.Tower.Above<T.Ext{rx, ix, dx}, f, T.Base{b}>,
            NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
              Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
        case T.Bad{} _:
          Empty.absurd(TH.Tower.Above<T.Bad{}, f, y>, hx)
        case T.Fuel{} _:
          Empty.absurd(TH.Tower.Above<T.Fuel{}, f, y>, hx)
        case _ T.Bad{}:
          Empty.absurd(TH.Tower.Above<x, f, T.Bad{}>, hy)
        case _ T.Fuel{}:
          Empty.absurd(TH.Tower.Above<x, f, T.Fuel{}>, hy)

# mul.fuel.ext is the third field of the same induction
def TH.Tower.mul.fuel.ext(f, x, y, hx, hy, h, hf):
  TH.Tower.above.eq(f, x, y, TH.Tower.mul.above(f, x, y, hx, hy, h, hf))
