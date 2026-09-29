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
# the commutativity law reaches the Rat leaves, where Rat.add_comm is unconditional
import ./rat.bend as R
import ./rat_helpers.bend as RH

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

# add_comm: the first law that needs the level witness, and one of the two that
# need nothing of the coefficients -- Rat.add_comm is unconditional. The Ext arm
# destructures the witness with a single case, because Tower.same reduces to
# Tower.Same.Ext there; the disagreeing arms carry Empty and go absurd, and the
# two marker arms are `{==}` -- add of a marker is that marker whichever side it
# is on. Four witness arms and twelve Empty arms, because the family was extended
# to agree on markers (round fifty-one) and a wildcard would leave it stuck.
def T.Tower.add_comm(x, y, hs):
  match x y:
    case T.Base{a} T.Base{b}:
      Equal.cong(R.Rat, T.Tower, u => T.Base{u}, R.Rat.add(a, b),
        R.Rat.add(b, a), R.Rat.add_comm(a, b))
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      match hs:
        case T.SameExt{+sre, +sim, +sd}:
          +e1 = T.Tower.add_comm(rx, ry, sre)
          +e2 = T.Tower.add_comm(ix, iy, sim)
          +eA = Equal.cong(T.Tower, T.Tower,
            u => T.Ext{u, T.Tower.add(ix, iy), dx},
            T.Tower.add(rx, ry), T.Tower.add(ry, rx), e1)
          +eB = Equal.cong(T.Tower, T.Tower,
            u => T.Ext{T.Tower.add(ry, rx), u, dx},
            T.Tower.add(ix, iy), T.Tower.add(iy, ix), e2)
          +eC = Equal.cong(T.Tower, T.Tower,
            u => T.Ext{T.Tower.add(ry, rx), T.Tower.add(iy, ix), u}, dx, dy, sd)
          Equal.trans(T.Tower,
            T.Ext{T.Tower.add(rx, ry), T.Tower.add(ix, iy), dx},
            T.Ext{T.Tower.add(ry, rx), T.Tower.add(ix, iy), dx},
            T.Ext{T.Tower.add(ry, rx), T.Tower.add(iy, ix), dy},
            eA,
            Equal.trans(T.Tower,
              T.Ext{T.Tower.add(ry, rx), T.Tower.add(ix, iy), dx},
              T.Ext{T.Tower.add(ry, rx), T.Tower.add(iy, ix), dx},
              T.Ext{T.Tower.add(ry, rx), T.Tower.add(iy, ix), dy},
              eB, eC))
    case T.Bad{} T.Bad{}:
      {==}
    case T.Fuel{} T.Fuel{}:
      {==}
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Base{a} T.Bad{}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Base{a} T.Fuel{}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Bad{} T.Base{b}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Bad{} T.Ext{ry, iy, dy}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Bad{} T.Fuel{}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Fuel{} T.Base{b}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Fuel{} T.Ext{ry, iy, dy}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)
    case T.Fuel{} T.Bad{}:
      Empty.absurd({T.Tower.add(x, y) == T.Tower.add(y, x) : T.Tower}, hs)

# same.sym is a shape induction with the witness swapped: the Ext arm rebuilds
# Same.Ext from the two recursive instances and the symmetric radicand equation,
# and the twelve disagreeing arms carry Empty in the hypothesis and go absurd.
def TH.Tower.same.sym(x, y, hs):
  match x y:
    case T.Base{a} T.Base{b}:
      T.SameBase{}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      match hs:
        case T.SameExt{+sre, +sim, +sd}:
          T.SameExt{TH.Tower.same.sym(rx, ry, sre), TH.Tower.same.sym(ix, iy, sim),
            Equal.sym(T.Tower, dx, dy, sd)}
    case T.Bad{} T.Bad{}:
      T.SameBase{}
    case T.Fuel{} T.Fuel{}:
      T.SameBase{}
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Base{a} T.Bad{}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Base{a} T.Fuel{}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Bad{} T.Base{b}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Bad{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Bad{} T.Fuel{}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Fuel{} T.Base{b}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Fuel{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.same(y, x), hs)
    case T.Fuel{} T.Bad{}:
      Empty.absurd(T.Tower.same(y, x), hs)

# same.add is the same shape induction carried out over two pairs at once (256
# combinations collapse to sixteen arms, and the two hypotheses rule out the ones
# where a pair disagrees). The one arm with work in it is Ext/Ext/Ext/Ext: the two
# coordinates are recursive instances at the sub-witnesses and the radicand field
# is the outer hypothesis's. Every other agreeing arm lands on a marker on both
# sides -- add of a Bad or a Fuel is that marker, and the shapes decide it
# identically on the left and on the right -- so the witness there is the trivial
# one, which is what the marker arms of Tower.same exist for.
# same.add is a shape induction over two pairs at once. Two hundred and fifty-six
# combinations collapse to sixteen outer arms and sixteen inner ones; the twelve
# outer arms where x and y disagree carry Empty in hx and go absurd, and inside the
# four agreeing outer arms the inner disagreeing ones do the same with hu. The one
# arm with work in it is Ext/Ext/Ext/Ext: the two coordinates are recursive
# instances at the sub-witnesses and the radicand field is the outer hypothesis's.
# Every other agreeing arm lands on a marker on both sides -- add of a Bad or a Fuel
# is a marker, and the shapes decide it identically on the left and on the right --
# so the witness there is the trivial one, which is what the marker arms of
# Tower.same exist for. The recursive call's first argument is the outer Ext
# pattern's field, and the inner match's binders are named apart from it so that the
# shrinking argument is the one the checker sees.
def TH.Tower.same.add(x, y, u, v, hx, hu):
  match x y:
    case T.Base{a} T.Base{b}:
      match u v:
        case T.Base{c} T.Base{d}:
          T.SameBase{}
        case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
          T.SameBase{}
        case T.Bad{} T.Bad{}:
          T.SameBase{}
        case T.Fuel{} T.Fuel{}:
          T.SameBase{}
        case T.Base{c} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      match u v:
        case T.Base{c} T.Base{d}:
          T.SameBase{}
        case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
          match hx hu:
            case T.SameExt{+sre, +sim, +sd} T.SameExt{+ure, +uim, +ud}:
              T.SameExt{TH.Tower.same.add(rx, ry, ur, vr, sre, ure),
                TH.Tower.same.add(ix, iy, ui, vi, sim, uim), sd}
        case T.Bad{} T.Bad{}:
          T.SameBase{}
        case T.Fuel{} T.Fuel{}:
          T.SameBase{}
        case T.Base{c} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
    case T.Bad{} T.Bad{}:
      match u v:
        case T.Base{c} T.Base{d}:
          T.SameBase{}
        case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
          T.SameBase{}
        case T.Bad{} T.Bad{}:
          T.SameBase{}
        case T.Fuel{} T.Fuel{}:
          T.SameBase{}
        case T.Base{c} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
    case T.Fuel{} T.Fuel{}:
      match u v:
        case T.Base{c} T.Base{d}:
          T.SameBase{}
        case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
          T.SameBase{}
        case T.Bad{} T.Bad{}:
          T.SameBase{}
        case T.Fuel{} T.Fuel{}:
          T.SameBase{}
        case T.Base{c} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Base{c} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Ext{ur, ui, du} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Base{d}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Ext{vr, vi, dv}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hu)
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Base{a} T.Bad{}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Base{a} T.Fuel{}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Bad{} T.Base{b}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Bad{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Bad{} T.Fuel{}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Fuel{} T.Base{b}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Fuel{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)
    case T.Fuel{} T.Bad{}:
      Empty.absurd(T.Tower.same(T.Tower.add(x, u), T.Tower.add(y, v)), hx)

# same.of_eq: the equation rewrites the goal's y into x, and the shape induction runs
# in the rewritten goal. The ascription is the goal with the replaced occurrence as a
# hole -- here a type, not an equation, so it is spelled as the type.
def TH.Tower.same.of_eq(x, y, h):
  match x:
    case T.Base{a}:
      %h : T.Tower.same(T.Base{a}, _)
      T.SameBase{}
    case T.Ext{rx, ix, dx}:
      %h : T.Tower.same(T.Ext{rx, ix, dx}, _)
      T.SameExt{TH.Tower.same.of_eq(rx, rx, {==}), TH.Tower.same.of_eq(ix, ix, {==}),
        {==}}
    case T.Bad{}:
      %h : T.Tower.same(T.Bad{}, _)
      T.SameBase{}
    case T.Fuel{}:
      %h : T.Tower.same(T.Fuel{}, _)
      T.SameBase{}

# same.mul: the fuel case split sits in front of the shape induction. At 0n both sides
# are Fuel{} whatever the operands are, so the witness is trivial.
#
# At 1n+g the one arm with work is Ext/Ext/Ext/Ext, and it is where the law earns its
# keep. mul's Ext/Ext coordinates are
#   add(mul(g, rx, ru), mul(g, mul(g, ix, iu), dx))   and   add(mul(g, rx, iu), mul(g, ix, ru))
# so each coordinate is an add of two products, and the witness for an add of two pairs
# is same.add, with same.mul supplying the pair witnesses at the smaller fuel. One of
# those pairs is not a pair of operands but a pair of *products*: mul's third recursive
# call takes mul(g, ix, iu) as its first argument, so the instance needed is the law at
# (mul(g, ix, ui), mul(g, iy, vi)) paired with (dx, dy), whose first hypothesis is the
# recursive instance at (ix, iy) and whose second is the outer radicand equation --
# read through same.of_eq, because SameExt's third field is an equation and this law
# needs a witness. That is the whole reason this law exists rather than being folded
# into mul_comm.
#
# The marker arms follow mul's own precedence: a Fuel operand makes the product Fuel
# whichever side it is on, anything else mixed makes it Bad, and since both sides see
# the same shapes the two results are the same constructor -- so the witness is trivial
# there too, which is the marker arms of Tower.same doing their job.
def TH.Tower.same.mul(f, x, y, u, v, hx, hu):
  match f:
    case 0n:
      T.SameBase{}
    case 1n+g:
      match x y:
        case T.Base{a} T.Base{b}:
          match u v:
            case T.Base{c} T.Base{d}:
              T.SameBase{}
            case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
              T.SameBase{}
            case T.Bad{} T.Bad{}:
              T.SameBase{}
            case T.Fuel{} T.Fuel{}:
              T.SameBase{}
            case T.Base{c} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
        case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
          match u v:
            case T.Base{c} T.Base{d}:
              T.SameBase{}
            case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
              match hx hu:
                case T.SameExt{+sre, +sim, +sd} T.SameExt{+ure, +uim, +ud}:
                  +e1 = TH.Tower.same.mul(g, rx, ry, ur, vr, sre, ure)
                  +e2 = TH.Tower.same.mul(g, ix, iy, ui, vi, sim, uim)
                  +e3 = TH.Tower.same.mul(g, T.Tower.mul(g, ix, ui),
                    T.Tower.mul(g, iy, vi), dx, dy, e2, TH.Tower.same.of_eq(dx, dy, sd))
                  +e4 = TH.Tower.same.mul(g, rx, ry, ui, vi, sre, uim)
                  +e5 = TH.Tower.same.mul(g, ix, iy, ur, vr, sim, ure)
                  T.SameExt{
                    TH.Tower.same.add(T.Tower.mul(g, rx, ur), T.Tower.mul(g, ry, vr),
                      T.Tower.mul(g, T.Tower.mul(g, ix, ui), dx),
                      T.Tower.mul(g, T.Tower.mul(g, iy, vi), dy), e1, e3),
                    TH.Tower.same.add(T.Tower.mul(g, rx, ui), T.Tower.mul(g, ry, vi),
                      T.Tower.mul(g, ix, ur), T.Tower.mul(g, iy, vr), e4, e5),
                    sd}
            case T.Bad{} T.Bad{}:
              T.SameBase{}
            case T.Fuel{} T.Fuel{}:
              T.SameBase{}
            case T.Base{c} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
        case T.Bad{} T.Bad{}:
          match u v:
            case T.Base{c} T.Base{d}:
              T.SameBase{}
            case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
              T.SameBase{}
            case T.Bad{} T.Bad{}:
              T.SameBase{}
            case T.Fuel{} T.Fuel{}:
              T.SameBase{}
            case T.Base{c} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
        case T.Fuel{} T.Fuel{}:
          match u v:
            case T.Base{c} T.Base{d}:
              T.SameBase{}
            case T.Ext{ur, ui, du} T.Ext{vr, vi, dv}:
              T.SameBase{}
            case T.Bad{} T.Bad{}:
              T.SameBase{}
            case T.Fuel{} T.Fuel{}:
              T.SameBase{}
            case T.Base{c} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Base{c} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Ext{ur, ui, du} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Bad{} T.Fuel{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Base{d}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Ext{vr, vi, dv}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
            case T.Fuel{} T.Bad{}:
              Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hu)
        case T.Base{a} T.Ext{ry, iy, dy}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Base{a} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Base{a} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Ext{rx, ix, dx} T.Base{b}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Ext{rx, ix, dx} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Ext{rx, ix, dx} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Bad{} T.Base{b}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Bad{} T.Ext{ry, iy, dy}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Fuel{} T.Base{b}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Fuel{} T.Ext{ry, iy, dy}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.same(T.Tower.mul(f, x, u), T.Tower.mul(f, y, v)), hx)

def TH.Tower.level.refl(x):
  match x:
    case T.Base{a}:
      T.LevelBase{}
    case T.Ext{rx, ix, dx}:
      T.LevelExt{TH.Tower.level.refl(rx), TH.Tower.level.refl(ix), {==}}
    case T.Bad{}:
      T.LevelBase{}
    case T.Fuel{}:
      T.LevelBase{}

def TH.Tower.level.sym(x, y, h):
  match x y:
    case T.Base{a} T.Base{b}:
      T.LevelBase{}
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Base{a} T.Bad{}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Base{a} T.Fuel{}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      T.LevelExt{+lre, +lim, +ld} = h
      T.LevelExt{TH.Tower.level.sym(rx, ry, lre), TH.Tower.level.sym(ix, iy, lim),
                 Equal.sym(T.Tower, dx, dy, ld)}
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Bad{} T.Base{b}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Bad{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Bad{} T.Bad{}:
      T.LevelBase{}
    case T.Bad{} T.Fuel{}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Fuel{} T.Base{b}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Fuel{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Fuel{} T.Bad{}:
      Empty.absurd(T.Tower.level(y, x), h)
    case T.Fuel{} T.Fuel{}:
      T.LevelBase{}


def TH.Tower.level.trans(x, y, z, hxy, hyz):
  match x y:
    case T.Base{a} T.Base{b}:
      match z:
        case T.Base{c}:
          T.LevelBase{}
        case T.Ext{rz, iz, dz}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Bad{}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Fuel{}:
          Empty.absurd(T.Tower.level(x, z), hyz)
    case T.Base{a} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Base{a} T.Bad{}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Base{a} T.Fuel{}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Ext{rx, ix, dx} T.Base{b}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      match z:
        case T.Base{c}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Ext{rz, iz, dz}:
          T.LevelExt{+lre, +lim, +ld} = hxy
          T.LevelExt{+mre, +mim, +md} = hyz
          T.LevelExt{TH.Tower.level.trans(rx, ry, rz, lre, mre),
                     TH.Tower.level.trans(ix, iy, iz, lim, mim),
                     Equal.trans(T.Tower, dx, dy, dz, ld, md)}
        case T.Bad{}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Fuel{}:
          Empty.absurd(T.Tower.level(x, z), hyz)
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Bad{} T.Base{b}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Bad{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Bad{} T.Bad{}:
      match z:
        case T.Base{c}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Ext{rz, iz, dz}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Bad{}:
          T.LevelBase{}
        case T.Fuel{}:
          Empty.absurd(T.Tower.level(x, z), hyz)
    case T.Bad{} T.Fuel{}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Fuel{} T.Base{b}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Fuel{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Fuel{} T.Bad{}:
      Empty.absurd(T.Tower.level(x, z), hxy)
    case T.Fuel{} T.Fuel{}:
      match z:
        case T.Base{c}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Ext{rz, iz, dz}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Bad{}:
          Empty.absurd(T.Tower.level(x, z), hyz)
        case T.Fuel{}:
          T.LevelBase{}


def TH.Tower.pos.add(x, y, hx, hy):
  match x y:
    case T.Base{a} T.Base{b}:
      T.PosBase{+pa} = hx
      T.PosBase{+pb} = hy
      T.PosBase{R.Rat.add.den.pos(a, b, pa, pb)}
    case T.Base{a} T.Ext{ry, iy, dy}:
      T.PosOk{}
    case T.Base{a} T.Bad{}:
      T.PosOk{}
    case T.Base{a} T.Fuel{}:
      T.PosOk{}
    case T.Ext{rx, ix, dx} T.Base{b}:
      T.PosOk{}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      T.PosExt{+pre, +pim, +prad} = hx
      T.PosExt{+pre2, +pim2, +prad2} = hy
      T.PosExt{TH.Tower.pos.add(rx, ry, pre, pre2),
                TH.Tower.pos.add(ix, iy, pim, pim2),
                prad}
    case T.Ext{rx, ix, dx} T.Bad{}:
      T.PosOk{}
    case T.Ext{rx, ix, dx} T.Fuel{}:
      T.PosOk{}
    case T.Bad{} T.Base{b}:
      T.PosOk{}
    case T.Bad{} T.Ext{ry, iy, dy}:
      T.PosOk{}
    case T.Bad{} T.Bad{}:
      T.PosOk{}
    case T.Bad{} T.Fuel{}:
      T.PosOk{}
    case T.Fuel{} T.Base{b}:
      T.PosOk{}
    case T.Fuel{} T.Ext{ry, iy, dy}:
      T.PosOk{}
    case T.Fuel{} T.Bad{}:
      T.PosOk{}
    case T.Fuel{} T.Fuel{}:
      T.PosOk{}

def TH.Tower.pos.neg(x, hx):
  match x:
    case T.Base{a}:
      T.PosBase{+pa} = hx
      T.PosBase{R.Rat.neg.den.pos(a, pa)}
    case T.Ext{rx, ix, dx}:
      T.PosExt{+pre, +pim, +prad} = hx
      T.PosExt{TH.Tower.pos.neg(rx, pre), TH.Tower.pos.neg(ix, pim), prad}
    case T.Bad{}:
      T.PosOk{}
    case T.Fuel{}:
      T.PosOk{}

def TH.Tower.pos.mul(f, x, y, hx, hy):
  match f:
    case 0n:
      T.PosOk{}
    case 1n+g:
      match x y:
        case T.Base{a} T.Base{b}:
          T.PosBase{+pa} = hx
          T.PosBase{+pb} = hy
          T.PosBase{R.Rat.mul.den.pos(a, b, pa, pb)}
        case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
          T.PosExt{+pre, +pim, +prad} = hx
          T.PosExt{+pry, +piy, +pryd} = hy
          +hP = TH.Tower.pos.mul(g, ix, iy, pim, piy)
          +hrr = TH.Tower.pos.mul(g, rx, ry, pre, pry)
          +hri = TH.Tower.pos.mul(g, rx, iy, pre, piy)
          +hir = TH.Tower.pos.mul(g, ix, ry, pim, pry)
          +hPd = TH.Tower.pos.mul(g, T.Tower.mul(g, ix, iy), dx, hP, prad)
          T.PosExt{
            TH.Tower.pos.add(T.Tower.mul(g, rx, ry),
                             T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx), hrr, hPd),
            TH.Tower.pos.add(T.Tower.mul(g, rx, iy), T.Tower.mul(g, ix, ry), hri, hir),
            prad}
        case T.Base{a} T.Ext{ry, iy, dy}:
          T.PosOk{}
        case T.Ext{rx, ix, dx} T.Base{b}:
          T.PosOk{}
        case T.Fuel{} T.Base{b}:
          T.PosOk{}
        case T.Fuel{} T.Ext{ry, iy, dy}:
          T.PosOk{}
        case T.Fuel{} T.Bad{}:
          T.PosOk{}
        case T.Fuel{} T.Fuel{}:
          T.PosOk{}
        case T.Base{a} T.Fuel{}:
          T.PosOk{}
        case T.Ext{rx, ix, dx} T.Fuel{}:
          T.PosOk{}
        case T.Bad{} T.Base{b}:
          T.PosOk{}
        case T.Bad{} T.Ext{ry, iy, dy}:
          T.PosOk{}
        case T.Bad{} T.Bad{}:
          T.PosOk{}
        case T.Bad{} T.Fuel{}:
          T.PosOk{}
        case T.Ext{rx, ix, dx} T.Bad{}:
          T.PosOk{}
        case T.Base{a} T.Bad{}:
          T.PosOk{}


def TH.Tower.level.add(x, y, u, v, hxy, huv, hxu, hyv):
  match x y:
    case T.Base{ax} T.Base{ay}:
      match u v:
        case T.Base{au} T.Base{av}:
          T.LevelBase{}
        case T.Base{au} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Ext{ru, iu, du} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
    case T.Base{ax} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Base{ax} T.Bad{}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Base{ax} T.Fuel{}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Ext{rx, ix, dx} T.Base{ay}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      match u v:
        case T.Base{au} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Base{au} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
          T.LevelExt{+lrer, +limr, +ldr} = hxy
          T.LevelExt{+lreu, +limu, +ldu} = huv
          T.LevelExt{+lrex, +limx, +ldx} = hxu
          T.LevelExt{+lrey, +limy, +ldy} = hyv
          +ere = TH.Tower.level.add(rx, ry, ru, rv, lrer, lreu, lrex, lrey)
          +eim = TH.Tower.level.add(ix, iy, iu, iv, limr, limu, limx, limy)
          T.LevelExt{ere, eim, ldx}
        case T.Ext{ru, iu, du} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
    case T.Ext{rx, ix, dx} T.Bad{}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Ext{rx, ix, dx} T.Fuel{}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Bad{} T.Base{ay}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Bad{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Bad{} T.Bad{}:
      match u v:
        case T.Base{au} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Base{au} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Ext{ru, iu, du} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Bad{}:
          T.LevelBase{}
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
    case T.Bad{} T.Fuel{}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Fuel{} T.Base{ay}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Fuel{} T.Ext{ry, iy, dy}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Fuel{} T.Bad{}:
      Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxy)
    case T.Fuel{} T.Fuel{}:
      match u v:
        case T.Base{au} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Base{au} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Base{au} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Ext{ru, iu, du} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Ext{ru, iu, du} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Bad{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), hxu)
        case T.Bad{} T.Fuel{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Base{av}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Ext{rv, iv, dv}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Bad{}:
          Empty.absurd(T.Tower.level(T.Tower.add(x, y), T.Tower.add(u, v)), huv)
        case T.Fuel{} T.Fuel{}:
          T.LevelBase{}

def T.Tower.add_assoc(x, y, z, hx, hy, hz, px, py, pz, hxy, hyz):
  match x y z:
    case T.Base{a} T.Base{b} T.Base{c}:
      T.PosBase{+pa} = px
      T.PosBase{+pb} = py
      T.PosBase{+pc} = pz
      Equal.cong(R.Rat, T.Tower, u => T.Base{u},
        R.Rat.add(R.Rat.add(a, b), c), R.Rat.add(a, R.Rat.add(b, c)),
        RH.Rat.add_assoc.arb(a, b, c, pa, pb, pc))
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy} T.Ext{rz, iz, dz}:
      T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
      T.CleanExt{+hyr, +hyi, +hyd, +hyri, +hyrd} = hy
      T.CleanExt{+hzr, +hzi, +hzd, +hzri, +hzrd} = hz
      T.PosExt{+prer, +pimr, +pradr} = px
      T.PosExt{+prey, +pimy, +prady} = py
      T.PosExt{+prez, +pimz, +pradz} = pz
      +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), hxy)
      +eyz = N.succ_inj(T.Tower.depth(ry), T.Tower.depth(rz), hyz)
      +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
              Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
              Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                er, hyri))
      +eiz = Equal.trans(Nat, T.Tower.depth(iy), T.Tower.depth(ry), T.Tower.depth(iz),
               Equal.sym(Nat, T.Tower.depth(ry), T.Tower.depth(iy), hyri),
               Equal.trans(Nat, T.Tower.depth(ry), T.Tower.depth(rz), T.Tower.depth(iz),
                 eyz, hzri))
      +e1 = T.Tower.add_assoc(rx, ry, rz, hxr, hyr, hzr, prer, prey, prez, er, eyz)
      +e2 = T.Tower.add_assoc(ix, iy, iz, hxi, hyi, hzi, pimr, pimy, pimz, ei, eiz)
      +c1 = Equal.cong(T.Tower, T.Tower,
              u => T.Ext{u, T.Tower.add(T.Tower.add(ix, iy), iz), dx},
              T.Tower.add(T.Tower.add(rx, ry), rz),
              T.Tower.add(rx, T.Tower.add(ry, rz)), e1)
      +c2 = Equal.cong(T.Tower, T.Tower,
              u => T.Ext{T.Tower.add(rx, T.Tower.add(ry, rz)), u, dx},
              T.Tower.add(T.Tower.add(ix, iy), iz),
              T.Tower.add(ix, T.Tower.add(iy, iz)), e2)
      Equal.trans(T.Tower,
        T.Ext{T.Tower.add(T.Tower.add(rx, ry), rz), T.Tower.add(T.Tower.add(ix, iy), iz), dx},
        T.Ext{T.Tower.add(rx, T.Tower.add(ry, rz)), T.Tower.add(T.Tower.add(ix, iy), iz), dx},
        T.Ext{T.Tower.add(rx, T.Tower.add(ry, rz)), T.Tower.add(ix, T.Tower.add(iy, iz)), dx},
        c1, c2)
    case T.Base{a} T.Base{b} T.Ext{rz, iz, dz}:
      {==}
    case T.Base{a} T.Base{b} T.Bad{}:
      {==}
    case T.Base{a} T.Base{b} T.Fuel{}:
      {==}
    case T.Base{a} T.Ext{ry, iy, dy} T.Base{c}:
      {==}
    case T.Base{a} T.Ext{ry, iy, dy} T.Ext{rz, iz, dz}:
      {==}
    case T.Base{a} T.Ext{ry, iy, dy} T.Bad{}:
      {==}
    case T.Base{a} T.Ext{ry, iy, dy} T.Fuel{}:
      {==}
    case T.Base{a} T.Bad{} T.Base{c}:
      {==}
    case T.Base{a} T.Bad{} T.Ext{rz, iz, dz}:
      {==}
    case T.Base{a} T.Bad{} T.Bad{}:
      {==}
    case T.Base{a} T.Bad{} T.Fuel{}:
      {==}
    case T.Base{a} T.Fuel{} T.Base{c}:
      {==}
    case T.Base{a} T.Fuel{} T.Ext{rz, iz, dz}:
      {==}
    case T.Base{a} T.Fuel{} T.Bad{}:
      {==}
    case T.Base{a} T.Fuel{} T.Fuel{}:
      {==}
    case T.Ext{rx, ix, dx} T.Base{b} T.Base{c}:
      {==}
    case T.Ext{rx, ix, dx} T.Base{b} T.Ext{rz, iz, dz}:
      {==}
    case T.Ext{rx, ix, dx} T.Base{b} T.Bad{}:
      {==}
    case T.Ext{rx, ix, dx} T.Base{b} T.Fuel{}:
      {==}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy} T.Base{c}:
      {==}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy} T.Bad{}:
      {==}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy} T.Fuel{}:
      {==}
    case T.Ext{rx, ix, dx} T.Bad{} T.Base{c}:
      {==}
    case T.Ext{rx, ix, dx} T.Bad{} T.Ext{rz, iz, dz}:
      {==}
    case T.Ext{rx, ix, dx} T.Bad{} T.Bad{}:
      {==}
    case T.Ext{rx, ix, dx} T.Bad{} T.Fuel{}:
      {==}
    case T.Ext{rx, ix, dx} T.Fuel{} T.Base{c}:
      {==}
    case T.Ext{rx, ix, dx} T.Fuel{} T.Ext{rz, iz, dz}:
      {==}
    case T.Ext{rx, ix, dx} T.Fuel{} T.Bad{}:
      {==}
    case T.Ext{rx, ix, dx} T.Fuel{} T.Fuel{}:
      {==}
    case T.Bad{} T.Base{b} T.Base{c}:
      {==}
    case T.Bad{} T.Base{b} T.Ext{rz, iz, dz}:
      {==}
    case T.Bad{} T.Base{b} T.Bad{}:
      {==}
    case T.Bad{} T.Base{b} T.Fuel{}:
      {==}
    case T.Bad{} T.Ext{ry, iy, dy} T.Base{c}:
      {==}
    case T.Bad{} T.Ext{ry, iy, dy} T.Ext{rz, iz, dz}:
      {==}
    case T.Bad{} T.Ext{ry, iy, dy} T.Bad{}:
      {==}
    case T.Bad{} T.Ext{ry, iy, dy} T.Fuel{}:
      {==}
    case T.Bad{} T.Bad{} T.Base{c}:
      {==}
    case T.Bad{} T.Bad{} T.Ext{rz, iz, dz}:
      {==}
    case T.Bad{} T.Bad{} T.Bad{}:
      {==}
    case T.Bad{} T.Bad{} T.Fuel{}:
      {==}
    case T.Bad{} T.Fuel{} T.Base{c}:
      {==}
    case T.Bad{} T.Fuel{} T.Ext{rz, iz, dz}:
      {==}
    case T.Bad{} T.Fuel{} T.Bad{}:
      {==}
    case T.Bad{} T.Fuel{} T.Fuel{}:
      {==}
    case T.Fuel{} T.Base{b} T.Base{c}:
      {==}
    case T.Fuel{} T.Base{b} T.Ext{rz, iz, dz}:
      {==}
    case T.Fuel{} T.Base{b} T.Bad{}:
      {==}
    case T.Fuel{} T.Base{b} T.Fuel{}:
      {==}
    case T.Fuel{} T.Ext{ry, iy, dy} T.Base{c}:
      {==}
    case T.Fuel{} T.Ext{ry, iy, dy} T.Ext{rz, iz, dz}:
      {==}
    case T.Fuel{} T.Ext{ry, iy, dy} T.Bad{}:
      {==}
    case T.Fuel{} T.Ext{ry, iy, dy} T.Fuel{}:
      {==}
    case T.Fuel{} T.Bad{} T.Base{c}:
      {==}
    case T.Fuel{} T.Bad{} T.Ext{rz, iz, dz}:
      {==}
    case T.Fuel{} T.Bad{} T.Bad{}:
      {==}
    case T.Fuel{} T.Bad{} T.Fuel{}:
      {==}
    case T.Fuel{} T.Fuel{} T.Base{c}:
      {==}
    case T.Fuel{} T.Fuel{} T.Ext{rz, iz, dz}:
      {==}
    case T.Fuel{} T.Fuel{} T.Bad{}:
      {==}
    case T.Fuel{} T.Fuel{} T.Fuel{}:
      {==}

def T.Tower.add_neg(x, hx, px):
  match x:
    case T.Base{a}:
      T.PosBase{+pa} = px
      Equal.cong(R.Rat, T.Tower, u => T.Base{u},
        R.Rat.add(a, R.Rat.neg(a)), R.Rat.zero(), R.Rat.add_neg(a, pa))
    case T.Ext{rx, ix, dx}:
      T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
      T.PosExt{+pre, +pim, +prad} = px
      +c1 = Equal.cong(T.Tower, T.Tower,
              u => T.Ext{u, T.Tower.add(ix, T.Tower.neg(ix)), dx},
              T.Tower.add(rx, T.Tower.neg(rx)), T.Tower.zero(rx),
              T.Tower.add_neg(rx, hxr, pre))
      +c2 = Equal.cong(T.Tower, T.Tower,
              u => T.Ext{T.Tower.zero(rx), u, dx},
              T.Tower.add(ix, T.Tower.neg(ix)), T.Tower.zero(ix),
              T.Tower.add_neg(ix, hxi, pim))
      Equal.trans(T.Tower,
        T.Ext{T.Tower.add(rx, T.Tower.neg(rx)), T.Tower.add(ix, T.Tower.neg(ix)), dx},
        T.Ext{T.Tower.zero(rx), T.Tower.add(ix, T.Tower.neg(ix)), dx},
        T.Ext{T.Tower.zero(rx), T.Tower.zero(ix), dx}, c1, c2)
    case T.Bad{}:
      {==}
    case T.Fuel{}:
      {==}

def T.Tower.neg_add(x, y, hx, hy, px, py, h):
  match x y:
    case T.Base{a} T.Base{b}:
      T.PosBase{+pa} = px
      T.PosBase{+pb} = py
      Equal.cong(R.Rat, T.Tower, u => T.Base{u},
        R.Rat.neg(R.Rat.add(a, b)), R.Rat.add(R.Rat.neg(a), R.Rat.neg(b)),
        RH.Rat.neg_add.arb(a, b, pa, pb))
    case T.Base{a} T.Ext{ry, iy, dy}:
      {==}
    case T.Base{a} T.Bad{}:
      {==}
    case T.Base{a} T.Fuel{}:
      {==}
    case T.Ext{rx, ix, dx} T.Base{b}:
      {==}
    case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
      T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
      T.CleanExt{+hyr, +hyi, +hyd, +hyri, +hyrd} = hy
      T.PosExt{+prer, +pimr, +pradr} = px
      T.PosExt{+prey, +pimy, +prady} = py
      +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)
      +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
              Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
              Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                er, hyri))
      +c1 = Equal.cong(T.Tower, T.Tower,
              u => T.Ext{u, T.Tower.neg(T.Tower.add(ix, iy)), dx},
              T.Tower.neg(T.Tower.add(rx, ry)),
              T.Tower.add(T.Tower.neg(rx), T.Tower.neg(ry)),
              T.Tower.neg_add(rx, ry, hxr, hyr, prer, prey, er))
      +c2 = Equal.cong(T.Tower, T.Tower,
              u => T.Ext{T.Tower.add(T.Tower.neg(rx), T.Tower.neg(ry)), u, dx},
              T.Tower.neg(T.Tower.add(ix, iy)),
              T.Tower.add(T.Tower.neg(ix), T.Tower.neg(iy)),
              T.Tower.neg_add(ix, iy, hxi, hyi, pimr, pimy, ei))
      Equal.trans(T.Tower,
        T.Ext{T.Tower.neg(T.Tower.add(rx, ry)), T.Tower.neg(T.Tower.add(ix, iy)), dx},
        T.Ext{T.Tower.add(T.Tower.neg(rx), T.Tower.neg(ry)), T.Tower.neg(T.Tower.add(ix, iy)), dx},
        T.Ext{T.Tower.add(T.Tower.neg(rx), T.Tower.neg(ry)), T.Tower.add(T.Tower.neg(ix), T.Tower.neg(iy)), dx},
        c1, c2)
    case T.Ext{rx, ix, dx} T.Bad{}:
      {==}
    case T.Ext{rx, ix, dx} T.Fuel{}:
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

# ---------------------------------------------------------------------------
# Tower.neg_pair (round sixty-three): mul_neg and neg_mul are one induction
# ---------------------------------------------------------------------------
# One coordinate of the pair law, four times over: rewrite each summand to its
# negated form, then distribute -- which is Tower.neg_add read backwards. A proof
# helper, not a law: it adds nothing to the law surface.
def Tower.neg_coord(+t1: T.Tower, +u1: T.Tower, +t2: T.Tower, +u2: T.Tower,
    e1: {t1 == T.Tower.neg(u1) : T.Tower},
    e2: {t2 == T.Tower.neg(u2) : T.Tower},
    c1: T.Tower.clean(u1), c2: T.Tower.clean(u2),
    p1: T.Tower.pos(u1), p2: T.Tower.pos(u2),
    hd: {T.Tower.depth(u1) == T.Tower.depth(u2) : Nat}) ->
    {T.Tower.add(t1, t2) == T.Tower.neg(T.Tower.add(u1, u2)) : T.Tower}:
  Equal.trans(T.Tower,
    T.Tower.add(t1, t2),
    T.Tower.add(T.Tower.neg(u1), t2),
    T.Tower.neg(T.Tower.add(u1, u2)),
    Equal.cong(T.Tower, T.Tower, u => T.Tower.add(u, t2), t1, T.Tower.neg(u1), e1),
    Equal.trans(T.Tower,
      T.Tower.add(T.Tower.neg(u1), t2),
      T.Tower.add(T.Tower.neg(u1), T.Tower.neg(u2)),
      T.Tower.neg(T.Tower.add(u1, u2)),
      Equal.cong(T.Tower, T.Tower, u => T.Tower.add(T.Tower.neg(u1), u), t2,
        T.Tower.neg(u2), e2),
      Equal.sym(T.Tower, T.Tower.neg(T.Tower.add(u1, u2)),
        T.Tower.add(T.Tower.neg(u1), T.Tower.neg(u2)),
        T.Tower.neg_add(u1, u2, c1, c2, p1, p2, hd))))

# The pair induction. Fuel first, then shapes; only Base/Base and Ext/Ext are
# inhabited, every other arm contradicting either hf (fuel 0n), one operand's
# cleanliness evidence (a marker is Empty) or the depth equation (a Base and an
# Ext cannot sit at one level). The prelude of the Ext/Ext arm is mul.safe's: the
# same five sub-products, each with its own cleanliness, level and sufficiency
# equation. What is new is what the five pairs buy -- each returns both halves of
# this law at its coordinates, and each half's radicand coordinate then uses the
# *other* half at the pair (mul(g, ix, iy), dx), which is why the pair is stated
# at all: mul(f, x, neg y)'s radicand coordinate is
# mul(g, mul(g, ix, neg iy), dx), one congruence away from
# mul(g, neg(mul(g, ix, iy)), dx) and hence from neg(mul(g, mul(g, ix, iy), dx))
# only through neg_mul at that pair.
def TH.Tower.neg_pair(f, x, y, hx, hy, px, py, h, hf):
  match f:
    case 0n:
      Empty.absurd(TH.Tower.NegPair<f, x, y>,
        NH.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n), 0n,
          Nat.add(1n, T.Tower.depth(x)), hf)))
    case 1n+g:
      match x y:
        case T.Base{a} T.Base{b}:
          T.PosBase{+pa} = px
          T.PosBase{+pb} = py
          TH.NegBoth{
            Equal.cong(R.Rat, T.Tower, u => T.Base{u},
              R.Rat.mul(a, R.Rat.neg(b)), R.Rat.neg(R.Rat.mul(a, b)),
              R.Rat.mul_neg(a, b, pa, pb)),
            Equal.cong(R.Rat, T.Tower, u => T.Base{u},
              R.Rat.mul(R.Rat.neg(a), b), R.Rat.neg(R.Rat.mul(a, b)),
              R.Rat.neg_mul(a, b, pa, pb))}
        case T.Ext{rx, ix, dx} T.Ext{ry, iy, dy}:
          T.CleanExt{+hxr, +hxi, +hxd, +hxri, +hxrd} = hx
          T.CleanExt{+hyr, +hyi, +hyd, +hyri, +hyrd} = hy
          T.PosExt{+prer, +pimr, +pradr} = px
          T.PosExt{+prey, +pimy, +prady} = py
          +er = N.succ_inj(T.Tower.depth(rx), T.Tower.depth(ry), h)
          +ei = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx), T.Tower.depth(iy),
                  Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri),
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry), T.Tower.depth(iy),
                    er, hyri))
          +ef = Equal.trans(Nat, Nat.add(1n, g), f,
                  Nat.add(1n, Nat.add(1n, T.Tower.depth(rx))), {==},
                  Equal.trans(Nat, f, Nat.add(1n, T.Tower.depth(x)),
                    Nat.add(1n, Nat.add(1n, T.Tower.depth(rx))), hf, {==}))
          +hf1 = N.succ_inj(g, Nat.add(1n, T.Tower.depth(rx)), ef)
          +hf2 = Equal.trans(Nat, g, Nat.add(1n, T.Tower.depth(rx)),
                  Nat.add(1n, T.Tower.depth(ix)), hf1,
                  Equal.cong(Nat, Nat, u => Nat.add(1n, u),
                    T.Tower.depth(rx), T.Tower.depth(ix), hxri))
          # the five recursive pairs, with the cleanliness, level and pos facts
          # the coordinate proofs need
          +p1 = TH.Tower.neg_pair(g, rx, ry, hxr, hyr, prer, prey, er, hf1)
          +cs1 = TH.Tower.safe.clean(g, rx, ry,
                  TH.Tower.mul.safe(g, rx, ry, hxr, hyr, er, hf1))
          +hd1 = TH.Tower.safe.depth(g, rx, ry,
                  TH.Tower.mul.safe(g, rx, ry, hxr, hyr, er, hf1))
          +cp1 = TH.Tower.pos.mul(g, rx, ry, prer, prey)
          +p2i = TH.Tower.neg_pair(g, ix, iy, hxi, hyi, pimr, pimy, ei, hf2)
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
          +cp2 = TH.Tower.pos.mul(g, ix, iy, pimr, pimy)
          +cp2d = TH.Tower.pos.mul(g, T.Tower.mul(g, ix, iy), dx, cp2, pradr)
          +p2 = TH.Tower.neg_pair(g, T.Tower.mul(g, ix, iy), dx, cs2i, hxd, cp2, pradr,
                  e2, hf3)
          +cs2 = TH.Tower.safe.clean(g, T.Tower.mul(g, ix, iy), dx,
                  TH.Tower.mul.safe(g, T.Tower.mul(g, ix, iy), dx, cs2i, hxd, e2, hf3))
          +hd2 = TH.Tower.safe.depth(g, T.Tower.mul(g, ix, iy), dx,
                  TH.Tower.mul.safe(g, T.Tower.mul(g, ix, iy), dx, cs2i, hxd, e2, hf3))
          +e3 = Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ry),
                  T.Tower.depth(iy), er, hyri)
          +p3 = TH.Tower.neg_pair(g, rx, iy, hxr, hyi, prer, pimy, e3, hf1)
          +cs3 = TH.Tower.safe.clean(g, rx, iy,
                  TH.Tower.mul.safe(g, rx, iy, hxr, hyi, e3, hf1))
          +hd3 = TH.Tower.safe.depth(g, rx, iy,
                  TH.Tower.mul.safe(g, rx, iy, hxr, hyi, e3, hf1))
          +cp3 = TH.Tower.pos.mul(g, rx, iy, prer, pimy)
          +e4 = Equal.trans(Nat, T.Tower.depth(ix), T.Tower.depth(rx),
                  T.Tower.depth(ry),
                  Equal.sym(Nat, T.Tower.depth(rx), T.Tower.depth(ix), hxri), er)
          +p4 = TH.Tower.neg_pair(g, ix, ry, hxi, hyr, pimr, prey, e4, hf2)
          +cs4 = TH.Tower.safe.clean(g, ix, ry,
                  TH.Tower.mul.safe(g, ix, ry, hxi, hyr, e4, hf2))
          +hd4 = TH.Tower.safe.depth(g, ix, ry,
                  TH.Tower.mul.safe(g, ix, ry, hxi, hyr, e4, hf2))
          +cp4 = TH.Tower.pos.mul(g, ix, ry, pimr, prey)
          # the re coordinate pairs (mul(g,rx,ry)) with (mul(g,mul(g,ix,iy),dx)),
          # the im coordinate pairs the two cross products
          +eA = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(rx),
                  T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)), hd1,
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ix),
                    T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)), hxri,
                    Equal.trans(Nat, T.Tower.depth(ix),
                      T.Tower.depth(T.Tower.mul(g, ix, iy)),
                      T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                      Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)),
                        T.Tower.depth(ix), hd2i),
                      Equal.sym(Nat,
                        T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                        T.Tower.depth(T.Tower.mul(g, ix, iy)), hd2))))
          +eB = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, iy)), T.Tower.depth(rx),
                  T.Tower.depth(T.Tower.mul(g, ix, ry)), hd3,
                  Equal.trans(Nat, T.Tower.depth(rx), T.Tower.depth(ix),
                    T.Tower.depth(T.Tower.mul(g, ix, ry)), hxri,
                    Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, ry)),
                      T.Tower.depth(ix), hd4)))
          # mneg: the re coordinate rewrites the first summand and the radicand
          # one, the im coordinate the two cross products
          +ea1 = TH.Tower.negpair.mneg(g, rx, ry, p1)
          +ea2i = TH.Tower.negpair.mneg(g, ix, iy, p2i)
          +ea2t = Equal.trans(T.Tower,
                    T.Tower.mul(g, T.Tower.mul(g, ix, T.Tower.neg(iy)), dx),
                    T.Tower.mul(g, T.Tower.neg(T.Tower.mul(g, ix, iy)), dx),
                    T.Tower.neg(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                    Equal.cong(T.Tower, T.Tower, u => T.Tower.mul(g, u, dx),
                      T.Tower.mul(g, ix, T.Tower.neg(iy)),
                      T.Tower.neg(T.Tower.mul(g, ix, iy)), ea2i),
                    TH.Tower.negpair.nmul(g, T.Tower.mul(g, ix, iy), dx, p2))
          +emre = Tower.neg_coord(
                    T.Tower.mul(g, rx, T.Tower.neg(ry)), T.Tower.mul(g, rx, ry),
                    T.Tower.mul(g, T.Tower.mul(g, ix, T.Tower.neg(iy)), dx),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx),
                    ea1, ea2t, cs1, cs2, cp1, cp2d, eA)
          +emim = Tower.neg_coord(
                    T.Tower.mul(g, rx, T.Tower.neg(iy)), T.Tower.mul(g, rx, iy),
                    T.Tower.mul(g, ix, T.Tower.neg(ry)), T.Tower.mul(g, ix, ry),
                    TH.Tower.negpair.mneg(g, rx, iy, p3),
                    TH.Tower.negpair.mneg(g, ix, ry, p4),
                    cs3, cs4, cp3, cp4, eB)
          # nmul: the same, with the negation on the first argument
          +enre = Tower.neg_coord(
                    T.Tower.mul(g, T.Tower.neg(rx), ry), T.Tower.mul(g, rx, ry),
                    T.Tower.mul(g, T.Tower.mul(g, T.Tower.neg(ix), iy), dx),
                    T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx),
                    TH.Tower.negpair.nmul(g, rx, ry, p1),
                    Equal.trans(T.Tower,
                      T.Tower.mul(g, T.Tower.mul(g, T.Tower.neg(ix), iy), dx),
                      T.Tower.mul(g, T.Tower.neg(T.Tower.mul(g, ix, iy)), dx),
                      T.Tower.neg(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
                      Equal.cong(T.Tower, T.Tower, u => T.Tower.mul(g, u, dx),
                        T.Tower.mul(g, T.Tower.neg(ix), iy),
                        T.Tower.neg(T.Tower.mul(g, ix, iy)),
                        TH.Tower.negpair.nmul(g, ix, iy, p2i)),
                      TH.Tower.negpair.nmul(g, T.Tower.mul(g, ix, iy), dx, p2)),
                    cs1, cs2, cp1, cp2d, eA)
          +enim = Tower.neg_coord(
                    T.Tower.mul(g, T.Tower.neg(rx), iy), T.Tower.mul(g, rx, iy),
                    T.Tower.mul(g, T.Tower.neg(ix), ry), T.Tower.mul(g, ix, ry),
                    TH.Tower.negpair.nmul(g, rx, iy, p3),
                    TH.Tower.negpair.nmul(g, ix, ry, p4),
                    cs3, cs4, cp3, cp4, eB)
          # each field is two congruence steps: the coordinates are independent,
          # so the re step holds the im coordinate and the im step holds the re
          # coordinate -- at the value the previous step left it.
          +em = Equal.trans(T.Tower,
                  T.Ext{T.Tower.add(T.Tower.mul(g, rx, T.Tower.neg(ry)),
                        T.Tower.mul(g, T.Tower.mul(g, ix, T.Tower.neg(iy)), dx)),
                    T.Tower.add(T.Tower.mul(g, rx, T.Tower.neg(iy)),
                      T.Tower.mul(g, ix, T.Tower.neg(ry))), dx},
                  T.Ext{T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                        T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                    T.Tower.add(T.Tower.mul(g, rx, T.Tower.neg(iy)),
                      T.Tower.mul(g, ix, T.Tower.neg(ry))), dx},
                  T.Ext{T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                        T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                    T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry))), dx},
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Ext{u, T.Tower.add(T.Tower.mul(g, rx, T.Tower.neg(iy)),
                             T.Tower.mul(g, ix, T.Tower.neg(ry))), dx},
                    T.Tower.add(T.Tower.mul(g, rx, T.Tower.neg(ry)),
                      T.Tower.mul(g, T.Tower.mul(g, ix, T.Tower.neg(iy)), dx)),
                    T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                      T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))), emre),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Ext{T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                             T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))), u, dx},
                    T.Tower.add(T.Tower.mul(g, rx, T.Tower.neg(iy)),
                      T.Tower.mul(g, ix, T.Tower.neg(ry))),
                    T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry))), emim))
          +en = Equal.trans(T.Tower,
                  T.Ext{T.Tower.add(T.Tower.mul(g, T.Tower.neg(rx), ry),
                        T.Tower.mul(g, T.Tower.mul(g, T.Tower.neg(ix), iy), dx)),
                    T.Tower.add(T.Tower.mul(g, T.Tower.neg(rx), iy),
                      T.Tower.mul(g, T.Tower.neg(ix), ry)), dx},
                  T.Ext{T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                        T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                    T.Tower.add(T.Tower.mul(g, T.Tower.neg(rx), iy),
                      T.Tower.mul(g, T.Tower.neg(ix), ry)), dx},
                  T.Ext{T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                        T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
                    T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry))), dx},
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Ext{u, T.Tower.add(T.Tower.mul(g, T.Tower.neg(rx), iy),
                             T.Tower.mul(g, T.Tower.neg(ix), ry)), dx},
                    T.Tower.add(T.Tower.mul(g, T.Tower.neg(rx), ry),
                      T.Tower.mul(g, T.Tower.mul(g, T.Tower.neg(ix), iy), dx)),
                    T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                      T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))), enre),
                  Equal.cong(T.Tower, T.Tower,
                    u => T.Ext{T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, ry),
                             T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))), u, dx},
                    T.Tower.add(T.Tower.mul(g, T.Tower.neg(rx), iy),
                      T.Tower.mul(g, T.Tower.neg(ix), ry)),
                    T.Tower.neg(T.Tower.add(T.Tower.mul(g, rx, iy),
                      T.Tower.mul(g, ix, ry))), enim))
          TH.NegBoth{em, en}
        case T.Base{a} T.Ext{ry, iy, dy}:
          Empty.absurd(TH.Tower.NegPair<f, T.Base{a}, T.Ext{ry, iy, dy}>,
            NH.eq_ne_gt(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
              0n, Nat.add(1n, T.Tower.depth(ry)), h)))
        case T.Ext{rx, ix, dx} T.Base{b}:
          Empty.absurd(TH.Tower.NegPair<f, T.Ext{rx, ix, dx}, T.Base{b}>,
            NH.gt_ne_eq(Equal.cong(Nat, Cmp, u => Nat.cmp(u, 0n),
              Nat.add(1n, T.Tower.depth(rx)), 0n, h)))
        case T.Bad{} _:
          Empty.absurd(TH.Tower.NegPair<f, T.Bad{}, y>, hx)
        case T.Fuel{} _:
          Empty.absurd(TH.Tower.NegPair<f, T.Fuel{}, y>, hx)
        case _ T.Bad{}:
          Empty.absurd(TH.Tower.NegPair<f, x, T.Bad{}>, hy)
        case _ T.Fuel{}:
          Empty.absurd(TH.Tower.NegPair<f, x, T.Fuel{}>, hy)

# The two readable laws are projections of the pair, one call each.
def T.Tower.mul_neg(f, x, y, hx, hy, px, py, h, hf):
  TH.Tower.negpair.mneg(f, x, y, TH.Tower.neg_pair(f, x, y, hx, hy, px, py, h, hf))

def T.Tower.neg_mul(f, x, y, hx, hy, px, py, h, hf):
  TH.Tower.negpair.nmul(f, x, y, TH.Tower.neg_pair(f, x, y, hx, hy, px, py, h, hf))

# add_zero: the Base arm is Rat.add_zero handed the canon witness's fx, with the
# value first rewritten to the spelling the Rat law is stated at; the congruence
# carries the result back up to Tower. The Ext arm recurses coordinatewise -- zero
# is defined that way -- and the markers are definitional.
def T.Tower.add_zero(x, cx):
  match x:
    case T.Base{a}:
      match cx:
        case T.CanonBase{+ce, +cfx}:
          %Equal.sym(R.Rat, a, R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, ce) : {T.Base{R.Rat.add(_, R.Rat.zero())} == T.Base{a} : T.Tower}
          %Equal.sym(R.Rat, a, R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, ce) : {T.Base{R.Rat.add(R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, R.Rat.zero())} == T.Base{_} : T.Tower}
          Equal.cong(R.Rat, T.Tower, u => T.Base{u},
            R.Rat.add(R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, R.Rat.zero()),
            R.Rat{R.Rat.numof(a), R.Rat.denof(a)},
            R.Rat.add_zero(R.Rat.numof(a), R.Rat.denof(a),
              Equal.trans(R.Rat, R.Rat.mk(R.Rat.numof(a), R.Rat.denof(a)), a,
                R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, cfx, ce)))
    case T.Ext{rx, ix, dx}:
      match cx:
        case T.CanonExt{+cre, +cim, +cd, +lri, +lrd}:
          +e1 = T.Tower.add_zero(rx, cre)
          +e2 = T.Tower.add_zero(ix, cim)
          +c1 = Equal.cong(T.Tower, T.Tower,
                  u => T.Ext{u, T.Tower.add(ix, T.Tower.zero(ix)), dx},
                  T.Tower.add(rx, T.Tower.zero(rx)), rx, e1)
          +c2 = Equal.cong(T.Tower, T.Tower,
                  u => T.Ext{rx, u, dx},
                  T.Tower.add(ix, T.Tower.zero(ix)), ix, e2)
          Equal.trans(T.Tower,
            T.Ext{T.Tower.add(rx, T.Tower.zero(rx)),
                  T.Tower.add(ix, T.Tower.zero(ix)), dx},
            T.Ext{rx, T.Tower.add(ix, T.Tower.zero(ix)), dx},
            T.Ext{rx, ix, dx}, c1, c2)
    case T.Bad{}:
      {==}
    case T.Fuel{}:
      {==}

# zero_add: the same canonical shape as add_zero, with zero(x) in the first slot.
# Both occurrences of a are rewritten for the same two reasons -- the Rat law is
# stated at the spelled value, and Rat.add cannot unfold while an operand is a
# variable.
def T.Tower.zero_add(x, cx):
  match x:
    case T.Base{a}:
      match cx:
        case T.CanonBase{+ce, +cfx}:
          %Equal.sym(R.Rat, a, R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, ce) : {T.Base{R.Rat.add(R.Rat.zero(), _)} == T.Base{a} : T.Tower}
          %Equal.sym(R.Rat, a, R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, ce) : {T.Base{R.Rat.add(R.Rat.zero(), R.Rat{R.Rat.numof(a), R.Rat.denof(a)})} == T.Base{_} : T.Tower}
          Equal.cong(R.Rat, T.Tower, u => T.Base{u},
            R.Rat.add(R.Rat.zero(), R.Rat{R.Rat.numof(a), R.Rat.denof(a)}),
            R.Rat{R.Rat.numof(a), R.Rat.denof(a)},
            R.Rat.zero_add(R.Rat.numof(a), R.Rat.denof(a),
              Equal.trans(R.Rat, R.Rat.mk(R.Rat.numof(a), R.Rat.denof(a)), a,
                R.Rat{R.Rat.numof(a), R.Rat.denof(a)}, cfx, ce)))
    case T.Ext{rx, ix, dx}:
      match cx:
        case T.CanonExt{+cre, +cim, +cd, +lri, +lrd}:
          +e1 = T.Tower.zero_add(rx, cre)
          +e2 = T.Tower.zero_add(ix, cim)
          +c1 = Equal.cong(T.Tower, T.Tower,
                  u => T.Ext{u, T.Tower.add(T.Tower.zero(ix), ix), dx},
                  T.Tower.add(T.Tower.zero(rx), rx), rx, e1)
          +c2 = Equal.cong(T.Tower, T.Tower,
                  u => T.Ext{rx, u, dx},
                  T.Tower.add(T.Tower.zero(ix), ix), ix, e2)
          Equal.trans(T.Tower,
            T.Ext{T.Tower.add(T.Tower.zero(rx), rx),
                  T.Tower.add(T.Tower.zero(ix), ix), dx},
            T.Ext{rx, T.Tower.add(T.Tower.zero(ix), ix), dx},
            T.Ext{rx, ix, dx}, c1, c2)
    case T.Bad{}:
      {==}
    case T.Fuel{}:
      {==}

# zero.level is a shape induction with nothing to compute: the two sides reduce as soon
# as both shapes are spelled, and the Ext arm rebuilds from the witness's own fields.
def TH.Tower.zero.level(u, v, h):
  match u v:
    case T.Base{a} T.Base{b}:
      {==}
    case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
      match h:
        case T.LevelExt{+lre, +lim, +ld}:
          +e1 = TH.Tower.zero.level(ru, rv, lre)
          +e2 = TH.Tower.zero.level(iu, iv, lim)
          +eA = Equal.cong(T.Tower, T.Tower, w => T.Ext{w, T.Tower.zero(iu), du},
            T.Tower.zero(ru), T.Tower.zero(rv), e1)
          +eB = Equal.cong(T.Tower, T.Tower, w => T.Ext{T.Tower.zero(rv), w, du},
            T.Tower.zero(iu), T.Tower.zero(iv), e2)
          +eC = Equal.cong(T.Tower, T.Tower,
            w => T.Ext{T.Tower.zero(rv), T.Tower.zero(iv), w}, du, dv, ld)
          Equal.trans(T.Tower,
            T.Ext{T.Tower.zero(ru), T.Tower.zero(iu), du},
            T.Ext{T.Tower.zero(rv), T.Tower.zero(iu), du},
            T.Ext{T.Tower.zero(rv), T.Tower.zero(iv), dv},
            eA,
            Equal.trans(T.Tower,
              T.Ext{T.Tower.zero(rv), T.Tower.zero(iu), du},
              T.Ext{T.Tower.zero(rv), T.Tower.zero(iv), du},
              T.Ext{T.Tower.zero(rv), T.Tower.zero(iv), dv},
              eB, eC))
    case T.Bad{} T.Bad{}:
      {==}
    case T.Fuel{} T.Fuel{}:
      {==}
    case T.Base{a} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Base{a} T.Bad{}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Base{a} T.Fuel{}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Ext{ru, iu, du} T.Base{b}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Ext{ru, iu, du} T.Bad{}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Ext{ru, iu, du} T.Fuel{}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Bad{} T.Base{b}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Bad{} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Bad{} T.Fuel{}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Fuel{} T.Base{b}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Fuel{} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)
    case T.Fuel{} T.Bad{}:
      Empty.absurd({T.Tower.zero(u) == T.Tower.zero(v) : T.Tower}, h)

def TH.Tower.add.zero(u, v, h):
  match u v:
    case T.Base{a} T.Base{b}:
      {==}
    case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
      match h:
        case T.LevelExt{+lre, +lim, +ld}:
          +e1 = TH.Tower.add.zero(ru, rv, lre)
          +e2 = TH.Tower.add.zero(iu, iv, lim)
          +eA = Equal.cong(T.Tower, T.Tower, w => T.Ext{w, T.Tower.add(T.Tower.zero(iu), T.Tower.zero(iv)), du},
            T.Tower.add(T.Tower.zero(ru), T.Tower.zero(rv)),
            T.Tower.zero(ru), e1)
          +eB = Equal.cong(T.Tower, T.Tower, w => T.Ext{T.Tower.zero(ru), w, du},
            T.Tower.add(T.Tower.zero(iu), T.Tower.zero(iv)),
            T.Tower.zero(iu), e2)
          Equal.trans(T.Tower,
            T.Ext{T.Tower.add(T.Tower.zero(ru), T.Tower.zero(rv)),
                  T.Tower.add(T.Tower.zero(iu), T.Tower.zero(iv)), du},
            T.Ext{T.Tower.zero(ru), T.Tower.add(T.Tower.zero(iu), T.Tower.zero(iv)), du},
            T.Ext{T.Tower.zero(ru), T.Tower.zero(iu), du},
            eA, eB)
    case T.Bad{} T.Bad{}:
      {==}
    case T.Fuel{} T.Fuel{}:
      {==}
    case T.Base{a} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Base{a} T.Bad{}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Base{a} T.Fuel{}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Ext{ru, iu, du} T.Base{b}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Ext{ru, iu, du} T.Bad{}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Ext{ru, iu, du} T.Fuel{}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Bad{} T.Base{b}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Bad{} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Bad{} T.Fuel{}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Fuel{} T.Base{b}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Fuel{} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)
    case T.Fuel{} T.Bad{}:
      Empty.absurd({T.Tower.add(T.Tower.zero(u), T.Tower.zero(v)) == T.Tower.zero(u) : T.Tower}, h)

def TH.Tower.level.depth(u, v, h):
  match u v:
    case T.Base{a} T.Base{b}:
      {==}
    case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
      match h:
        case T.LevelExt{+lre, +lim, +ld}:
          Equal.cong(Nat, Nat, w => Nat.add(1n, w),
            T.Tower.depth(ru), T.Tower.depth(rv),
            TH.Tower.level.depth(ru, rv, lre))
    case T.Bad{} T.Bad{}:
      {==}
    case T.Fuel{} T.Fuel{}:
      {==}
    case T.Base{a} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Base{a} T.Bad{}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Base{a} T.Fuel{}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Ext{ru, iu, du} T.Base{b}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Ext{ru, iu, du} T.Bad{}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Ext{ru, iu, du} T.Fuel{}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Bad{} T.Base{b}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Bad{} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Bad{} T.Fuel{}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Fuel{} T.Base{b}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Fuel{} T.Ext{rv, iv, dv}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)
    case T.Fuel{} T.Bad{}:
      Empty.absurd({T.Tower.depth(u) == T.Tower.depth(v) : Nat}, h)

def TH.Tower.zero.mul(f, u, v, cu, cv, pu, pv, h, hf):
  match f:
    case 0n:
      Empty.absurd({T.Tower.mul(0n, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower},
        NH.gt_ne_eq(Equal.cong(Nat, Cmp, w => Nat.cmp(w, 0n),
          Nat.add(1n, T.Tower.depth(u)), 0n,
          Equal.sym(Nat, 0n, Nat.add(1n, T.Tower.depth(u)), hf))))
    case 1n+g:
      match u v:
        case T.Base{a} T.Base{b}:
          T.PosBase{pden} = pv
          Equal.cong(R.Rat, T.Tower, w => T.Base{w},
            R.Rat.mul(R.Rat.zero(), b), R.Rat.zero(), R.Rat.zero_mul(b, pden))
        case T.Ext{ru, iu, du} T.Ext{rv, iv, dv}:
          # Evidence is taken apart by binding destructuring, not by match: `match cu cv` is
          # refused on the indexed families. The fuel is derived at the spelled coordinate
          # and not as depth(u): reading u as a term consumes it, and u is the index of
          # cu, pu and h, so the destructuring below then reads a consumed binder.
          T.CanonExt{+cre, +cim, +cd, +lri, +lrd} = cu
          T.CanonExt{+crev, +cimv, +cdv, +lriv, +lrdv} = cv
          T.PosExt{+pre, +pim, +prad} = pu
          T.PosExt{+prev, +piv, +pradv} = pv
          T.LevelExt{+lre, +lim, +ld} = h
          +hfg = N.succ_inj(g, Nat.add(1n, T.Tower.depth(ru)), hf)
          +hfg2 = hfg
          +hlidu = TH.Tower.level.trans(iu, rv, du,
            TH.Tower.level.trans(iu, iv, rv, lim, TH.Tower.level.sym(rv, iv, lriv)),
            TH.Tower.level.trans(rv, ru, du, TH.Tower.level.sym(ru, rv, lre), lrd))
          +hlriv = TH.Tower.level.trans(ru, rv, iv, lre, lriv)
          +hlirv = TH.Tower.level.trans(iu, iv, rv, lim,
            TH.Tower.level.sym(rv, iv, lriv))
          +hfi = Equal.trans(Nat, g, Nat.add(1n, T.Tower.depth(ru)),
            Nat.add(1n, T.Tower.depth(iu)), hfg,
            Equal.cong(Nat, Nat, w => Nat.add(1n, w),
              T.Tower.depth(ru), T.Tower.depth(iu),
              TH.Tower.level.depth(ru, iu, lri)))
          +i1 = TH.Tower.zero.mul(g, ru, rv, cre, crev, pre, prev, lre, hfg2)
          +i2 = TH.Tower.zero.mul(g, iu, iv, cim, cimv, pim, piv, lim, hfi)
          +ig = Equal.cong(T.Tower, T.Tower, w => T.Tower.mul(g, w, du),
            T.Tower.mul(g, T.Tower.zero(iu), iv), T.Tower.zero(iu), i2)
          +i3 = TH.Tower.zero.mul(g, iu, du, cim, cd, pim, prad, hlidu, hfi)
          +i4 = TH.Tower.zero.mul(g, ru, iv, cre, cimv, pre, piv, hlriv, hfg2)
          +i5 = TH.Tower.zero.mul(g, iu, rv, cim, crev, pim, prev, hlirv, hfi)
          +az = TH.Tower.add.zero(ru, iu, lri)
          +zl = TH.Tower.zero.level(ru, iu, lri)
          +c1a = Equal.cong(T.Tower, T.Tower,
            w => T.Tower.add(w, T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du)),
            T.Tower.mul(g, T.Tower.zero(ru), rv), T.Tower.zero(ru), i1)
          +c1b = Equal.cong(T.Tower, T.Tower, w => T.Tower.add(T.Tower.zero(ru), w),
            T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du),
            T.Tower.mul(g, T.Tower.zero(iu), du), ig)
          +c1c = Equal.cong(T.Tower, T.Tower, w => T.Tower.add(T.Tower.zero(ru), w),
            T.Tower.mul(g, T.Tower.zero(iu), du), T.Tower.zero(iu), i3)
          +c1 = Equal.trans(T.Tower, T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), rv), T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du)),
            T.Tower.add(T.Tower.zero(ru), T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du)),
            T.Tower.zero(ru), c1a,
            Equal.trans(T.Tower,
              T.Tower.add(T.Tower.zero(ru), T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du)),
              T.Tower.add(T.Tower.zero(ru), T.Tower.mul(g, T.Tower.zero(iu), du)),
              T.Tower.zero(ru), c1b,
              Equal.trans(T.Tower,
                T.Tower.add(T.Tower.zero(ru), T.Tower.mul(g, T.Tower.zero(iu), du)),
                T.Tower.add(T.Tower.zero(ru), T.Tower.zero(iu)),
                T.Tower.zero(ru), c1c, az)))
          +c2a = Equal.cong(T.Tower, T.Tower,
            w => T.Tower.add(w, T.Tower.mul(g, T.Tower.zero(iu), rv)),
            T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.zero(ru), i4)
          +c2b = Equal.cong(T.Tower, T.Tower, w => T.Tower.add(T.Tower.zero(ru), w),
            T.Tower.mul(g, T.Tower.zero(iu), rv), T.Tower.zero(iu), i5)
          +c2 = Equal.trans(T.Tower, T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.mul(g, T.Tower.zero(iu), rv)),
            T.Tower.add(T.Tower.zero(ru), T.Tower.mul(g, T.Tower.zero(iu), rv)),
            T.Tower.zero(ru), c2a,
            Equal.trans(T.Tower,
              T.Tower.add(T.Tower.zero(ru), T.Tower.mul(g, T.Tower.zero(iu), rv)),
              T.Tower.add(T.Tower.zero(ru), T.Tower.zero(iu)),
              T.Tower.zero(ru), c2b, az))
          +eA = Equal.cong(T.Tower, T.Tower, w => T.Ext{w, T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.mul(g, T.Tower.zero(iu), rv)), du}, T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), rv), T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du)), T.Tower.zero(ru), c1)
          +eB = Equal.cong(T.Tower, T.Tower,
            w => T.Ext{T.Tower.zero(ru), w, du}, T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.mul(g, T.Tower.zero(iu), rv)), T.Tower.zero(ru), c2)
          +eC = Equal.cong(T.Tower, T.Tower,
            w => T.Ext{T.Tower.zero(ru), w, du},
            T.Tower.zero(ru), T.Tower.zero(iu), zl)
          Equal.trans(T.Tower,
            T.Ext{T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), rv), T.Tower.mul(g, T.Tower.mul(g, T.Tower.zero(iu), iv), du)), T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.mul(g, T.Tower.zero(iu), rv)), du},
            T.Ext{T.Tower.zero(ru), T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.mul(g, T.Tower.zero(iu), rv)), du},
            T.Ext{T.Tower.zero(ru), T.Tower.zero(iu), du},
            eA,
            Equal.trans(T.Tower,
              T.Ext{T.Tower.zero(ru), T.Tower.add(T.Tower.mul(g, T.Tower.zero(ru), iv), T.Tower.mul(g, T.Tower.zero(iu), rv)), du},
              T.Ext{T.Tower.zero(ru), T.Tower.zero(ru), du},
              T.Ext{T.Tower.zero(ru), T.Tower.zero(iu), du}, eB, eC))
        case T.Bad{} T.Bad{}:
          {==}
        case T.Fuel{} T.Fuel{}:
          {==}
        case T.Base{a} T.Ext{rv, iv, dv}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Base{a} T.Bad{}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Base{a} T.Fuel{}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Ext{ru, iu, du} T.Base{b}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Ext{ru, iu, du} T.Bad{}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Ext{ru, iu, du} T.Fuel{}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Bad{} T.Base{b}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Bad{} T.Ext{rv, iv, dv}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Bad{} T.Fuel{}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Fuel{} T.Base{b}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Fuel{} T.Ext{rv, iv, dv}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
        case T.Fuel{} T.Bad{}:
          Empty.absurd({T.Tower.mul(f, T.Tower.zero(u), v) == T.Tower.zero(u) : T.Tower}, h)
