import Base
import ./nat.bend as NL

# Nat proofs
# =========
#
# Fills every law of nat.bend. The discrimination families CmpIsEQ,
# CmpIsGT, NatIsPos and the Nat.pred helper are proof machinery only
# (no law statement mentions them), so they live here.

def NL.add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %NL.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def NL.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.add_succ(ap, b) : {1n+1n+Nat.add(ap, b) == 1n+_ : Nat}
      {==}

def NL.add_comm(a, b):
  match a:
    case 0n:
      %NL.add_zero(b) : {_ == Nat.add(b, 0n) : Nat}
      {==}
    case 1n+ap:
      %NL.add_succ(b, ap) : {1n+Nat.add(ap, b) == _ : Nat}
      %NL.add_comm(ap, b) : {1n+Nat.add(ap, b) == 1n+_ : Nat}
      {==}

def NL.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.add_assoc(ap, b, c) : {1n+Nat.add(Nat.add(ap, b), c) == 1n+_ : Nat}
      {==}

def NL.add_exchange(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.add_succ(b, Nat.add(ap, c)) : {1n+Nat.add(ap, Nat.add(b, c)) == _ : Nat}
      %NL.add_exchange(ap, b, c) : {1n+Nat.add(ap, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def NL.mul_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      NL.mul_zero(p)

def NL.mul_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.mul_succ(ap, b) : {1n+Nat.add(ap, Nat.add(b, Nat.mul(ap, b))) == 1n+Nat.add(b, _) : Nat}
      %NL.add_exchange(ap, b, Nat.mul(ap, b)) : {1n+Nat.add(ap, Nat.add(b, Nat.mul(ap, b))) == 1n+_ : Nat}
      {==}

def NL.mul_one(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.mul_one(ap) : {1n+ap == 1n+_ : Nat}
      {==}

def NL.mul_comm(a, b):
  match a:
    case 0n:
      %NL.mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n+ap:
      %NL.mul_succ(b, ap) : {Nat.add(b, Nat.mul(ap, b)) == _ : Nat}
      %NL.mul_comm(ap, b) : {Nat.add(b, Nat.mul(ap, b)) == Nat.add(b, _) : Nat}
      {==}

# Discrimination predicates: CmpIsEQ(c) is Unit when c is EQ, else Empty.
def CmpIsEQ(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case LT{}:
      Empty
    case GT{}:
      Empty

def CmpIsGT(c: Cmp) -> Type:
  match c:
    case GT{}:
      Unit
    case LT{}:
      Empty
    case EQ{}:
      Empty

def NL.lt_ne_eq(e):
  %Equal.sym(Cmp, LT{}, EQ{}, e) : CmpIsEQ(_)
  Unit{}

def NL.gt_ne_eq(e):
  %Equal.sym(Cmp, GT{}, EQ{}, e) : CmpIsEQ(_)
  Unit{}

def NL.eq_ne_gt(e):
  %Equal.sym(Cmp, EQ{}, GT{}, e) : CmpIsGT(_)
  Unit{}

def NL.lt_ne_gt(e):
  %Equal.sym(Cmp, LT{}, GT{}, e) : CmpIsGT(_)
  Unit{}

def NL.cmp_eq(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, NL.lt_ne_eq(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, NL.gt_ne_eq(e))
    case 1n+ap 1n+bp:
      %NL.cmp_eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def NL.cmp_antisym(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      NL.cmp_antisym(ap, bp)

def NL.cmp_gt_sub_add(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.add(Nat.sub(0n, 0n), 0n) == 0n : Nat}, NL.eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+bp), 1n+bp) == 0n : Nat}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      NL.add_zero(1n+ap)
    case 1n+ap 1n+bp:
      %NL.add_succ(Nat.sub(ap, bp), bp) : {_ == 1n+ap : Nat}
      %NL.cmp_gt_sub_add(ap, bp, e) : {1n+Nat.add(Nat.sub(ap, bp), bp) == 1n+_ : Nat}
      {==}

def NL.add_comm_succ(a, b):
  %NL.add_succ(a, b) : {_ == Nat.add(b, 1n+a) : Nat}
  %NL.add_succ(b, a) : {1n+Nat.add(a, b) == _ : Nat}
  %NL.add_comm(a, b) : {1n+Nat.add(a, b) == 1n+_ : Nat}
  {==}

def NL.add_assoc_rev(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), NL.add_assoc(a, b, c))

def NL.mul_distrib(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.mul_distrib(ap, b, c) : {Nat.add(Nat.add(b, Nat.mul(ap, b)), Nat.add(c, Nat.mul(ap, c))) == Nat.add(Nat.add(b, c), _) : Nat}
      Equal.trans(Nat,
        Nat.add(Nat.add(b, Nat.mul(ap, b)), Nat.add(c, Nat.mul(ap, c))),
        Nat.add(b, Nat.add(Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c)))),
        Nat.add(Nat.add(b, c), Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
        NL.add_assoc(b, Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c))),
        Equal.trans(Nat,
          Nat.add(b, Nat.add(Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c)))),
          Nat.add(b, Nat.add(c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c)))),
          Nat.add(Nat.add(b, c), Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
          Equal.cong(Nat, Nat, x => Nat.add(b, x),
            Nat.add(Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c))),
            Nat.add(c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
            NL.add_exchange(Nat.mul(ap, b), c, Nat.mul(ap, c))),
          Equal.sym(Nat,
            Nat.add(Nat.add(b, c), Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
            Nat.add(b, Nat.add(c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c)))),
            NL.add_assoc(b, c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))))))

def NL.mul_add_left(x, y, z):
  match x:
    case 0n:
      {==}
    case 1n+xp:
      %NL.add_assoc_rev(z, Nat.mul(xp, z), Nat.mul(y, z)) : {_ == Nat.add(z, Nat.mul(Nat.add(xp, y), z)) : Nat}
      %NL.mul_add_left(xp, y, z) : {Nat.add(z, Nat.add(Nat.mul(xp, z), Nat.mul(y, z))) == Nat.add(z, _) : Nat}
      {==}

def NL.mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.mul_add_left(b, Nat.mul(ap, b), c) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(ap, Nat.mul(b, c))) : Nat}
      %NL.mul_assoc(ap, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(ap, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

def NL.sub_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      {==}

def NL.sub_self(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      NL.sub_self(ap)

def NL.add_sub_cancel(a, b):
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, NL.add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      %Equal.sym(Nat, Nat.sub(a, 0n), a, NL.sub_zero(a)) : {_ == a : Nat}
      {==}
    case 1n+bp:
      %NL.add_succ(a, bp) : {Nat.sub(_, 1n+bp) == a : Nat}
      NL.add_sub_cancel(a, bp)

def NL.sub_add(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+cp:
      {==}
    case 0n 1n+bp 0n:
      {==}
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n 0n:
      {==}
    case 1n+ap 0n 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      NL.sub_add(ap, bp, 0n)
    case 1n+ap 1n+bp 1n+cp:
      NL.sub_add(ap, bp, 1n+cp)

def NL.sub_sub_swap(a, b, c):
  %NL.sub_add(c, a, b) : {_ == Nat.sub(Nat.sub(c, b), a) : Nat}
  %NL.sub_add(c, b, a) : {Nat.sub(c, Nat.add(a, b)) == _ : Nat}
  %NL.add_comm(a, b) : {Nat.sub(c, Nat.add(a, b)) == Nat.sub(c, _) : Nat}
  {==}

def NL.eq_ne_lt(e):
  %e : CmpIsEQ(_)
  Unit{}

def NL.gt_ne_lt(e):
  %e : CmpIsGT(_)
  Unit{}

def NL.cmp_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      NL.cmp_refl(ap)

def NL.cmp_lt_add(a, b):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %NL.add_succ(b, ap) : {Nat.cmp(ap, _) == LT{} : Cmp}
      NL.cmp_lt_add(ap, b)

def NL.cmp_gt_add(a, b):
  %Equal.sym(Cmp, Nat.cmp(Nat.add(1n+b, a), a), NL.Cmp.flip(Nat.cmp(a, Nat.add(1n+b, a))), NL.cmp_antisym(Nat.add(1n+b, a), a)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(a, Nat.add(1n+b, a)), LT{}, NL.cmp_lt_add(a, b)) : {NL.Cmp.flip(_) == GT{} : Cmp}
  {==}

def NL.cmp_add_right(a, b, k):
  match a b:
    case 0n 0n:
      NL.cmp_refl(k)
    case 0n 1n+bp:
      NL.cmp_lt_add(k, bp)
    case 1n+ap 0n:
      NL.cmp_gt_add(k, ap)
    case 1n+ap 1n+bp:
      NL.cmp_add_right(ap, bp, k)

def NL.cmp_add_left(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+kp:
      NL.cmp_add_left(kp, a, b)

def NL.cmp_mul_right(a, b, k):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          %Equal.sym(Cmp, Nat.cmp(Nat.add(k, Nat.mul(ap, 1n+k)), Nat.add(k, Nat.mul(bp, 1n+k))), Nat.cmp(Nat.mul(ap, 1n+k), Nat.mul(bp, 1n+k)), NL.cmp_add_left(k, Nat.mul(ap, 1n+k), Nat.mul(bp, 1n+k))) : {_ == Nat.cmp(ap, bp) : Cmp}
          NL.cmp_mul_right(ap, bp, k)

def NL.cmp_gt_succ(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(1n, 0n) == GT{} : Cmp}, NL.eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(1n, 1n+bp) == GT{} : Cmp}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      NL.cmp_gt_succ(ap, bp, e)

def NL.cmp_gt_refl_succ(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      NL.cmp_gt_refl_succ(ap)

def NL.cmp_gt_sub(a, b, c, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.sub(0n, c)) == GT{} : Cmp}, NL.eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(0n, Nat.sub(1n+bp, c)) == GT{} : Cmp}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      match c:
        case 0n:
          {==}
        case 1n+cp:
          {==}
    case 1n+ap 1n+bp:
      match c:
        case 0n:
          e
        case 1n+cp:
          NL.cmp_gt_succ(ap, Nat.sub(bp, cp), NL.cmp_gt_sub(ap, bp, cp, e))

def NL.cmp_lt_sub(x, y, z, e):
  %Equal.sym(Cmp, Nat.cmp(Nat.sub(y, x), z), NL.Cmp.flip(Nat.cmp(z, Nat.sub(y, x))), NL.cmp_antisym(Nat.sub(y, x), z)) : {_ == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(z, Nat.sub(y, x)), GT{}, NL.cmp_gt_sub(z, y, x, e)) : {NL.Cmp.flip(_) == LT{} : Cmp}
  {==}

def NL.cmp_gt_add_left(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+ap:
      NL.cmp_gt_succ(Nat.add(ap, b), c, NL.cmp_gt_add_left(ap, b, c, e))

def NL.cmp_lt_add_r(a, b, c, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.add(0n, c)) == LT{} : Cmp}, NL.eq_ne_lt(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.cmp(1n+ap, Nat.add(0n, c)) == LT{} : Cmp}, NL.gt_ne_lt(e))
    case 1n+ap 1n+bp:
      NL.cmp_lt_add_r(ap, bp, c, e)

def NL.cmp_lt_succ_r(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, 1n) == LT{} : Cmp}, NL.eq_ne_lt(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.cmp(1n+ap, 1n) == LT{} : Cmp}, NL.gt_ne_lt(e))
    case 1n+ap 1n+bp:
      NL.cmp_lt_succ_r(ap, bp, e)

def NL.cmp_lt_succ_self(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      NL.cmp_lt_succ_self(ap)

def NL.cmp_sub_lt(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(Nat.sub(0n, 1n), 0n) == LT{} : Cmp}, NL.lt_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(Nat.sub(0n, 2n+bp), 0n) == LT{} : Cmp}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, NL.sub_zero(ap)) : {Nat.cmp(_, 1n+ap) == LT{} : Cmp}
      NL.cmp_lt_succ_self(ap)
    case 1n+ap 1n+bp:
      NL.cmp_lt_succ_r(Nat.sub(ap, 1n+bp), ap, NL.cmp_sub_lt(ap, bp, e))

def NL.cmp_lt_sub_add(a, b, e):
  NL.cmp_gt_sub_add(b, a,
    Equal.trans(Cmp, Nat.cmp(b, a), NL.Cmp.flip(Nat.cmp(a, b)), GT{},
      NL.cmp_antisym(b, a),
      Equal.sym(Cmp, GT{}, NL.Cmp.flip(Nat.cmp(a, b)),
        Equal.cong(Cmp, Cmp, NL.Cmp.flip, LT{}, Nat.cmp(a, b),
          Equal.sym(Cmp, Nat.cmp(a, b), LT{}, e)))))

def NL.cmp_eq_sub_add(a, b, e):
  %NL.cmp_eq(a, b, e) : {Nat.add(Nat.sub(a, _), b) == a : Nat}
  %NL.cmp_eq(a, b, e) : {Nat.add(Nat.sub(a, a), _) == a : Nat}
  %Equal.sym(Nat, Nat.sub(a, a), 0n, NL.sub_self(a)) : {Nat.add(_, a) == a : Nat}
  {==}

def NL.flip_eq_lt(c, e):
  match c:
    case EQ{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, NL.eq_ne_lt(e))
    case LT{}:
      Empty.absurd({LT{} == GT{} : Cmp}, NL.gt_ne_lt(e))
    case GT{}:
      {==}

def NL.sub_pos(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.sub(0n, 0n) == 1n+Nat.sub(0n, 1n) : Nat}, NL.eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.sub(0n, 1n+bp) == 1n+Nat.sub(0n, 2n+bp) : Nat}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, NL.sub_zero(ap)) : {1n+ap == 1n+_ : Nat}
      {==}
    case 1n+ap 1n+bp:
      NL.sub_pos(ap, bp, e)

def NL.cmp_add_sub(x, y, z, e):
  %NL.cmp_gt_sub_add(z, y, e) : {Nat.cmp(Nat.add(x, y), _) == Nat.cmp(x, Nat.sub(z, y)) : Cmp}
  NL.cmp_add_right(x, Nat.sub(z, y), y)

def NL.cmp_sub_add(a, b, c, e):
  %NL.cmp_gt_sub_add(a, c, e) : {Nat.cmp(Nat.sub(a, c), b) == Nat.cmp(_, Nat.add(c, b)) : Cmp}
  %NL.add_comm(b, c) : {Nat.cmp(Nat.sub(a, c), b) == Nat.cmp(Nat.add(Nat.sub(a, c), c), _) : Cmp}
  Equal.sym(Cmp, Nat.cmp(Nat.add(Nat.sub(a, c), c), Nat.add(b, c)), Nat.cmp(Nat.sub(a, c), b), NL.cmp_add_right(Nat.sub(a, c), b, c))

def NL.cmp_add_same_left(a, b):
  %NL.add_comm(b, a) : {Nat.cmp(a, _) == Nat.cmp(0n, b) : Cmp}
  NL.cmp_add_right(0n, b, a)

def NL.cmp_sub_flip(a, b, c, ea, eb):
  %NL.cmp_add_right(Nat.sub(c, a), b, a) : {_ == NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %Equal.sym(Nat, Nat.add(Nat.sub(c, a), a), c, NL.cmp_gt_sub_add(c, a, ea)) : {Nat.cmp(_, Nat.add(b, a)) == NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %Equal.sym(Cmp, Nat.cmp(c, Nat.add(b, a)), NL.Cmp.flip(Nat.cmp(Nat.add(b, a), c)), NL.cmp_antisym(c, Nat.add(b, a))) : {_ == NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %NL.add_comm(a, b) : {NL.Cmp.flip(Nat.cmp(_, c)) == NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %NL.cmp_gt_sub_add(c, b, eb) : {NL.Cmp.flip(Nat.cmp(Nat.add(a, b), _)) == NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(a, b), Nat.add(Nat.sub(c, b), b)), Nat.cmp(a, Nat.sub(c, b)), NL.cmp_add_right(a, Nat.sub(c, b), b)) : {NL.Cmp.flip(_) == NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  {==}

# Nat.pred: predecessor (0 maps to 0)
def Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def NL.succ_inj(a, b, e):
  Equal.cong(Nat, Nat, Nat.pred, 1n+a, 1n+b, e)

# NatIsPos: discrimination family, Unit on successors, Empty on zero
def NatIsPos(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def NL.succ_add_ne(b, k, e):
  match k:
    case 0n:
      %Equal.sym(Nat, 0n, Nat.add(1n+b, 0n), e) : NatIsPos(_)
      Unit{}
    case 1n+kp:
      NL.succ_add_ne(b, kp,
        Equal.trans(Nat, kp, Nat.add(b, 1n+kp), 1n+Nat.add(b, kp),
          NL.succ_inj(kp, Nat.add(b, 1n+kp), e),
          Equal.sym(Nat, 1n+Nat.add(b, kp), Nat.add(b, 1n+kp), NL.add_succ(b, kp))))

def NL.add_cancel(a, b, k, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, NL.succ_add_ne(bp, k, e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat},
        NL.succ_add_ne(ap, k, Equal.sym(Nat, Nat.add(1n+ap, k), Nat.add(0n, k), e)))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, x => 1n+x, ap, bp,
        NL.add_cancel(ap, bp, k, NL.succ_inj(Nat.add(ap, k), Nat.add(bp, k), e)))

def NL.cmp_lt_of_sub_lt(b, c, x, e1, e2):
  %NL.cmp_gt_sub_add(x, c, e1) : {Nat.cmp(_, Nat.add(c, b)) == LT{} : Cmp}
  %NL.add_comm(b, c) : {Nat.cmp(Nat.add(Nat.sub(x, c), c), _) == LT{} : Cmp}
  Equal.trans(Cmp, Nat.cmp(Nat.add(Nat.sub(x, c), c), Nat.add(b, c)), Nat.cmp(Nat.sub(x, c), b), LT{},
    NL.cmp_add_right(Nat.sub(x, c), b, c), e2)

def NL.cmp_zero_gt(x, e):
  match x:
    case 0n:
      NL.eq_ne_gt(e)
    case 1n+xp:
      NL.lt_ne_gt(e)

def NL.ge_sub_add(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+bp), 1n+bp) == 0n : Nat}, NL.cmp_zero_gt(bp, e))
    case 1n+ap 0n:
      NL.add_zero(1n+ap)
    case 1n+ap 1n+bp:
      %NL.add_succ(Nat.sub(ap, bp), bp) : {_ == 1n+ap : Nat}
      %NL.ge_sub_add(ap, bp, e) : {1n+Nat.add(Nat.sub(ap, bp), bp) == 1n+_ : Nat}
      {==}

def NL.ci1aux(a, b, c, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.sub(a, b), c), b), Nat.add(Nat.sub(a, b), Nat.add(c, b)), NL.add_assoc(Nat.sub(a, b), c, b)) : {_ == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %NL.add_comm(b, c) : {Nat.add(Nat.sub(a, b), _) == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, b), Nat.add(b, c)), Nat.add(Nat.add(Nat.sub(a, b), b), c), NL.add_assoc_rev(Nat.sub(a, b), b, c)) : {_ == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, b), b), a, NL.ge_sub_add(a, b, e1)) : {Nat.add(_, c) == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %NL.add_assoc_rev(a, Nat.sub(c, b), b) : {Nat.add(a, c) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(c, b), b), c, NL.cmp_gt_sub_add(c, b, e2)) : {Nat.add(a, c) == Nat.add(a, _) : Nat}
  {==}

def NL.ci1(a, b, c, e1, e2):
  NL.add_cancel(Nat.add(Nat.sub(a, b), c), Nat.add(a, Nat.sub(c, b)), b, NL.ci1aux(a, b, c, e1, e2))

def NL.ci2aux(a, c, e):
  %Equal.sym(Nat, Nat.add(Nat.sub(1n+a, Nat.sub(a, c)), Nat.sub(a, c)), 1n+a, NL.cmp_gt_sub_add(1n+a, Nat.sub(a, c), NL.cmp_gt_sub(1n+a, a, c, NL.cmp_gt_refl_succ(a)))) : {_ == Nat.add(1n+c, Nat.sub(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(c, Nat.sub(a, c)), Nat.add(Nat.sub(a, c), c), NL.add_comm(c, Nat.sub(a, c))) : {1n+a == 1n+_ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, c), c), a, NL.cmp_gt_sub_add(a, c, e)) : {1n+a == 1n+_ : Nat}
  {==}

def NL.ci2(a, c, e):
  match a c:
    case 0n 0n:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 0n)) == 0n : Nat}, NL.eq_ne_gt(e))
    case 0n 1n+cp:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+cp)) == 1n+cp : Nat}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      NL.sub_self(ap)
    case 1n+ap 1n+cp:
      NL.add_cancel(Nat.sub(1n+ap, Nat.sub(ap, cp)), 1n+cp, Nat.sub(ap, cp), NL.ci2aux(ap, cp, e))

def NL.ci3aux(x, y, z, e1, e2, e3):
  %NL.cmp_gt_sub_add(y, x, e1) : {Nat.add(Nat.sub(z, Nat.sub(y, x)), _) == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.add(Nat.sub(y, x), x)), Nat.add(Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), x), NL.add_assoc_rev(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x), x)) : {_ == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), z, NL.cmp_gt_sub_add(z, Nat.sub(y, x), Equal.trans(Cmp, Nat.cmp(z, Nat.sub(y, x)), NL.Cmp.flip(Nat.cmp(Nat.sub(y, x), z)), GT{}, NL.cmp_antisym(z, Nat.sub(y, x)), Equal.cong(Cmp, Cmp, NL.Cmp.flip, Nat.cmp(Nat.sub(y, x), z), LT{}, e3)))) : {Nat.add(_, x) == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}
  %NL.cmp_gt_sub_add(y, z, e2) : {Nat.add(z, x) == Nat.add(Nat.sub(x, Nat.sub(y, z)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.add(Nat.sub(y, z), z)), Nat.add(Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)), z), NL.add_assoc_rev(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z), z)) : {Nat.add(z, x) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)), x, NL.cmp_gt_sub_add(x, Nat.sub(y, z), NL.flip_eq_lt(Nat.cmp(x, Nat.sub(y, z)), Equal.trans(Cmp, NL.Cmp.flip(Nat.cmp(x, Nat.sub(y, z))), Nat.cmp(Nat.sub(y, x), z), LT{}, Equal.sym(Cmp, Nat.cmp(Nat.sub(y, x), z), NL.Cmp.flip(Nat.cmp(x, Nat.sub(y, z))), NL.cmp_sub_flip(x, z, y, e1, e2)), e3)))) : {Nat.add(z, x) == Nat.add(_, z) : Nat}
  NL.add_comm(z, x)

def NL.ci3(x, y, z, e1, e2, e3):
  NL.add_cancel(Nat.sub(z, Nat.sub(y, x)), Nat.sub(x, Nat.sub(y, z)), y, NL.ci3aux(x, y, z, e1, e2, e3))

def NL.ci4aux(x, y, z, e1, e2):
  %NL.cmp_gt_sub_add(y, x, e1) : {Nat.add(Nat.sub(z, Nat.sub(y, x)), _) == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.add(Nat.sub(y, x), x)), Nat.add(Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), x), NL.add_assoc_rev(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x), x)) : {_ == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), z, NL.cmp_gt_sub_add(z, Nat.sub(y, x), NL.cmp_gt_sub(z, y, x, e2))) : {Nat.add(_, x) == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}
  %NL.add_assoc_rev(x, Nat.sub(z, y), y) : {Nat.add(z, x) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, y), y), z, NL.cmp_gt_sub_add(z, y, e2)) : {Nat.add(z, x) == Nat.add(x, _) : Nat}
  NL.add_comm(z, x)

def NL.ci4(x, y, z, e1, e2):
  NL.add_cancel(Nat.sub(z, Nat.sub(y, x)), Nat.add(x, Nat.sub(z, y)), y, NL.ci4aux(x, y, z, e1, e2))

def NL.ci5aux(a, b, c, e):
  %Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(a, b), c), c), Nat.add(a, b), NL.cmp_gt_sub_add(Nat.add(a, b), c, NL.cmp_gt_add_left(a, b, c, e))) : {_ == Nat.add(Nat.add(a, Nat.sub(b, c)), c) : Nat}
  %NL.add_assoc_rev(a, Nat.sub(b, c), c) : {Nat.add(a, b) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(b, c), c), b, NL.cmp_gt_sub_add(b, c, e)) : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def NL.ci5(a, b, c, e):
  NL.add_cancel(Nat.sub(Nat.add(a, b), c), Nat.add(a, Nat.sub(b, c)), c, NL.ci5aux(a, b, c, e))

def NL.ci6aux(a, b, c, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(a, b), c), c), Nat.add(a, b), NL.cmp_gt_sub_add(Nat.add(a, b), c, e2)) : {_ == Nat.add(Nat.sub(a, Nat.sub(c, b)), c) : Nat}
  %NL.cmp_gt_sub_add(c, b, e1) : {Nat.add(a, b) == Nat.add(Nat.sub(a, Nat.sub(c, b)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, Nat.sub(c, b)), Nat.add(Nat.sub(c, b), b)), Nat.add(Nat.add(Nat.sub(a, Nat.sub(c, b)), Nat.sub(c, b)), b), NL.add_assoc_rev(Nat.sub(a, Nat.sub(c, b)), Nat.sub(c, b), b)) : {Nat.add(a, b) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, Nat.sub(c, b)), Nat.sub(c, b)), a, NL.cmp_gt_sub_add(a, Nat.sub(c, b), Equal.trans(Cmp, Nat.cmp(a, Nat.sub(c, b)), Nat.cmp(Nat.add(a, b), c), GT{}, Equal.sym(Cmp, Nat.cmp(Nat.add(a, b), c), Nat.cmp(a, Nat.sub(c, b)), NL.cmp_add_sub(a, b, c, e1)), e2))) : {Nat.add(a, b) == Nat.add(_, b) : Nat}
  {==}

def NL.ci6(a, b, c, e1, e2):
  NL.add_cancel(Nat.sub(Nat.add(a, b), c), Nat.sub(a, Nat.sub(c, b)), c, NL.ci6aux(a, b, c, e1, e2))

def NL.ci7(a, b, c):
  %NL.add_comm(b, a) : {Nat.sub(c, _) == Nat.sub(Nat.sub(c, b), a) : Nat}
  NL.sub_add(c, b, a)

def NL.ci9aux(b, c, x, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(c, b), x), x), Nat.add(c, b), NL.cmp_gt_sub_add(Nat.add(c, b), x, Equal.trans(Cmp, Nat.cmp(Nat.add(c, b), x), NL.Cmp.flip(Nat.cmp(x, Nat.add(c, b))), GT{}, NL.cmp_antisym(Nat.add(c, b), x), Equal.cong(Cmp, Cmp, NL.Cmp.flip, Nat.cmp(x, Nat.add(c, b)), LT{}, NL.cmp_lt_of_sub_lt(b, c, x, e1, e2))))) : {_ == Nat.add(Nat.sub(b, Nat.sub(x, c)), x) : Nat}
  %NL.cmp_gt_sub_add(x, c, e1) : {Nat.add(c, b) == Nat.add(Nat.sub(b, Nat.sub(x, c)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(b, Nat.sub(x, c)), Nat.add(Nat.sub(x, c), c)), Nat.add(Nat.add(Nat.sub(b, Nat.sub(x, c)), Nat.sub(x, c)), c), NL.add_assoc_rev(Nat.sub(b, Nat.sub(x, c)), Nat.sub(x, c), c)) : {Nat.add(c, b) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(b, Nat.sub(x, c)), Nat.sub(x, c)), b, NL.cmp_gt_sub_add(b, Nat.sub(x, c), Equal.trans(Cmp, Nat.cmp(b, Nat.sub(x, c)), NL.Cmp.flip(Nat.cmp(Nat.sub(x, c), b)), GT{}, NL.cmp_antisym(b, Nat.sub(x, c)), Equal.cong(Cmp, Cmp, NL.Cmp.flip, Nat.cmp(Nat.sub(x, c), b), LT{}, e2)))) : {Nat.add(c, b) == Nat.add(_, c) : Nat}
  NL.add_comm(c, b)

def NL.ci9(b, c, x, e1, e2):
  NL.add_cancel(Nat.sub(Nat.add(c, b), x), Nat.sub(b, Nat.sub(x, c)), x, NL.ci9aux(b, c, x, e1, e2))

def NL.ci10(a, b, x, e):
  match a x:
    case 0n 0n:
      {==}
    case 0n 1n+xp:
      Empty.absurd({Nat.sub(1n+Nat.add(0n, b), 1n+xp) == 1n+Nat.add(Nat.sub(0n, 1n+xp), b) : Nat}, NL.cmp_zero_gt(xp, e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+xp:
      NL.ci10(ap, b, xp, e)

def NL.ci8aux(x, y, z, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.sub(x, y), z), Nat.sub(y, z)), Nat.add(Nat.sub(x, y), Nat.add(z, Nat.sub(y, z))), NL.add_assoc(Nat.sub(x, y), z, Nat.sub(y, z))) : {_ == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  %Equal.sym(Nat, Nat.add(z, Nat.sub(y, z)), Nat.add(Nat.sub(y, z), z), NL.add_comm(z, Nat.sub(y, z))) : {Nat.add(Nat.sub(x, y), _) == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(y, z), z), y, NL.cmp_gt_sub_add(y, z, e2)) : {Nat.add(Nat.sub(x, y), _) == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(x, y), y), x, NL.cmp_gt_sub_add(x, y, e1)) : {_ == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  Equal.sym(Nat, Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)), x, NL.cmp_gt_sub_add(x, Nat.sub(y, z), NL.cmp_gt_sub(x, y, z, e1)))

def NL.ci8(x, y, z, e1, e2):
  NL.add_cancel(Nat.add(Nat.sub(x, y), z), Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z), NL.ci8aux(x, y, z, e1, e2))

def NL.cmp_gt_of_lt(a, b, e):
  Equal.trans(Cmp, Nat.cmp(b, a), NL.Cmp.flip(Nat.cmp(a, b)), GT{},
    NL.cmp_antisym(b, a),
    Equal.cong(Cmp, Cmp, NL.Cmp.flip, Nat.cmp(a, b), LT{}, e))

def NL.cmp_lt_of_gt(a, b, e):
  Equal.trans(Cmp, Nat.cmp(b, a), NL.Cmp.flip(Nat.cmp(a, b)), LT{},
    NL.cmp_antisym(b, a),
    Equal.cong(Cmp, Cmp, NL.Cmp.flip, Nat.cmp(a, b), GT{}, e))

def NL.flip_flip(c):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

def NL.cmp_sub_gt_self(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.sub(0n, 1n)) == GT{} : Cmp}, NL.lt_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(0n, Nat.sub(0n, 2n+bp)) == GT{} : Cmp}, NL.lt_ne_gt(e))
    case 1n+ap 0n:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, NL.sub_zero(ap)) : {Nat.cmp(1n+ap, _) == GT{} : Cmp}
      NL.cmp_gt_refl_succ(ap)
    case 1n+ap 1n+bp:
      NL.cmp_gt_succ(ap, Nat.sub(ap, 1n+bp), NL.cmp_sub_gt_self(ap, bp, e))

def NL.cmp_lt_zero(a, e):
  match a:
    case 0n:
      NL.eq_ne_lt(e)
    case 1n+ap:
      NL.gt_ne_lt(e)

def NL.cmp_sub_flip_of(d, a, b, c, ed, ea, eb):
  Equal.trans(Cmp, NL.Cmp.flip(d), NL.Cmp.flip(Nat.cmp(Nat.sub(c, a), b)), Nat.cmp(a, Nat.sub(c, b)),
    Equal.cong(Cmp, Cmp, NL.Cmp.flip, d, Nat.cmp(Nat.sub(c, a), b), ed),
    Equal.trans(Cmp, NL.Cmp.flip(Nat.cmp(Nat.sub(c, a), b)), NL.Cmp.flip(NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b)))), Nat.cmp(a, Nat.sub(c, b)),
      Equal.cong(Cmp, Cmp, NL.Cmp.flip, Nat.cmp(Nat.sub(c, a), b), NL.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))), NL.cmp_sub_flip(a, b, c, ea, eb)),
      NL.flip_flip(Nat.cmp(a, Nat.sub(c, b)))))

def NL.sub_of_add(u, v, w, e):
  %e : {Nat.sub(_, v) == u : Nat}
  NL.add_sub_cancel(u, v)

def NL.mul_sub_add(a, b, c, e):
  Equal.trans(Nat,
    Nat.add(Nat.mul(c, Nat.sub(a, b)), Nat.mul(c, b)),
    Nat.mul(c, Nat.add(Nat.sub(a, b), b)),
    Nat.mul(c, a),
    NL.mul_distrib(c, Nat.sub(a, b), b),
    Equal.cong(Nat, Nat, t => Nat.mul(c, t),
      Nat.add(Nat.sub(a, b), b), a, NL.cmp_gt_sub_add(a, b, e)))

def NL.mul_sub(a, b, c, e):
  Equal.sym(Nat,
    Nat.sub(Nat.mul(c, a), Nat.mul(c, b)),
    Nat.mul(c, Nat.sub(a, b)),
    NL.sub_of_add(Nat.mul(c, Nat.sub(a, b)), Nat.mul(c, b), Nat.mul(c, a),
      NL.mul_sub_add(a, b, c, e)))

# The cross-sum lemmas
# ====================
#
# Neither fill is an induction: both are single Equal chains, because neither
# statement is about a recursive Nat -- only cmp_add_right, cmp_gt_sub_add,
# add_assoc and add_comm are involved, one step each.

# cross_gt_gt: cancel the common add(xn,yn) from the cross sum, after expanding
# the two differences. The first half is
#   A + (xn+yn) = (A+xn) + yn = xp + yn          (add_assoc backwards,
#                                                 cmp_gt_sub_add)
# and the second is the hypothesis, then the mirrored expansion of yp inside
# its right side, then add_assoc and add_comm to swing the trailing xn in:
#   xp + yn = yp + xn = (B+yn) + xn = B + (yn+xn) = B + (xn+yn).
def NL.cross_gt_gt(xp, xn, yp, yn, e1, e2, e):
  NL.add_cancel(Nat.sub(xp, xn), Nat.sub(yp, yn), Nat.add(xn, yn),
    Equal.trans(Nat,
      Nat.add(Nat.sub(xp, xn), Nat.add(xn, yn)),
      Nat.add(xp, yn),
      Nat.add(Nat.sub(yp, yn), Nat.add(xn, yn)),
      Equal.trans(Nat,
        Nat.add(Nat.sub(xp, xn), Nat.add(xn, yn)),
        Nat.add(Nat.add(Nat.sub(xp, xn), xn), yn),
        Nat.add(xp, yn),
        Equal.sym(Nat,
          Nat.add(Nat.add(Nat.sub(xp, xn), xn), yn),
          Nat.add(Nat.sub(xp, xn), Nat.add(xn, yn)),
          NL.add_assoc(Nat.sub(xp, xn), xn, yn)),
        Equal.cong(Nat, Nat, u => Nat.add(u, yn),
          Nat.add(Nat.sub(xp, xn), xn), xp,
          NL.cmp_gt_sub_add(xp, xn, e1))),
      Equal.trans(Nat,
        Nat.add(xp, yn),
        Nat.add(yp, xn),
        Nat.add(Nat.sub(yp, yn), Nat.add(xn, yn)),
        e,
        Equal.trans(Nat,
          Nat.add(yp, xn),
          Nat.add(Nat.add(Nat.sub(yp, yn), yn), xn),
          Nat.add(Nat.sub(yp, yn), Nat.add(xn, yn)),
          Equal.cong(Nat, Nat, u => Nat.add(u, xn),
            yp, Nat.add(Nat.sub(yp, yn), yn),
            Equal.sym(Nat, Nat.add(Nat.sub(yp, yn), yn), yp,
              NL.cmp_gt_sub_add(yp, yn, e2))),
          Equal.trans(Nat,
            Nat.add(Nat.add(Nat.sub(yp, yn), yn), xn),
            Nat.add(Nat.sub(yp, yn), Nat.add(yn, xn)),
            Nat.add(Nat.sub(yp, yn), Nat.add(xn, yn)),
            NL.add_assoc(Nat.sub(yp, yn), yn, xn),
            Equal.cong(Nat, Nat, u => Nat.add(Nat.sub(yp, yn), u),
              Nat.add(yn, xn), Nat.add(xn, yn), NL.add_comm(yn, xn)))))))

# cross_cmp: c1 reaches the common scaled comparison in one step (the branch's
# own evidence, then cmp_add_right backwards); that comparison reaches c2
# through the hypothesis, commutation, cmp_add_right on the other pair, and the
# second branch's evidence backwards.
def NL.cross_cmp(c1, xp, xn, c2, yp, yn, e1, e2, e):
  Equal.trans(Cmp,
    c1,
    Nat.cmp(Nat.add(xp, yn), Nat.add(xn, yn)),
    c2,
    Equal.trans(Cmp,
      c1,
      Nat.cmp(xp, xn),
      Nat.cmp(Nat.add(xp, yn), Nat.add(xn, yn)),
      e1,
      Equal.sym(Cmp,
        Nat.cmp(Nat.add(xp, yn), Nat.add(xn, yn)),
        Nat.cmp(xp, xn),
        NL.cmp_add_right(xp, xn, yn))),
    Equal.trans(Cmp,
      Nat.cmp(Nat.add(xp, yn), Nat.add(xn, yn)),
      Nat.cmp(Nat.add(yp, xn), Nat.add(yn, xn)),
      c2,
      Equal.trans(Cmp,
        Nat.cmp(Nat.add(xp, yn), Nat.add(xn, yn)),
        Nat.cmp(Nat.add(yp, xn), Nat.add(xn, yn)),
        Nat.cmp(Nat.add(yp, xn), Nat.add(yn, xn)),
        Equal.cong(Nat, Cmp, u => Nat.cmp(u, Nat.add(xn, yn)),
          Nat.add(xp, yn), Nat.add(yp, xn), e),
        Equal.cong(Nat, Cmp, u => Nat.cmp(Nat.add(yp, xn), u),
          Nat.add(xn, yn), Nat.add(yn, xn), NL.add_comm(xn, yn))),
      Equal.trans(Cmp,
        Nat.cmp(Nat.add(yp, xn), Nat.add(yn, xn)),
        Nat.cmp(yp, yn),
        c2,
        NL.cmp_add_right(yp, yn, xn),
        Equal.sym(Cmp, c2, Nat.cmp(yp, yn), e2))))

# Nat.divmod
# ==========
#
# Both laws are inductions on n, the fuel, with the budget hypothesis e1 as
# the only side condition. e1 is oriented {r + (1 + m) == b}, so `%e1`
# replaces b (its right side) with r + (1 + m); the two steps that need the
# other direction wrap it in Equal.sym, exactly as the orientation note in
# PROVING.md describes.
#
# The recursive calls carry a re-derived budget, because the loop's new state
# spells it differently:
#   m rolls over (m = 0): the new budget is 1 + r = b, i.e. the same equation
#     with the sides added the other way round (Nat.add_comm on m = 0);
#   m bumps (m = 1 + mp): the new budget is (1 + r) + (1 + mp) = b, which is
#     the old one plus `add_succ` (1 + (r + X) = r + (1 + X)) -- this is the
#     reason the law states 1 + m rather than m + 1.

def NL.divmod.go.spec(n, m, d, r, b, e1):
  match n:
    case 0n:
      # go(0, m, d, r) = (d, r), so the goal is d*b + r = d*b + (r + 0).
      %Equal.sym(Nat, Nat.add(r, 0n), r, NL.add_zero(r)) : {Nat.add(Nat.mul(d, b), r) == Nat.add(Nat.mul(d, b), _) : Nat}
      {==}
    case 1n+np:
      match m:
        case 0n:
          # go(1+np, 0, d, r) = go(np, r, 1+d, 0): the goal's right side
          # r + (1 + np) has to become (1+d)*b + (0 + np), i.e. (b + d*b) + np.
          %NL.add_assoc(r, 1n, np) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), b), Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n))) == Nat.add(Nat.mul(d, b), _) : Nat}
          %Equal.sym(Nat, Nat.add(r, 1n), b, e1) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), b), Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n))) == Nat.add(Nat.mul(d, b), Nat.add(_, np)) : Nat}
          %NL.add_assoc(Nat.mul(d, b), b, np) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), b), Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n))) == _ : Nat}
          %Equal.sym(Nat, Nat.add(Nat.mul(d, b), b), Nat.add(b, Nat.mul(d, b)), NL.add_comm(Nat.mul(d, b), b)) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), b), Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n))) == Nat.add(_, np) : Nat}
          NL.divmod.go.spec(np, r, 1n+d, 0n, b,
            Equal.trans(Nat, Nat.add(1n, r), Nat.add(r, 1n), b,
              Equal.sym(Nat, Nat.add(r, 1n), Nat.add(1n, r), NL.add_comm(r, 1n)),
              e1))
        case 1n+mp:
          # go(1+np, 1+mp, d, r) = go(np, mp, d, 1+r): the goal's r + (1 + np)
          # is the new state's (1 + r) + np up to add_succ, one rewrite.
          %NL.add_succ(r, np) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, mp, d, 1n+r)), b), Nat.mod.fin(Nat.divmod.go(np, mp, d, 1n+r))) == Nat.add(Nat.mul(d, b), _) : Nat}
          NL.divmod.go.spec(np, mp, d, 1n+r, b,
            Equal.trans(Nat, Nat.add(Nat.add(1n, r), Nat.add(1n, mp)), Nat.add(r, Nat.add(1n, Nat.add(1n, mp))), b,
              NL.add_succ(r, Nat.add(1n, mp)),
              e1))

def NL.divmod.go.mod_lt(n, m, d, r, b, e1):
  match n:
    case 0n:
      # go(0, m, d, r) = (d, r): the remainder is r, and the budget
      # r + (1 + m) = b already says r < b. Rewriting b to r + (1 + m) turns
      # the goal into cmp(r, r + (1+m)) = LT, which cmp_add_same_left moves to
      # cmp(0, 1+m) = LT -- and 1 + m is a constructor, so that is reflexive.
      %e1 : {Nat.cmp(r, _) == LT{} : Cmp}
      %Equal.sym(Cmp, Nat.cmp(r, Nat.add(r, Nat.add(1n, m))), Nat.cmp(0n, Nat.add(1n, m)), NL.cmp_add_same_left(r, Nat.add(1n, m))) : {_ == LT{} : Cmp}
      {==}
    case 1n+np:
      match m:
        case 0n:
          NL.divmod.go.mod_lt(np, r, 1n+d, 0n, b,
            Equal.trans(Nat, Nat.add(1n, r), Nat.add(r, 1n), b,
              Equal.sym(Nat, Nat.add(r, 1n), Nat.add(1n, r), NL.add_comm(r, 1n)),
              e1))
        case 1n+mp:
          NL.divmod.go.mod_lt(np, mp, d, 1n+r, b,
            Equal.trans(Nat, Nat.add(Nat.add(1n, r), Nat.add(1n, mp)), Nat.add(r, Nat.add(1n, Nat.add(1n, mp))), b,
              NL.add_succ(r, Nat.add(1n, mp)),
              e1))

# The initial state (a, bp, 0, 0) has budget 0 + (1 + bp) = 1 + bp, which is
# the divisor itself, so e1 is `{==}` at both call sites and the two laws
# about Nat.div / Nat.mod are one call each: Nat.divmod(a, 1+b) reduces to
# Nat.divmod.go(a, b, 0, 0) and the invariant's right side d*b + (r + n)
# reduces to a.
def NL.div_add_mod(a, b):
  NL.divmod.go.spec(a, b, 0n, 0n, 1n+b, {==})

def NL.mod_lt(a, b):
  NL.divmod.go.mod_lt(a, b, 0n, 0n, 1n+b, {==})

# Exact division
# ==============
#
# div_unique is the induction; everything else in the block is a call of it (or
# of div_exact) with an equation shuffled into the shape it wants.

# lt_ne_add: the comparison moves to cmp(s, 0) -- cmp_add_right at b, then
# add_comm so that the trailing b is add(0, b) = b -- and cmp_lt_zero refutes it.
def NL.lt_ne_add(a, b, s, e1, e2):
  NL.cmp_lt_zero(s,
    Equal.trans(Cmp, Nat.cmp(s, 0n), Nat.cmp(Nat.add(b, s), b), LT{},
      Equal.trans(Cmp, Nat.cmp(s, 0n), Nat.cmp(Nat.add(s, b), b), Nat.cmp(Nat.add(b, s), b),
        Equal.sym(Cmp, Nat.cmp(Nat.add(s, b), b), Nat.cmp(s, 0n),
          NL.cmp_add_right(s, 0n, b)),
        Equal.sym(Cmp, Nat.cmp(Nat.add(b, s), b), Nat.cmp(Nat.add(s, b), b),
          Equal.cong(Nat, Cmp, u => Nat.cmp(u, b), Nat.add(b, s), Nat.add(s, b),
            NL.add_comm(b, s)))),
      Equal.trans(Cmp, Nat.cmp(Nat.add(b, s), b), Nat.cmp(a, b), LT{},
        Equal.cong(Nat, Cmp, u => Nat.cmp(u, b), Nat.add(b, s), a, e2),
        e1)))

# add_assoc_cancel: move the common b0 out to the right on both sides (comm,
# then add_assoc backwards) and add_cancel it away.
def NL.add_assoc_cancel(b0, x, r, y, s, e):
  NL.add_cancel(Nat.add(x, r), Nat.add(y, s), b0,
    Equal.trans(Nat,
      Nat.add(Nat.add(x, r), b0),
      Nat.add(Nat.add(b0, x), r),
      Nat.add(Nat.add(y, s), b0),
      Equal.trans(Nat,
        Nat.add(Nat.add(x, r), b0),
        Nat.add(b0, Nat.add(x, r)),
        Nat.add(Nat.add(b0, x), r),
        NL.add_comm(Nat.add(x, r), b0),
        Equal.sym(Nat, Nat.add(Nat.add(b0, x), r), Nat.add(b0, Nat.add(x, r)),
          NL.add_assoc(b0, x, r))),
      Equal.trans(Nat,
        Nat.add(Nat.add(b0, x), r),
        Nat.add(Nat.add(b0, y), s),
        Nat.add(Nat.add(y, s), b0),
        e,
        Equal.trans(Nat,
          Nat.add(Nat.add(b0, y), s),
          Nat.add(b0, Nat.add(y, s)),
          Nat.add(Nat.add(y, s), b0),
          NL.add_assoc(b0, y, s),
          NL.add_comm(b0, Nat.add(y, s))))))

# div_unique: induction on d1, case on d2, and in the folded case the common b0
# comes off both sides with add_assoc_cancel before the induction hypothesis
# applies.
#
# The two vacuous branches produce the hypothesis of lt_ne_add from the same
# equation: with the d = 0 side reduced, one side of the equation is exactly
# b0 + (d'*b0 + r), and lt_ne_add turns that into Empty.
def NL.div_unique(d1, r1, d2, r2, b0, e, l1, l2):
  match d1:
    case 0n:
      match d2:
        case 0n:
          {==}
        case 1n+dp:
          Empty.absurd({0n == 1n+dp : Nat},
            NL.lt_ne_add(r1, 1n+b0, Nat.add(Nat.mul(dp, 1n+b0), r2), l1,
              Equal.trans(Nat,
                Nat.add(1n+b0, Nat.add(Nat.mul(dp, 1n+b0), r2)),
                Nat.add(Nat.add(1n+b0, Nat.mul(dp, 1n+b0)), r2),
                r1,
                NL.add_assoc_rev(1n+b0, Nat.mul(dp, 1n+b0), r2),
                Equal.sym(Nat, r1, Nat.add(Nat.add(1n+b0, Nat.mul(dp, 1n+b0)), r2), e))))
    case 1n+d1p:
      match d2:
        case 0n:
          Empty.absurd({1n+d1p == 0n : Nat},
            NL.lt_ne_add(r2, 1n+b0, Nat.add(Nat.mul(d1p, 1n+b0), r1), l2,
              Equal.trans(Nat,
                Nat.add(1n+b0, Nat.add(Nat.mul(d1p, 1n+b0), r1)),
                Nat.add(Nat.add(1n+b0, Nat.mul(d1p, 1n+b0)), r1),
                r2,
                NL.add_assoc_rev(1n+b0, Nat.mul(d1p, 1n+b0), r1),
                e)))
        case 1n+d2p:
          Equal.cong(Nat, Nat, u => 1n+u, d1p, d2p,
            NL.div_unique(d1p, r1, d2p, r2, b0,
              NL.add_assoc_cancel(1n+b0, Nat.mul(d1p, 1n+b0), r1, Nat.mul(d2p, 1n+b0), r2, e),
              l1, l2))

# div_exact: the two representations of a are (div(a,1+b), mod(a,1+b)) from
# div_add_mod and (q, 0) from the hypothesis -- the second needs the equation
# commuted (mul_comm) and zero added, since div_unique wants it as
# mul(q, 1+b) + 0.
def NL.div_exact(a, b, q, e):
  NL.div_unique(Nat.div(a, 1n+b), Nat.mod(a, 1n+b), q, 0n, b,
    Equal.trans(Nat,
      Nat.add(Nat.mul(Nat.div(a, 1n+b), 1n+b), Nat.mod(a, 1n+b)),
      a,
      Nat.add(Nat.mul(q, 1n+b), 0n),
      NL.div_add_mod(a, b),
      Equal.trans(Nat, a, Nat.mul(1n+b, q), Nat.add(Nat.mul(q, 1n+b), 0n),
        e,
        Equal.trans(Nat, Nat.mul(1n+b, q), Nat.mul(q, 1n+b), Nat.add(Nat.mul(q, 1n+b), 0n),
          NL.mul_comm(1n+b, q),
          Equal.sym(Nat, Nat.add(Nat.mul(q, 1n+b), 0n), Nat.mul(q, 1n+b),
            NL.add_zero(Nat.mul(q, 1n+b)))))),
    NL.mod_lt(a, b),
    {==})

# div_exact_mul: a*(1+k) is (1+b)*(1+k)*q up to mul_assoc and mul_comm, and
# div_exact is stated for the divisor written 1 + b' -- here b' = k + b*(1+k),
# which is what (1+b)*(1+k) reduces to.
def NL.div_exact_mul(a, b, q, k, e):
  NL.div_exact(Nat.mul(a, 1n+k), Nat.add(k, Nat.mul(b, 1n+k)), q,
    Equal.trans(Nat,
      Nat.mul(a, 1n+k),
      Nat.mul(Nat.mul(1n+b, q), 1n+k),
      Nat.mul(Nat.mul(1n+b, 1n+k), q),
      Equal.cong(Nat, Nat, u => Nat.mul(u, 1n+k), a, Nat.mul(1n+b, q), e),
      Equal.trans(Nat,
        Nat.mul(Nat.mul(1n+b, q), 1n+k),
        Nat.mul(1n+b, Nat.mul(1n+k, q)),
        Nat.mul(Nat.mul(1n+b, 1n+k), q),
        Equal.trans(Nat,
          Nat.mul(Nat.mul(1n+b, q), 1n+k),
          Nat.mul(1n+b, Nat.mul(q, 1n+k)),
          Nat.mul(1n+b, Nat.mul(1n+k, q)),
          NL.mul_assoc(1n+b, q, 1n+k),
          Equal.cong(Nat, Nat, u => Nat.mul(1n+b, u), Nat.mul(q, 1n+k), Nat.mul(1n+k, q),
            NL.mul_comm(q, 1n+k))),
        Equal.sym(Nat, Nat.mul(Nat.mul(1n+b, 1n+k), q), Nat.mul(1n+b, Nat.mul(1n+k, q)),
          NL.mul_assoc(1n+b, 1n+k, q)))))

# div_one: g = 1 is 1 + 0, and a == 1*a is mul_one (a == a*1) commuted.
def NL.div_one(a):
  NL.div_exact(a, 0n, a,
    Equal.trans(Nat, a, Nat.mul(a, 1n), Nat.mul(1n, a),
      NL.mul_one(a),
      Equal.sym(Nat, Nat.mul(1n, a), Nat.mul(a, 1n), NL.mul_comm(1n, a))))

# div_zero: both branches of Nat.divmod answer 0 for a zero dividend, so the
# whole proof is the case split that lets divmod's own match on the divisor
# fire.
def NL.div_zero(d):
  match d:
    case 0n:
      {==}
    case 1n+dp:
      {==}

def NL.div_self(ap):
  NL.div_exact(1n+ap, ap, 1n, NL.mul_one(1n+ap))

def NL.sub_zero_left(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      {==}

def NL.sub_of_lt(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.sub(0n, 0n) == 0n : Nat}, NL.eq_ne_lt(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, NL.gt_ne_lt(e))
    case 1n+ap 1n+bp:
      NL.sub_of_lt(ap, bp, e)

# Nat.pos_ne_zero: a successor is not zero -- the discrimination halves of
# divides_pos. Bare rather than NL-prefixed (it is proof machinery, no law
# statement mentions it), like Nat.pred and Nat.succ_add_ne_zero.
def Nat.pos_ne_zero(n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  %e : NatIsPos(_)
  Unit{}

def NL.pos_witness(n, e):
  Equal.trans(Nat, n, Nat.sub(n, 0n), 1n+Nat.sub(n, 1n),
    Equal.sym(Nat, Nat.sub(n, 0n), n, NL.sub_zero(n)),
    NL.sub_pos(n, 0n, NL.cmp_gt_of_lt(0n, n, e)))

def NL.divides_pos(g, q, ap, e):
  match g:
    case 0n:
      Empty.absurd({Nat.cmp(0n, 0n) == LT{} : Cmp}, Nat.pos_ne_zero(ap, e))
    case 1n+gp:
      {==}

# sub_diag: GT and LT rewrite the side that is zero and then collapse the outer
# truncation (sub_zero, sub_zero_left); EQ turns the comparison into np == nn
# and derives both sides are 0 from sub_self.
def NL.sub_diag(c, np, nn, e):
  match c:
    case GT{}:
      %Equal.sym(Nat, Nat.sub(nn, np), 0n,
        NL.sub_of_lt(nn, np, NL.cmp_lt_of_gt(np, nn, Equal.sym(Cmp, GT{}, Nat.cmp(np, nn), e))))
        : {Nat.sub(Nat.sub(np, nn), _) == Nat.sub(np, nn) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.sub(np, nn), 0n), Nat.sub(np, nn), NL.sub_zero(Nat.sub(np, nn)))
        : {_ == Nat.sub(np, nn) : Nat}
      {==}
    case EQ{}:
      %Equal.sym(Nat, Nat.sub(np, nn), 0n,
        Equal.trans(Nat, Nat.sub(np, nn), Nat.sub(np, np), 0n,
          Equal.cong(Nat, Nat, u => Nat.sub(np, u), nn, np,
            Equal.sym(Nat, np, nn, NL.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e)))),
          NL.sub_self(np)))
        : {Nat.sub(_, Nat.sub(nn, np)) == _ : Nat}
      %Equal.sym(Nat, Nat.sub(nn, np), 0n,
        Equal.trans(Nat, Nat.sub(nn, np), Nat.sub(nn, nn), 0n,
          Equal.cong(Nat, Nat, u => Nat.sub(nn, u), np, nn,
            NL.cmp_eq(np, nn, Equal.sym(Cmp, EQ{}, Nat.cmp(np, nn), e))),
          NL.sub_self(nn)))
        : {Nat.sub(0n, _) == 0n : Nat}
      {==}
    case LT{}:
      %Equal.sym(Nat, Nat.sub(np, nn), 0n,
        NL.sub_of_lt(np, nn, Equal.sym(Cmp, LT{}, Nat.cmp(np, nn), e)))
        : {Nat.sub(_, Nat.sub(nn, np)) == _ : Nat}
      %Equal.sym(Nat, Nat.sub(0n, Nat.sub(nn, np)), 0n, NL.sub_zero_left(Nat.sub(nn, np)))
        : {_ == 0n : Nat}
      {==}

# Nat.gcd
# =======
#
# Fills the gcd block of nat.bend. The proofs are, in order of size:
#   - the two Nat shuffles callers need (add_mul_slack, and the slack
#     identities inside gcd.go.fuel) -- pure reassociation;
#   - gcd.go.scale, an induction on the fuel whose step is one cmp transport
#     plus one Nat.sub scaling;
#   - gcd.go.fuel and gcd.go.divides, inductions on the fuel slack u (which is
#     what keeps the two fuel spellings in step) and on the fuel itself.

# d is a parameter, so the caller passes the constructor it matched and the
# scaled comparison collapses to that constructor outright.
def NL.cmp_mul_right_of(a, b, k, d, e):
  Equal.trans(Cmp, d, Nat.cmp(a, b), Nat.cmp(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k)),
    e, Equal.sym(Cmp, Nat.cmp(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k)), Nat.cmp(a, b), NL.cmp_mul_right(a, b, k)))

# mul_sub_right = mul_sub conjugated by Nat.mul_comm on both sides; the goal's
# products are written the other way round, so the two product rewrites come
# first and the lemma application last.
def NL.mul_sub_right(a, b, c, e):
  %NL.mul_comm(c, a) : {Nat.mul(Nat.sub(a, b), c) == Nat.sub(_, Nat.mul(b, c)) : Nat}
  %NL.mul_comm(c, b) : {Nat.mul(Nat.sub(a, b), c) == Nat.sub(Nat.mul(c, a), _) : Nat}
  %NL.mul_sub(a, b, c, e) : {Nat.mul(Nat.sub(a, b), c) == _ : Nat}
  NL.mul_comm(Nat.sub(a, b), c)

def NL.add_mul_slack(x, y, k):
  %NL.mul_succ(x, k) : {Nat.add(Nat.add(x, y), Nat.add(Nat.mul(x, k), Nat.mul(y, k))) == Nat.add(_, Nat.mul(y, 1n+k)) : Nat}
  %NL.mul_succ(y, k) : {Nat.add(Nat.add(x, y), Nat.add(Nat.mul(x, k), Nat.mul(y, k))) == Nat.add(Nat.add(x, Nat.mul(x, k)), _) : Nat}
  %NL.add_assoc_rev(x, y, Nat.add(Nat.mul(x, k), Nat.mul(y, k))) : {_ == Nat.add(Nat.add(x, Nat.mul(x, k)), Nat.add(y, Nat.mul(y, k))) : Nat}
  %NL.add_exchange(Nat.mul(x, k), y, Nat.mul(y, k)) : {Nat.add(x, _) == Nat.add(Nat.add(x, Nat.mul(x, k)), Nat.add(y, Nat.mul(y, k))) : Nat}
  %NL.add_assoc(x, Nat.mul(x, k), Nat.add(y, Nat.mul(y, k))) : {_ == Nat.add(Nat.add(x, Nat.mul(x, k)), Nat.add(y, Nat.mul(y, k))) : Nat}
  {==}

# gcd.go.scale: induction on the fuel. Each step is the loop's own equivariance
# -- the scaled comparison collapses to the branch constructor
# (cmp_mul_right_of), the scaled difference collapses to the scaled difference
# (mul_sub_right) -- after which the recursive call is literally the induction
# hypothesis at the new state. The fuel is not touched, which is why the law
# needs no hypothesis: the two sides run out of fuel together.
def NL.gcd.go.scale(s, y, c, x, kp, e):
  match s:
    case 0n:
      %NL.mul_zero(1n+kp) : {_ == Nat.mul(1n+kp, 0n) : Nat}
      {==}
    case 1n+sp:
      match y:
        case 0n:
          %NL.mul_comm(x, 1n+kp) : {Nat.mul(x, 1n+kp) == _ : Nat}
          {==}
        case 1n+yp:
          match c:
            case EQ{}:
              %NL.cmp_mul_right_of(x, 1n+yp, kp, EQ{}, e) : {NL.Nat.gcd.go(1n+sp, Nat.mul(1n+yp, 1n+kp), _, Nat.mul(x, 1n+kp)) == Nat.mul(1n+kp, x) : Nat}
              %NL.mul_comm(x, 1n+kp) : {Nat.mul(x, 1n+kp) == _ : Nat}
              {==}
            case LT{}:
              %NL.cmp_mul_right_of(x, 1n+yp, kp, LT{}, e) : {NL.Nat.gcd.go(1n+sp, Nat.mul(1n+yp, 1n+kp), _, Nat.mul(x, 1n+kp)) == Nat.mul(1n+kp, NL.Nat.gcd.go(sp, Nat.sub(1n+yp, x), Nat.cmp(x, Nat.sub(1n+yp, x)), x)) : Nat}
              %NL.mul_sub_right(1n+yp, x, 1n+kp, NL.cmp_gt_of_lt(x, 1n+yp, Equal.sym(Cmp, LT{}, Nat.cmp(x, 1n+yp), e))) : {NL.Nat.gcd.go(sp, _, Nat.cmp(Nat.mul(x, 1n+kp), _), Nat.mul(x, 1n+kp)) == Nat.mul(1n+kp, NL.Nat.gcd.go(sp, Nat.sub(1n+yp, x), Nat.cmp(x, Nat.sub(1n+yp, x)), x)) : Nat}
              NL.gcd.go.scale(sp, Nat.sub(1n+yp, x), Nat.cmp(x, Nat.sub(1n+yp, x)), x, kp, {==})
            case GT{}:
              %NL.cmp_mul_right_of(x, 1n+yp, kp, GT{}, e) : {NL.Nat.gcd.go(1n+sp, Nat.mul(1n+yp, 1n+kp), _, Nat.mul(x, 1n+kp)) == Nat.mul(1n+kp, NL.Nat.gcd.go(sp, 1n+yp, Nat.cmp(Nat.sub(x, 1n+yp), 1n+yp), Nat.sub(x, 1n+yp))) : Nat}
              %NL.mul_sub_right(x, 1n+yp, 1n+kp, Equal.sym(Cmp, GT{}, Nat.cmp(x, 1n+yp), e)) : {NL.Nat.gcd.go(sp, Nat.mul(1n+yp, 1n+kp), Nat.cmp(_, Nat.mul(1n+yp, 1n+kp)), _) == Nat.mul(1n+kp, NL.Nat.gcd.go(sp, 1n+yp, Nat.cmp(Nat.sub(x, 1n+yp), 1n+yp), Nat.sub(x, 1n+yp))) : Nat}
              NL.gcd.go.scale(sp, 1n+yp, Nat.cmp(Nat.sub(x, 1n+yp), 1n+yp), Nat.sub(x, 1n+yp), kp, {==})

# gcd.slack_lt: from cmp(1+xp, 1+yp) = LT, cmp_lt_sub_add gives
# (yp - xp) + (1+xp) = 1+yp; peeling the successor off both sides (add_succ,
# then succ_inj) turns that into (yp - xp) + xp = yp, which is what the
# shuffle needs. The shuffle then reassociates
#   (1+xp + S) + (xp+t) -> 1+xp + (S + (xp+t)) -> 1+xp + ((S+xp) + t)
#                       -> 1+xp + (yp + t) -> ((1+xp) + yp) + t
# with S = yp - xp; the last step reads add_succ (1 + (xp+yp) = xp + (1+yp))
# backwards, since xp + (1+yp) is how the loop spells the state's y slot.
def NL.gcd.slack_lt(xp, yp, t, e):
  %NL.add_assoc_rev(1n+xp, Nat.sub(yp, xp), Nat.add(xp, t)) : {_ == Nat.add(Nat.add(xp, 1n+yp), t) : Nat}
  %NL.add_assoc(Nat.sub(yp, xp), xp, t) : {Nat.add(1n+xp, _) == Nat.add(Nat.add(xp, 1n+yp), t) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(yp, xp), xp), yp,
    NL.succ_inj(Nat.add(Nat.sub(yp, xp), xp), yp,
      Equal.trans(Nat,
        Nat.add(1n, Nat.add(Nat.sub(yp, xp), xp)),
        Nat.add(Nat.sub(yp, xp), 1n+xp),
        Nat.add(1n, yp),
        NL.add_succ(Nat.sub(yp, xp), xp),
        NL.cmp_lt_sub_add(1n+xp, 1n+yp, e))))
    : {Nat.add(1n+xp, Nat.add(_, t)) == Nat.add(Nat.add(xp, 1n+yp), t) : Nat}
  %NL.add_succ(xp, yp) : {Nat.add(1n+xp, Nat.add(yp, t)) == Nat.add(_, t) : Nat}
  %NL.add_assoc(1n+xp, yp, t) : {_ == Nat.add(Nat.add(1n+xp, yp), t) : Nat}
  {==}

# gcd.slack_gt: the mirror. cmp_gt_sub_add gives (xp - yp) + (1+yp) = 1+xp and
# sub_pos rewrites xp - yp as 1 + (xp - (1+yp)), so after succ_inj
# (xp - (1+yp)) + (1+yp) = xp -- exactly the fact that collapses the state's
# x slot (1 + (xp - (1+yp))) back to xp. The rest is the same shuffle as
# slack_lt, ending with add_succ and add_assoc.
def NL.gcd.slack_gt(xp, yp, t, e):
  %Equal.sym(Nat, Nat.add(Nat.sub(xp, 1n+yp), 1n+yp), xp,
    NL.succ_inj(Nat.add(Nat.sub(xp, 1n+yp), 1n+yp), xp,
      Equal.trans(Nat,
        Nat.add(1n, Nat.add(Nat.sub(xp, 1n+yp), 1n+yp)),
        Nat.add(Nat.sub(xp, yp), 1n+yp),
        Nat.add(1n, xp),
        Equal.sym(Nat, Nat.add(Nat.sub(xp, yp), 1n+yp), Nat.add(1n+Nat.sub(xp, 1n+yp), 1n+yp),
          Equal.cong(Nat, Nat, u => Nat.add(u, 1n+yp), Nat.sub(xp, yp), 1n+Nat.sub(xp, 1n+yp), NL.sub_pos(xp, yp, e))),
        NL.cmp_gt_sub_add(1n+xp, 1n+yp, e))))
    : {Nat.add(1n, Nat.add(_, Nat.add(yp, t))) == Nat.add(Nat.add(xp, 1n+yp), t) : Nat}
  %NL.add_succ(xp, yp) : {Nat.add(1n+xp, Nat.add(yp, t)) == Nat.add(_, t) : Nat}
  %NL.add_assoc(1n+xp, yp, t) : {_ == Nat.add(Nat.add(1n+xp, yp), t) : Nat}
  {==}

# A successor-headed Nat is never 0; proof machinery only (no law statement
# mentions it), so it lives here with NatIsPos -- and, like Nat.pred, bare
# rather than NL-prefixed: an NL-prefixed name belongs to nat.bend's namespace
# and only the *fills* of its laws resolve from there.
def Nat.succ_add_ne_zero(xp: Nat, y: Nat, t: Nat, e: {Nat.add(Nat.add(1n+xp, y), t) == 0n : Nat}) -> Empty:
  %e : NatIsPos(_)
  Unit{}

# gcd.go.fuel: induction on s1. The s1 = 0 branch is impossible -- e2 would
# make a successor-headed Nat 0 -- and every other branch is the loop's own
# step, after which the induction hypothesis applies at the new state with the
# slack identity (gcd.slack_lt / gcd.slack_gt) as its fuel hypothesis and the
# same u. The two fuel rewrites never appear because the loop peels one
# successor off s1 = 1 + sp on both sides at once.
def NL.gcd.go.fuel(s1, y, c, xp, t, u, e1, e2):
  match s1:
    case 0n:
      Empty.absurd({NL.Nat.gcd.go(Nat.add(0n, u), y, c, 1n+xp) == NL.Nat.gcd.go(0n, y, c, 1n+xp) : Nat},
        Nat.succ_add_ne_zero(xp, y, t, e2))
    case 1n+sp:
      match y:
        case 0n:
          {==}
        case 1n+yp:
          match c:
            case EQ{}:
              {==}
            case LT{}:
              NL.gcd.go.fuel(sp, Nat.sub(1n+yp, 1n+xp), Nat.cmp(1n+xp, Nat.sub(1n+yp, 1n+xp)), xp, Nat.add(xp, t), u, {==},
                Equal.trans(Nat,
                  Nat.add(Nat.add(1n+xp, Nat.sub(1n+yp, 1n+xp)), Nat.add(xp, t)),
                  Nat.add(Nat.add(xp, 1n+yp), t),
                  sp,
                  NL.gcd.slack_lt(xp, yp, t, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, 1n+yp), e1)),
                  NL.succ_inj(Nat.add(Nat.add(xp, 1n+yp), t), sp, e2)))
            case GT{}:
              %Equal.sym(Nat, Nat.sub(xp, yp), 1n+Nat.sub(xp, 1n+yp), NL.sub_pos(xp, yp, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, 1n+yp), e1))) : {NL.Nat.gcd.go(Nat.add(sp, u), 1n+yp, Nat.cmp(_, 1n+yp), _) == NL.Nat.gcd.go(sp, 1n+yp, Nat.cmp(_, 1n+yp), _) : Nat}
              NL.gcd.go.fuel(sp, 1n+yp, Nat.cmp(1n+Nat.sub(xp, 1n+yp), 1n+yp), Nat.sub(xp, 1n+yp), Nat.add(yp, t), u, {==},
                Equal.trans(Nat,
                  Nat.add(Nat.add(1n+Nat.sub(xp, 1n+yp), 1n+yp), Nat.add(yp, t)),
                  Nat.add(Nat.add(xp, 1n+yp), t),
                  sp,
                  NL.gcd.slack_gt(xp, yp, t, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, 1n+yp), e1)),
                  NL.succ_inj(Nat.add(Nat.add(xp, 1n+yp), t), sp, e2)))

# gcd_scale: the top level, and the reason gcd.go.scale and gcd.go.fuel both
# exist. Nat.gcd(m*k, d*k) runs the loop with fuel m*k + d*k and Nat.gcd(m, d)
# with fuel m + d, so the two loops cannot be matched directly; the sequence is
#   1. gcd.go.scale at the scaled fuel, which relates the scaled state to the
#      unscaled one at that same (over-large) fuel;
#   2. add_mul_slack, which says that fuel is m + d plus a slack;
#   3. gcd.go.fuel, which throws the slack away;
#   4. Nat.mul_comm, because the loop scaling puts k on the left of the
#      product and the statement has it on the right.
def NL.gcd_scale(m, d, kp):
  match m:
    case 0n:
      {==}
    case 1n+mp:
      %Equal.sym(Nat,
        NL.Nat.gcd.go(Nat.add(Nat.mul(1n+mp, 1n+kp), Nat.mul(d, 1n+kp)), Nat.mul(d, 1n+kp), Nat.cmp(Nat.mul(1n+mp, 1n+kp), Nat.mul(d, 1n+kp)), Nat.mul(1n+mp, 1n+kp)),
        Nat.mul(1n+kp, NL.Nat.gcd.go(Nat.add(Nat.mul(1n+mp, 1n+kp), Nat.mul(d, 1n+kp)), d, Nat.cmp(1n+mp, d), 1n+mp)),
        NL.gcd.go.scale(Nat.add(Nat.mul(1n+mp, 1n+kp), Nat.mul(d, 1n+kp)), d, Nat.cmp(1n+mp, d), 1n+mp, kp, {==}))
        : {_ == Nat.mul(NL.Nat.gcd.go(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), 1n+mp), 1n+kp) : Nat}
      %NL.add_mul_slack(1n+mp, d, kp) : {Nat.mul(1n+kp, NL.Nat.gcd.go(_, d, Nat.cmp(1n+mp, d), 1n+mp)) == Nat.mul(NL.Nat.gcd.go(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), 1n+mp), 1n+kp) : Nat}
      %Equal.sym(Nat,
        NL.Nat.gcd.go(Nat.add(Nat.add(1n+mp, d), Nat.add(Nat.mul(1n+mp, kp), Nat.mul(d, kp))), d, Nat.cmp(1n+mp, d), 1n+mp),
        NL.Nat.gcd.go(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), 1n+mp),
        NL.gcd.go.fuel(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), mp, 0n, Nat.add(Nat.mul(1n+mp, kp), Nat.mul(d, kp)), {==}, NL.add_zero(Nat.add(1n+mp, d))))
        : {Nat.mul(1n+kp, _) == Nat.mul(NL.Nat.gcd.go(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), 1n+mp), 1n+kp) : Nat}
      %NL.mul_comm(1n+kp, NL.Nat.gcd.go(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), 1n+mp)) : {Nat.mul(1n+kp, NL.Nat.gcd.go(Nat.add(1n+mp, d), d, Nat.cmp(1n+mp, d), 1n+mp)) == _ : Nat}
      {==}

def NL.divides_add(g, q1, q2, a, b, p1, p2):
  Equal.trans(Nat, Nat.add(a, b), Nat.add(Nat.mul(g, q1), b), Nat.mul(g, Nat.add(q1, q2)),
    Equal.cong(Nat, Nat, u => Nat.add(u, b), a, Nat.mul(g, q1), p1),
    Equal.trans(Nat, Nat.add(Nat.mul(g, q1), b), Nat.add(Nat.mul(g, q1), Nat.mul(g, q2)), Nat.mul(g, Nat.add(q1, q2)),
      Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(g, q1), u), b, Nat.mul(g, q2), p2),
      NL.mul_distrib(g, q1, q2)))

# gcd divides both arguments
# ==========================
#
# gcd.divides_lt / gcd.divides_gt: one loop step, as a function from the
# induction hypothesis's witness pair to the step's goal. Both destructure the
# pair into its two Nat.Div witnesses, take each witness apart into (quotient,
# equation), and hand back the *old* half unchanged -- rebuilt from the fields
# it just took apart -- next to the new one, whose equation is divides_add with
# the two quotients added.
#
# The rebuild is the whole reason Nat.Div exists: q1, q2, p1 and p2 are each
# read twice (once into the rebuilt witness, once into divides_add), which a
# Sigma's linear fields could not do. Here the pattern is plain -- a +field
# comes out Many without any `+` marker -- and the destructure pattern is the
# ADT's own constructor (a `(q, e) = d` pair pattern would be Tuple, and the
# checker would look for a Tuple of the wrong type).
def NL.gcd.divides_lt(g, x, s, y, d, e):
  (d1, d2) = d
  NL.Div{q2, p2} = d1
  NL.Div{q1, p1} = d2
  (NL.Div{q2, p2}, NL.Div{Nat.add(q1, q2), Equal.trans(Nat, y, Nat.add(s, x), Nat.mul(g, Nat.add(q1, q2)),
    Equal.sym(Nat, Nat.add(s, x), y, e),
    NL.divides_add(g, q1, q2, s, x, p1, p2))})

# gcd.divides_gt: the mirror. The pair covers (1+xp, y), so the rebuilt half
# is the *second* one (the y slot of the step, which the loop leaves alone) and
# the new half is the first (the difference).
def NL.gcd.divides_gt(g, xp, y, x, d, e):
  (d1, d2) = d
  NL.Div{q1, p1} = d1
  NL.Div{q2, p2} = d2
  (NL.Div{Nat.add(q1, q2), Equal.trans(Nat, x, Nat.add(1n+xp, y), Nat.mul(g, Nat.add(q1, q2)),
    Equal.sym(Nat, Nat.add(1n+xp, y), x, e),
    NL.divides_add(g, q1, q2, 1n+xp, y, p1, p2))},
   NL.Div{q2, p2})

# gcd.go.divides: induction on the fuel s, exactly like gcd.go.fuel, and for
# the same reason -- every recursive call is one step of the loop, and the
# induction hypothesis is the *pair* the step helper wants as its d parameter,
# so it is passed straight in with no destructure of a computed value.
#
# s = 0: impossible. Nat.gcd.go answers 0 there and e2 would make
# (1+xp + y) + t zero, so the goal is vacuous -- Nat.succ_add_ne_zero turns e2
# into Empty and Empty.absurd closes it. The goal has to be spelled with the
# loop term unfolded because `Nat.gcd.go(0n, ..)` is what the checker reduces
# the goal's head to.
#
# y = 0 and c = EQ: no step happens, the loop answers the x slot 1 + xp, so the
# goal is "1+xp divides 1+xp and y". The y half needs the equation to be turned
# around: mul_one proves {1+xp == 1+xp*1}, and the goal wants {y == 1+xp*1}
# with y = 1+xp (EQ) or y = 0 (the y = 0 branch, where mul_zero gives the same
# thing with 0 on the left).
def NL.gcd.go.divides(s, y, c, xp, t, e1, e2):
  match s:
    case 0n:
      Empty.absurd(NL.Nat.divides_both(NL.Nat.gcd.go(0n, y, c, 1n+xp), 1n+xp, y),
        Nat.succ_add_ne_zero(xp, y, t, e2))
    case 1n+sp:
      match y:
        case 0n:
          (NL.Div{1n, NL.mul_one(1n+xp)},
           NL.Div{0n, Equal.sym(Nat, Nat.mul(1n+xp, 0n), 0n, NL.mul_zero(1n+xp))})
        case 1n+yp:
          match c:
            case EQ{}:
              (NL.Div{1n, NL.mul_one(1n+xp)},
               NL.Div{1n, Equal.trans(Nat, 1n+yp, 1n+xp, Nat.mul(1n+xp, 1n),
                 Equal.sym(Nat, 1n+xp, 1n+yp, NL.cmp_eq(1n+xp, 1n+yp, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, 1n+yp), e1))),
                 NL.mul_one(1n+xp))})
            # LT: the loop's next state is (1+xp, (1+yp) - (1+xp)) at fuel sp --
            # the x slot is unchanged, so the induction hypothesis's x slot is
            # 1+xp again and the helper's equation is cmp_lt_sub_add, which is
            # literally {(y - x) + x == y}. The fuel hypothesis is the same
            # transport gcd.go.fuel uses: (slack_lt says the new state plus
            # (xp + t) is the old state plus t, and one successor comes off
            # both sides, which is why the new slack is xp + t).
            case LT{}:
              NL.gcd.divides_lt(
                NL.Nat.gcd.go(sp, Nat.sub(1n+yp, 1n+xp), Nat.cmp(1n+xp, Nat.sub(1n+yp, 1n+xp)), 1n+xp),
                1n+xp, Nat.sub(1n+yp, 1n+xp), 1n+yp,
                NL.gcd.go.divides(sp, Nat.sub(1n+yp, 1n+xp), Nat.cmp(1n+xp, Nat.sub(1n+yp, 1n+xp)), xp, Nat.add(xp, t), {==},
                  Equal.trans(Nat,
                    Nat.add(Nat.add(1n+xp, Nat.sub(1n+yp, 1n+xp)), Nat.add(xp, t)),
                    Nat.add(Nat.add(xp, 1n+yp), t),
                    sp,
                    NL.gcd.slack_lt(xp, yp, t, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, 1n+yp), e1)),
                    NL.succ_inj(Nat.add(Nat.add(xp, 1n+yp), t), sp, e2))),
                NL.cmp_lt_sub_add(1n+xp, 1n+yp, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, 1n+yp), e1)))
            # GT: the next state is ((1+xp) - (1+yp), 1+yp) and the y slot is
            # unchanged, so the pair the helper consumes is the *rewritten*
            # (1 + (xp - (1+yp)), 1+yp) -- note the second component is a
            # successor, which is exactly the spelling gcd.divides_gt's d
            # parameter demands. The x slot of the recursive call must be
            # 1 + (xp - (1+yp)) for a different reason -- a constructor, so the
            # call's own fuel 1+xp' + y reduces -- and that is what the sub_pos
            # rewrite below is for: it replaces the goal's stuck Nat.sub(xp, yp)
            # with exactly that spelling, in both places the loop term mentions
            # it.
            #
            # The helper's equation is then NOT cmp_gt_sub_add (whose
            # subtraction is (1+xp) - (1+yp) = xp - yp, a different term):
            # with the x slot rewritten it is ge_sub_add, one successor added
            # to both sides by Equal.cong.
            case GT{}:
              %Equal.sym(Nat, Nat.sub(xp, yp), 1n+Nat.sub(xp, 1n+yp),
                NL.sub_pos(xp, yp, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, 1n+yp), e1)))
                : NL.Nat.divides_both(NL.Nat.gcd.go(sp, 1n+yp, Nat.cmp(_, 1n+yp), _), 1n+xp, 1n+yp)
              NL.gcd.divides_gt(
                NL.Nat.gcd.go(sp, 1n+yp, Nat.cmp(1n+Nat.sub(xp, 1n+yp), 1n+yp), 1n+Nat.sub(xp, 1n+yp)),
                Nat.sub(xp, 1n+yp), 1n+yp, 1n+xp,
                NL.gcd.go.divides(sp, 1n+yp, Nat.cmp(1n+Nat.sub(xp, 1n+yp), 1n+yp), Nat.sub(xp, 1n+yp), Nat.add(yp, t), {==},
                  Equal.trans(Nat,
                    Nat.add(Nat.add(1n+Nat.sub(xp, 1n+yp), 1n+yp), Nat.add(yp, t)),
                    Nat.add(Nat.add(xp, 1n+yp), t),
                    sp,
                    NL.gcd.slack_gt(xp, yp, t, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, 1n+yp), e1)),
                    NL.succ_inj(Nat.add(Nat.add(xp, 1n+yp), t), sp, e2))),
                Equal.cong(Nat, Nat, u => 1n+u, Nat.add(Nat.sub(xp, 1n+yp), 1n+yp), xp,
                  NL.ge_sub_add(xp, 1n+yp, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, 1n+yp), e1))))

# gcd_divides: the top level. a = 0 hands the loop a state it never sees
# (Nat.gcd answers b directly), so the two witnesses are the trivial ones:
# b divides 0 with quotient 0, and b divides b with quotient 1. a = 1 + ap is
# gcd.go.divides at t = 0 -- the state's fuel a + b is (a + b) + 0.
def NL.gcd_divides(a, b):
  match a:
    case 0n:
      (NL.Div{0n, Equal.sym(Nat, Nat.mul(b, 0n), 0n, NL.mul_zero(b))},
       NL.Div{1n, NL.mul_one(b)})
    case 1n+ap:
      NL.gcd.go.divides(Nat.add(1n+ap, b), b, Nat.cmp(1n+ap, b), ap, 0n, {==}, NL.add_zero(Nat.add(1n+ap, b)))

# div_scale: write g as 1 + (g - 1) (pos_witness, from the positivity
# hypothesis), then the two sides of the goal are div_exact_mul and div_exact at
# the same q -- both take the same re-spelled witness.
def NL.div_scale(mag, g, kp, w, p):
  NL.Div{q, em} = w
  %Equal.sym(Nat, g, 1n+Nat.sub(g, 1n), NL.pos_witness(g, p))
    : {Nat.div(Nat.mul(mag, 1n+kp), Nat.mul(_, 1n+kp)) == Nat.div(mag, _) : Nat}
  Equal.trans(Nat,
    Nat.div(Nat.mul(mag, 1n+kp), Nat.mul(1n+Nat.sub(g, 1n), 1n+kp)),
    q,
    Nat.div(mag, 1n+Nat.sub(g, 1n)),
    NL.div_exact_mul(mag, Nat.sub(g, 1n), q, kp,
      Equal.trans(Nat, mag, Nat.mul(g, q), Nat.mul(1n+Nat.sub(g, 1n), q),
        em,
        Equal.cong(Nat, Nat, u => Nat.mul(u, q), g, 1n+Nat.sub(g, 1n), NL.pos_witness(g, p)))),
    Equal.sym(Nat, Nat.div(mag, 1n+Nat.sub(g, 1n)), q,
      NL.div_exact(mag, Nat.sub(g, 1n), q,
        Equal.trans(Nat, mag, Nat.mul(g, q), Nat.mul(1n+Nat.sub(g, 1n), q),
          em,
          Equal.cong(Nat, Nat, u => Nat.mul(u, q), g, 1n+Nat.sub(g, 1n), NL.pos_witness(g, p))))))

# divides_pos_wit: take the witness apart, spell the dividend as 1 + ap with
# pos_witness, and hand the two to divides_pos.
def NL.divides_pos_wit(g, a, w, p):
  NL.Div{q, e} = w
  NL.divides_pos(g, q, Nat.sub(a, 1n),
    Equal.trans(Nat, 1n+Nat.sub(a, 1n), a, Nat.mul(g, q),
      Equal.sym(Nat, a, 1n+Nat.sub(a, 1n), NL.pos_witness(a, p)),
      e))

def NL.mul_pos_right(g, q, ap, e):
  match q:
    case 0n:
      Empty.absurd({Nat.cmp(0n, 0n) == LT{} : Cmp},
        Nat.pos_ne_zero(ap,
          Equal.trans(Nat, 1n+ap, Nat.mul(g, 0n), 0n, e, NL.mul_zero(g))))
    case 1n+qp:
      {==}

# div_pos_wit: the witness gives div(1+ap, g) = q (div_exact, once g is written
# as the successor pos_witness provides), so the goal is cmp(0, q) = LT, which
# is mul_pos_right at the same witness.
def NL.div_pos_wit(g, ap, w):
  NL.Div{q, e} = w
  %Equal.sym(Nat, g, 1n+Nat.sub(g, 1n),
    NL.pos_witness(g, NL.divides_pos_wit(g, 1n+ap, w, {==})))
    : {Nat.cmp(0n, Nat.div(1n+ap, _)) == LT{} : Cmp}
  %Equal.sym(Nat, Nat.div(1n+ap, 1n+Nat.sub(g, 1n)), q,
    NL.div_exact(1n+ap, Nat.sub(g, 1n), q,
      Equal.trans(Nat, 1n+ap, Nat.mul(g, q), Nat.mul(1n+Nat.sub(g, 1n), q),
        e,
        Equal.cong(Nat, Nat, u => Nat.mul(u, q), g, 1n+Nat.sub(g, 1n),
          NL.pos_witness(g, NL.divides_pos_wit(g, 1n+ap, w, {==}))))))
    : {Nat.cmp(0n, _) == LT{} : Cmp}
  NL.mul_pos_right(g, q, ap, e)

# div_self_scale: div_exact wants the dividend as mul(1n+b, q), and the product
# the goal holds is mul(q, 1n+b) -- so the two sides are related by mul_comm
# alone, with the middle term left in the dividend spelling div_exact asks for.
def NL.div_self_scale(q, b):
  NL.div_exact(Nat.mul(q, 1n+b), b, q,
    Equal.trans(Nat,
      Nat.mul(q, 1n+b),
      Nat.mul(1n+b, q),
      Nat.mul(1n+b, q),
      NL.mul_comm(q, 1n+b),
      Equal.cong(Nat, Nat, u => Nat.mul(u, q), 1n+b, 1n+b, {==})))
