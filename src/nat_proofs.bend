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
law CmpIsEQ:
  for c: Cmp
  Type

def CmpIsEQ(c):
  match c:
    case EQ{}:
      Unit
    case LT{}:
      Empty
    case GT{}:
      Empty

law CmpIsGT:
  for c: Cmp
  Type

def CmpIsGT(c):
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
law NatIsPos:
  for n: Nat
  Type

def NatIsPos(n):
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
