import Base

# Nat lemmas
# ==========
#
# The arithmetic inventory base.bend does not ship. All lemmas are
# proved by structural induction on the first argument, with % rewrites
# oriented so no Equal.sym is ever needed.

# add_zero: x + 0 = x
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# add_succ: 1 + (a + b) = a + (1 + b)  (stated flipped so rewrites fire left-to-right)
law add_succ:
  for a: Nat
  for b: Nat
  {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %add_succ(ap, b) : {1n+1n+Nat.add(ap, b) == 1n+_ : Nat}
      {==}

# add_comm: a + b = b + a
law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      %add_zero(b) : {_ == Nat.add(b, 0n) : Nat}
      {==}
    case 1n+ap:
      %add_succ(b, ap) : {1n+Nat.add(ap, b) == _ : Nat}
      %add_comm(ap, b) : {1n+Nat.add(ap, b) == 1n+_ : Nat}
      {==}

# add_assoc: (a + b) + c = a + (b + c)
law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %add_assoc(ap, b, c) : {1n+Nat.add(Nat.add(ap, b), c) == 1n+_ : Nat}
      {==}

# add_exchange: a + (b + c) = b + (a + c)
law add_exchange:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_exchange(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %add_succ(b, Nat.add(ap, c)) : {1n+Nat.add(ap, Nat.add(b, c)) == _ : Nat}
      %add_exchange(ap, b, c) : {1n+Nat.add(ap, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# mul_zero: x * 0 = 0
law mul_zero:
  for +x: Nat
  {Nat.mul(x, 0n) == 0n : Nat}

def mul_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

# mul_succ: a + a*b = a*(1 + b)  (stated flipped so rewrites fire left-to-right)
law mul_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}

def mul_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %mul_succ(ap, b) : {1n+Nat.add(ap, Nat.add(b, Nat.mul(ap, b))) == 1n+Nat.add(b, _) : Nat}
      %add_exchange(ap, b, Nat.mul(ap, b)) : {1n+Nat.add(ap, Nat.add(b, Nat.mul(ap, b))) == 1n+_ : Nat}
      {==}

# mul_comm: a * b = b * a
law mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def mul_comm(a, b):
  match a:
    case 0n:
      %mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n+ap:
      %mul_succ(b, ap) : {Nat.add(b, Nat.mul(ap, b)) == _ : Nat}
      %mul_comm(ap, b) : {Nat.add(b, Nat.mul(ap, b)) == Nat.add(b, _) : Nat}
      {==}

# Comparison bridges
# ==================
#
# Nat.cmp returns a bare Cmp with no evidence. These lemmas reconnect a
# cmp result to arithmetic facts, so proofs that hit a stuck cmp can
# case-split on it.

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

# Constructor discrimination: distinct Cmp constructors are never equal.
law lt_ne_eq:
  for e: {LT{} == EQ{} : Cmp}
  Empty

def lt_ne_eq(e):
  %Equal.sym(Cmp, LT{}, EQ{}, e) : CmpIsEQ(_)
  Unit{}

law gt_ne_eq:
  for e: {GT{} == EQ{} : Cmp}
  Empty

def gt_ne_eq(e):
  %Equal.sym(Cmp, GT{}, EQ{}, e) : CmpIsEQ(_)
  Unit{}

law eq_ne_gt:
  for e: {EQ{} == GT{} : Cmp}
  Empty

def eq_ne_gt(e):
  %Equal.sym(Cmp, EQ{}, GT{}, e) : CmpIsGT(_)
  Unit{}

law lt_ne_gt:
  for e: {LT{} == GT{} : Cmp}
  Empty

def lt_ne_gt(e):
  %Equal.sym(Cmp, LT{}, GT{}, e) : CmpIsGT(_)
  Unit{}

# cmp_eq: if cmp(a,b) is EQ then a == b
law cmp_eq:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {a == b : Nat}

def cmp_eq(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, lt_ne_eq(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, gt_ne_eq(e))
    case 1n+ap 1n+bp:
      %cmp_eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

# Cmp.flip: swap LT and GT
def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case EQ{}:
      EQ{}
    case LT{}:
      GT{}
    case GT{}:
      LT{}

# cmp_antisym: comparing swapped arguments flips the result
law cmp_antisym:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, b) == Cmp.flip(Nat.cmp(b, a)) : Cmp}

def cmp_antisym(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cmp_antisym(ap, bp)

# cmp_gt_sub_add: if cmp(a,b) is GT then (a - b) + b = a
law cmp_gt_sub_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

def cmp_gt_sub_add(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.add(Nat.sub(0n, 0n), 0n) == 0n : Nat}, eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+bp), 1n+bp) == 0n : Nat}, lt_ne_gt(e))
    case 1n+ap 0n:
      add_zero(1n+ap)
    case 1n+ap 1n+bp:
      %add_succ(Nat.sub(ap, bp), bp) : {_ == 1n+ap : Nat}
      %cmp_gt_sub_add(ap, bp, e) : {1n+Nat.add(Nat.sub(ap, bp), bp) == 1n+_ : Nat}
      {==}

# add_comm_succ: a + (1+b) = b + (1+a)
law add_comm_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == Nat.add(b, 1n+a) : Nat}

def add_comm_succ(a, b):
  %add_succ(a, b) : {_ == Nat.add(b, 1n+a) : Nat}
  %add_succ(b, a) : {1n+Nat.add(a, b) == _ : Nat}
  %add_comm(a, b) : {1n+Nat.add(a, b) == 1n+_ : Nat}
  {==}

# add_assoc_rev: a + (b + c) = (a + b) + c  (flipped twin of add_assoc)
law add_assoc_rev:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

def add_assoc_rev(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c))

# mul_distrib: a*b + a*c = a*(b + c)  (stated flipped)
law mul_distrib:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}

def mul_distrib(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %mul_distrib(ap, b, c) : {Nat.add(Nat.add(b, Nat.mul(ap, b)), Nat.add(c, Nat.mul(ap, c))) == Nat.add(Nat.add(b, c), _) : Nat}
      Equal.trans(Nat,
        Nat.add(Nat.add(b, Nat.mul(ap, b)), Nat.add(c, Nat.mul(ap, c))),
        Nat.add(b, Nat.add(Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c)))),
        Nat.add(Nat.add(b, c), Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
        add_assoc(b, Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c))),
        Equal.trans(Nat,
          Nat.add(b, Nat.add(Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c)))),
          Nat.add(b, Nat.add(c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c)))),
          Nat.add(Nat.add(b, c), Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
          Equal.cong(Nat, Nat, x => Nat.add(b, x),
            Nat.add(Nat.mul(ap, b), Nat.add(c, Nat.mul(ap, c))),
            Nat.add(c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
            add_exchange(Nat.mul(ap, b), c, Nat.mul(ap, c))),
          Equal.sym(Nat,
            Nat.add(Nat.add(b, c), Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))),
            Nat.add(b, Nat.add(c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c)))),
            add_assoc(b, c, Nat.add(Nat.mul(ap, b), Nat.mul(ap, c))))))

# mul_add_left: x*z + y*z = (x + y)*z
law mul_add_left:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.add(Nat.mul(x, z), Nat.mul(y, z)) == Nat.mul(Nat.add(x, y), z) : Nat}

def mul_add_left(x, y, z):
  match x:
    case 0n:
      {==}
    case 1n+xp:
      %add_assoc_rev(z, Nat.mul(xp, z), Nat.mul(y, z)) : {_ == Nat.add(z, Nat.mul(Nat.add(xp, y), z)) : Nat}
      %mul_add_left(xp, y, z) : {Nat.add(z, Nat.add(Nat.mul(xp, z), Nat.mul(y, z))) == Nat.add(z, _) : Nat}
      {==}

# mul_assoc: (a * b) * c = a * (b * c)
law mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %mul_add_left(b, Nat.mul(ap, b), c) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(ap, Nat.mul(b, c))) : Nat}
      %mul_assoc(ap, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(ap, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# Truncated subtraction and ordering library
# ==========================================
#
# Lemmas about Nat.sub (truncated) and Nat.cmp, needed for the
# sign-magnitude Int.add_assoc proof. Evidence conventions: a hypothesis
# {Nat.cmp(a, b) == GT{} : Cmp} is a law parameter; %e : P rewrites the
# goal's RHS-of-e occurrences with the LHS (see PROVING.md).

# sub_zero: a - 0 = a
law sub_zero:
  for +a: Nat
  {Nat.sub(a, 0n) == a : Nat}

def sub_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      {==}

# sub_self: a - a = 0
law sub_self:
  for +a: Nat
  {Nat.sub(a, a) == 0n : Nat}

def sub_self(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      sub_self(ap)

# add_sub_cancel: (a + b) - b = a
law add_sub_cancel:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), b) == a : Nat}

def add_sub_cancel(a, b):
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      %Equal.sym(Nat, Nat.sub(a, 0n), a, sub_zero(a)) : {_ == a : Nat}
      {==}
    case 1n+bp:
      %add_succ(a, bp) : {Nat.sub(_, 1n+bp) == a : Nat}
      add_sub_cancel(a, bp)

# sub_add: a - (b + c) = (a - b) - c  (holds unconditionally for truncated sub)
law sub_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.sub(a, Nat.add(b, c)) == Nat.sub(Nat.sub(a, b), c) : Nat}

def sub_add(a, b, c):
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
      sub_add(ap, bp, 0n)
    case 1n+ap 1n+bp 1n+cp:
      sub_add(ap, bp, 1n+cp)

# sub_sub_swap: (c - a) - b = (c - b) - a
law sub_sub_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.sub(Nat.sub(c, a), b) == Nat.sub(Nat.sub(c, b), a) : Nat}

def sub_sub_swap(a, b, c):
  %sub_add(c, a, b) : {_ == Nat.sub(Nat.sub(c, b), a) : Nat}
  %sub_add(c, b, a) : {Nat.sub(c, Nat.add(a, b)) == _ : Nat}
  %add_comm(a, b) : {Nat.sub(c, Nat.add(a, b)) == Nat.sub(c, _) : Nat}
  {==}

# eq_ne_lt / gt_ne_lt: remaining Cmp discriminations
law eq_ne_lt:
  for e: {EQ{} == LT{} : Cmp}
  Empty

def eq_ne_lt(e):
  %e : CmpIsEQ(_)
  Unit{}

law gt_ne_lt:
  for e: {GT{} == LT{} : Cmp}
  Empty

def gt_ne_lt(e):
  %e : CmpIsGT(_)
  Unit{}

# cmp_refl: cmp(a, a) = EQ
law cmp_refl:
  for +a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

def cmp_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      cmp_refl(ap)

# cmp_lt_add: a < (1+b) + a
law cmp_lt_add:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, Nat.add(1n+b, a)) == LT{} : Cmp}

def cmp_lt_add(a, b):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %add_succ(b, ap) : {Nat.cmp(ap, _) == LT{} : Cmp}
      cmp_lt_add(ap, b)

# cmp_gt_add: (1+b) + a > a
law cmp_gt_add:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.add(1n+b, a), a) == GT{} : Cmp}

def cmp_gt_add(a, b):
  %Equal.sym(Cmp, Nat.cmp(Nat.add(1n+b, a), a), Cmp.flip(Nat.cmp(a, Nat.add(1n+b, a))), cmp_antisym(Nat.add(1n+b, a), a)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(a, Nat.add(1n+b, a)), LT{}, cmp_lt_add(a, b)) : {Cmp.flip(_) == GT{} : Cmp}
  {==}

# cmp_add_right: adding the same k to both sides preserves cmp
law cmp_add_right:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  {Nat.cmp(Nat.add(a, k), Nat.add(b, k)) == Nat.cmp(a, b) : Cmp}

def cmp_add_right(a, b, k):
  match a b:
    case 0n 0n:
      cmp_refl(k)
    case 0n 1n+bp:
      cmp_lt_add(k, bp)
    case 1n+ap 0n:
      cmp_gt_add(k, ap)
    case 1n+ap 1n+bp:
      cmp_add_right(ap, bp, k)

# cmp_gt_succ: a > b -> 1+a > b
law cmp_gt_succ:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(1n+a, b) == GT{} : Cmp}

def cmp_gt_succ(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(1n, 0n) == GT{} : Cmp}, eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(1n, 1n+bp) == GT{} : Cmp}, lt_ne_gt(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cmp_gt_succ(ap, bp, e)

# cmp_gt_refl_succ: 1+a > a
law cmp_gt_refl_succ:
  for +a: Nat
  {Nat.cmp(1n+a, a) == GT{} : Cmp}

def cmp_gt_refl_succ(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      cmp_gt_refl_succ(ap)

# cmp_gt_sub: a > b -> a > b - c
law cmp_gt_sub:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(a, Nat.sub(b, c)) == GT{} : Cmp}

def cmp_gt_sub(a, b, c, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.sub(0n, c)) == GT{} : Cmp}, eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(0n, Nat.sub(1n+bp, c)) == GT{} : Cmp}, lt_ne_gt(e))
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
          cmp_gt_succ(ap, Nat.sub(bp, cp), cmp_gt_sub(ap, bp, cp, e))

# cmp_lt_sub: z > y -> y - x < z
law cmp_lt_sub:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for e: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(y, x), z) == LT{} : Cmp}

def cmp_lt_sub(x, y, z, e):
  %Equal.sym(Cmp, Nat.cmp(Nat.sub(y, x), z), Cmp.flip(Nat.cmp(z, Nat.sub(y, x))), cmp_antisym(Nat.sub(y, x), z)) : {_ == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(z, Nat.sub(y, x)), GT{}, cmp_gt_sub(z, y, x, e)) : {Cmp.flip(_) == LT{} : Cmp}
  {==}

# cmp_gt_add_left: b > c -> a + b > c
law cmp_gt_add_left:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(b, c) == GT{} : Cmp}
  {Nat.cmp(Nat.add(a, b), c) == GT{} : Cmp}

def cmp_gt_add_left(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+ap:
      cmp_gt_succ(Nat.add(ap, b), c, cmp_gt_add_left(ap, b, c, e))

# cmp_lt_add_r: a < b -> a < b + c
law cmp_lt_add_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.cmp(a, Nat.add(b, c)) == LT{} : Cmp}

def cmp_lt_add_r(a, b, c, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.add(0n, c)) == LT{} : Cmp}, eq_ne_lt(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.cmp(1n+ap, Nat.add(0n, c)) == LT{} : Cmp}, gt_ne_lt(e))
    case 1n+ap 1n+bp:
      cmp_lt_add_r(ap, bp, c, e)

# cmp_lt_succ_r: a < b -> a < 1 + b
law cmp_lt_succ_r:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.cmp(a, 1n+b) == LT{} : Cmp}

def cmp_lt_succ_r(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, 1n) == LT{} : Cmp}, eq_ne_lt(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.cmp(1n+ap, 1n) == LT{} : Cmp}, gt_ne_lt(e))
    case 1n+ap 1n+bp:
      cmp_lt_succ_r(ap, bp, e)

# cmp_lt_succ_self: a < 1 + a
law cmp_lt_succ_self:
  for +a: Nat
  {Nat.cmp(a, 1n+a) == LT{} : Cmp}

def cmp_lt_succ_self(a):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      cmp_lt_succ_self(ap)

# cmp_sub_lt: a > 1+b -> a - (1+b) < a
law cmp_sub_lt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, 1n+b) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(a, 1n+b), a) == LT{} : Cmp}

def cmp_sub_lt(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(Nat.sub(0n, 1n), 0n) == LT{} : Cmp}, lt_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(Nat.sub(0n, 2n+bp), 0n) == LT{} : Cmp}, lt_ne_gt(e))
    case 1n+ap 0n:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, sub_zero(ap)) : {Nat.cmp(_, 1n+ap) == LT{} : Cmp}
      cmp_lt_succ_self(ap)
    case 1n+ap 1n+bp:
      cmp_lt_succ_r(Nat.sub(ap, 1n+bp), ap, cmp_sub_lt(ap, bp, e))

# cmp_lt_sub_add: cmp(a,b) = LT -> (b - a) + a = b  (LT twin of cmp_gt_sub_add)
law cmp_lt_sub_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.add(Nat.sub(b, a), a) == b : Nat}

def cmp_lt_sub_add(a, b, e):
  cmp_gt_sub_add(b, a,
    Equal.trans(Cmp, Nat.cmp(b, a), Cmp.flip(Nat.cmp(a, b)), GT{},
      cmp_antisym(b, a),
      Equal.sym(Cmp, GT{}, Cmp.flip(Nat.cmp(a, b)),
        Equal.cong(Cmp, Cmp, Cmp.flip, LT{}, Nat.cmp(a, b),
          Equal.sym(Cmp, Nat.cmp(a, b), LT{}, e)))))

# cmp_eq_sub_add: cmp(a,b) = EQ -> (a - b) + b = a
law cmp_eq_sub_add:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

def cmp_eq_sub_add(a, b, e):
  %cmp_eq(a, b, e) : {Nat.add(Nat.sub(a, _), b) == a : Nat}
  %cmp_eq(a, b, e) : {Nat.add(Nat.sub(a, a), _) == a : Nat}
  %Equal.sym(Nat, Nat.sub(a, a), 0n, sub_self(a)) : {Nat.add(_, a) == a : Nat}
  {==}

# flip_eq_lt: flip(c) = LT -> c = GT
law flip_eq_lt:
  for +c: Cmp
  for e: {Cmp.flip(c) == LT{} : Cmp}
  {c == GT{} : Cmp}

def flip_eq_lt(c, e):
  match c:
    case EQ{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, eq_ne_lt(e))
    case LT{}:
      Empty.absurd({LT{} == GT{} : Cmp}, gt_ne_lt(e))
    case GT{}:
      {==}

# sub_pos: a > b -> a - b = 1 + (a - (1+b))
law sub_pos:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.sub(a, b) == 1n+Nat.sub(a, 1n+b) : Nat}

def sub_pos(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.sub(0n, 0n) == 1n+Nat.sub(0n, 1n) : Nat}, eq_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.sub(0n, 1n+bp) == 1n+Nat.sub(0n, 2n+bp) : Nat}, lt_ne_gt(e))
    case 1n+ap 0n:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, sub_zero(ap)) : {1n+ap == 1n+_ : Nat}
      {==}
    case 1n+ap 1n+bp:
      sub_pos(ap, bp, e)

# cmp_add_sub: z > y -> cmp(x + y, z) = cmp(x, z - y)
law cmp_add_sub:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for e: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.cmp(Nat.add(x, y), z) == Nat.cmp(x, Nat.sub(z, y)) : Cmp}

def cmp_add_sub(x, y, z, e):
  %cmp_gt_sub_add(z, y, e) : {Nat.cmp(Nat.add(x, y), _) == Nat.cmp(x, Nat.sub(z, y)) : Cmp}
  cmp_add_right(x, Nat.sub(z, y), y)

# cmp_sub_add: a > c -> cmp(a - c, b) = cmp(a, c + b)
law cmp_sub_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, c) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(a, c), b) == Nat.cmp(a, Nat.add(c, b)) : Cmp}

def cmp_sub_add(a, b, c, e):
  %cmp_gt_sub_add(a, c, e) : {Nat.cmp(Nat.sub(a, c), b) == Nat.cmp(_, Nat.add(c, b)) : Cmp}
  %add_comm(b, c) : {Nat.cmp(Nat.sub(a, c), b) == Nat.cmp(Nat.add(Nat.sub(a, c), c), _) : Cmp}
  Equal.sym(Cmp, Nat.cmp(Nat.add(Nat.sub(a, c), c), Nat.add(b, c)), Nat.cmp(Nat.sub(a, c), b), cmp_add_right(Nat.sub(a, c), b, c))

# cmp_add_same_left: cmp(a, a + b) = cmp(0, b)
law cmp_add_same_left:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, Nat.add(a, b)) == Nat.cmp(0n, b) : Cmp}

def cmp_add_same_left(a, b):
  %add_comm(b, a) : {Nat.cmp(a, _) == Nat.cmp(0n, b) : Cmp}
  cmp_add_right(0n, b, a)

# cmp_sub_flip: c > a, c > b -> cmp(c - a, b) = flip(cmp(a, c - b))
law cmp_sub_flip:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ea: {Nat.cmp(c, a) == GT{} : Cmp}
  for eb: {Nat.cmp(c, b) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(c, a), b) == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}

def cmp_sub_flip(a, b, c, ea, eb):
  %cmp_add_right(Nat.sub(c, a), b, a) : {_ == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %Equal.sym(Nat, Nat.add(Nat.sub(c, a), a), c, cmp_gt_sub_add(c, a, ea)) : {Nat.cmp(_, Nat.add(b, a)) == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %Equal.sym(Cmp, Nat.cmp(c, Nat.add(b, a)), Cmp.flip(Nat.cmp(Nat.add(b, a), c)), cmp_antisym(c, Nat.add(b, a))) : {_ == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %add_comm(a, b) : {Cmp.flip(Nat.cmp(_, c)) == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %cmp_gt_sub_add(c, b, eb) : {Cmp.flip(Nat.cmp(Nat.add(a, b), _)) == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(a, b), Nat.add(Nat.sub(c, b), b)), Nat.cmp(a, Nat.sub(c, b)), cmp_add_right(a, Nat.sub(c, b), b)) : {Cmp.flip(_) == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}
  {==}

# Nat.pred: predecessor (0 maps to 0)
def Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# succ_inj: 1+a = 1+b -> a = b
law succ_inj:
  for +a: Nat
  for +b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
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

# succ_add_ne: k = (1+b) + k is impossible
law succ_add_ne:
  for +b: Nat
  for +k: Nat
  for e: {k == Nat.add(1n+b, k) : Nat}
  Empty

def succ_add_ne(b, k, e):
  match k:
    case 0n:
      %Equal.sym(Nat, 0n, Nat.add(1n+b, 0n), e) : NatIsPos(_)
      Unit{}
    case 1n+kp:
      succ_add_ne(b, kp,
        Equal.trans(Nat, kp, Nat.add(b, 1n+kp), 1n+Nat.add(b, kp),
          succ_inj(kp, Nat.add(b, 1n+kp), e),
          Equal.sym(Nat, 1n+Nat.add(b, kp), Nat.add(b, 1n+kp), add_succ(b, kp))))

# add_cancel: a + k = b + k -> a = b
law add_cancel:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for e: {Nat.add(a, k) == Nat.add(b, k) : Nat}
  {a == b : Nat}

def add_cancel(a, b, k, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, succ_add_ne(bp, k, e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat},
        succ_add_ne(ap, k, Equal.sym(Nat, Nat.add(1n+ap, k), Nat.add(0n, k), e)))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, x => 1n+x, ap, bp,
        add_cancel(ap, bp, k, succ_inj(Nat.add(ap, k), Nat.add(bp, k), e)))

# cmp_lt_of_sub_lt: x > c, x - c < b -> x < c + b
law cmp_lt_of_sub_lt:
  for +b: Nat
  for +c: Nat
  for +x: Nat
  for e1: {Nat.cmp(x, c) == GT{} : Cmp}
  for e2: {Nat.cmp(Nat.sub(x, c), b) == LT{} : Cmp}
  {Nat.cmp(x, Nat.add(c, b)) == LT{} : Cmp}

def cmp_lt_of_sub_lt(b, c, x, e1, e2):
  %cmp_gt_sub_add(x, c, e1) : {Nat.cmp(_, Nat.add(c, b)) == LT{} : Cmp}
  %add_comm(b, c) : {Nat.cmp(Nat.add(Nat.sub(x, c), c), _) == LT{} : Cmp}
  Equal.trans(Cmp, Nat.cmp(Nat.add(Nat.sub(x, c), c), Nat.add(b, c)), Nat.cmp(Nat.sub(x, c), b), LT{},
    cmp_add_right(Nat.sub(x, c), b, c), e2)

# cmp_zero_gt: cmp(0, x) = GT is impossible
law cmp_zero_gt:
  for +x: Nat
  for e: {Nat.cmp(0n, x) == GT{} : Cmp}
  Empty

def cmp_zero_gt(x, e):
  match x:
    case 0n:
      eq_ne_gt(e)
    case 1n+xp:
      lt_ne_gt(e)

# ge_sub_add: a >= b (stated as 1+a > b) -> (a - b) + b = a
law ge_sub_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(1n+a, b) == GT{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

def ge_sub_add(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+bp), 1n+bp) == 0n : Nat}, cmp_zero_gt(bp, e))
    case 1n+ap 0n:
      add_zero(1n+ap)
    case 1n+ap 1n+bp:
      %add_succ(Nat.sub(ap, bp), bp) : {_ == 1n+ap : Nat}
      %ge_sub_add(ap, bp, e) : {1n+Nat.add(Nat.sub(ap, bp), bp) == 1n+_ : Nat}
      {==}

# ci1aux .. ci1: a >= b, c > b -> (a - b) + c = a + (c - b)
# (via cancellation of b on the right; a >= b is stated as cmp(1+a, b) = GT)
law ci1aux:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(1n+a, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(c, b) == GT{} : Cmp}
  {Nat.add(Nat.add(Nat.sub(a, b), c), b) == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}

def ci1aux(a, b, c, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.sub(a, b), c), b), Nat.add(Nat.sub(a, b), Nat.add(c, b)), add_assoc(Nat.sub(a, b), c, b)) : {_ == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %add_comm(b, c) : {Nat.add(Nat.sub(a, b), _) == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, b), Nat.add(b, c)), Nat.add(Nat.add(Nat.sub(a, b), b), c), add_assoc_rev(Nat.sub(a, b), b, c)) : {_ == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, b), b), a, ge_sub_add(a, b, e1)) : {Nat.add(_, c) == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}
  %add_assoc_rev(a, Nat.sub(c, b), b) : {Nat.add(a, c) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(c, b), b), c, cmp_gt_sub_add(c, b, e2)) : {Nat.add(a, c) == Nat.add(a, _) : Nat}
  {==}

law ci1:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(1n+a, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(c, b) == GT{} : Cmp}
  {Nat.add(Nat.sub(a, b), c) == Nat.add(a, Nat.sub(c, b)) : Nat}

def ci1(a, b, c, e1, e2):
  add_cancel(Nat.add(Nat.sub(a, b), c), Nat.add(a, Nat.sub(c, b)), b, ci1aux(a, b, c, e1, e2))

# ci2aux .. ci2: a > c -> a - (a - c) = c  (via cancellation of a - c)
law ci2aux:
  for +a: Nat
  for +c: Nat
  for +e: {Nat.cmp(a, c) == GT{} : Cmp}
  {Nat.add(Nat.sub(1n+a, Nat.sub(a, c)), Nat.sub(a, c)) == Nat.add(1n+c, Nat.sub(a, c)) : Nat}

def ci2aux(a, c, e):
  %Equal.sym(Nat, Nat.add(Nat.sub(1n+a, Nat.sub(a, c)), Nat.sub(a, c)), 1n+a, cmp_gt_sub_add(1n+a, Nat.sub(a, c), cmp_gt_sub(1n+a, a, c, cmp_gt_refl_succ(a)))) : {_ == Nat.add(1n+c, Nat.sub(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(c, Nat.sub(a, c)), Nat.add(Nat.sub(a, c), c), add_comm(c, Nat.sub(a, c))) : {1n+a == 1n+_ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, c), c), a, cmp_gt_sub_add(a, c, e)) : {1n+a == 1n+_ : Nat}
  {==}

law ci2:
  for +a: Nat
  for +c: Nat
  for +e: {Nat.cmp(a, c) == GT{} : Cmp}
  {Nat.sub(a, Nat.sub(a, c)) == c : Nat}

def ci2(a, c, e):
  match a c:
    case 0n 0n:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 0n)) == 0n : Nat}, eq_ne_gt(e))
    case 0n 1n+cp:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+cp)) == 1n+cp : Nat}, lt_ne_gt(e))
    case 1n+ap 0n:
      sub_self(ap)
    case 1n+ap 1n+cp:
      add_cancel(Nat.sub(1n+ap, Nat.sub(ap, cp)), 1n+cp, Nat.sub(ap, cp), ci2aux(ap, cp, e))

# ci3aux .. ci3: y > x, y > z, y - x < z -> z - (y - x) = x - (y - z)
law ci3aux:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  for +e3: {Nat.cmp(Nat.sub(y, x), z) == LT{} : Cmp}
  {Nat.add(Nat.sub(z, Nat.sub(y, x)), y) == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}

def ci3aux(x, y, z, e1, e2, e3):
  %cmp_gt_sub_add(y, x, e1) : {Nat.add(Nat.sub(z, Nat.sub(y, x)), _) == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.add(Nat.sub(y, x), x)), Nat.add(Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), x), add_assoc_rev(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x), x)) : {_ == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), z, cmp_gt_sub_add(z, Nat.sub(y, x), Equal.trans(Cmp, Nat.cmp(z, Nat.sub(y, x)), Cmp.flip(Nat.cmp(Nat.sub(y, x), z)), GT{}, cmp_antisym(z, Nat.sub(y, x)), Equal.cong(Cmp, Cmp, Cmp.flip, Nat.cmp(Nat.sub(y, x), z), LT{}, e3)))) : {Nat.add(_, x) == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}
  %cmp_gt_sub_add(y, z, e2) : {Nat.add(z, x) == Nat.add(Nat.sub(x, Nat.sub(y, z)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.add(Nat.sub(y, z), z)), Nat.add(Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)), z), add_assoc_rev(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z), z)) : {Nat.add(z, x) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)), x, cmp_gt_sub_add(x, Nat.sub(y, z), flip_eq_lt(Nat.cmp(x, Nat.sub(y, z)), Equal.trans(Cmp, Cmp.flip(Nat.cmp(x, Nat.sub(y, z))), Nat.cmp(Nat.sub(y, x), z), LT{}, Equal.sym(Cmp, Nat.cmp(Nat.sub(y, x), z), Cmp.flip(Nat.cmp(x, Nat.sub(y, z))), cmp_sub_flip(x, z, y, e1, e2)), e3)))) : {Nat.add(z, x) == Nat.add(_, z) : Nat}
  add_comm(z, x)

law ci3:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  for +e3: {Nat.cmp(Nat.sub(y, x), z) == LT{} : Cmp}
  {Nat.sub(z, Nat.sub(y, x)) == Nat.sub(x, Nat.sub(y, z)) : Nat}

def ci3(x, y, z, e1, e2, e3):
  add_cancel(Nat.sub(z, Nat.sub(y, x)), Nat.sub(x, Nat.sub(y, z)), y, ci3aux(x, y, z, e1, e2, e3))

# ci4aux .. ci4: y > x, z > y -> z - (y - x) = x + (z - y)
law ci4aux:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.add(Nat.sub(z, Nat.sub(y, x)), y) == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}

def ci4aux(x, y, z, e1, e2):
  %cmp_gt_sub_add(y, x, e1) : {Nat.add(Nat.sub(z, Nat.sub(y, x)), _) == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.add(Nat.sub(y, x), x)), Nat.add(Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), x), add_assoc_rev(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x), x)) : {_ == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, Nat.sub(y, x)), Nat.sub(y, x)), z, cmp_gt_sub_add(z, Nat.sub(y, x), cmp_gt_sub(z, y, x, e2))) : {Nat.add(_, x) == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}
  %add_assoc_rev(x, Nat.sub(z, y), y) : {Nat.add(z, x) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(z, y), y), z, cmp_gt_sub_add(z, y, e2)) : {Nat.add(z, x) == Nat.add(x, _) : Nat}
  add_comm(z, x)

law ci4:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.sub(z, Nat.sub(y, x)) == Nat.add(x, Nat.sub(z, y)) : Nat}

def ci4(x, y, z, e1, e2):
  add_cancel(Nat.sub(z, Nat.sub(y, x)), Nat.add(x, Nat.sub(z, y)), y, ci4aux(x, y, z, e1, e2))

# ci5aux .. ci5: b > c -> (a + b) - c = a + (b - c)
law ci5aux:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e: {Nat.cmp(b, c) == GT{} : Cmp}
  {Nat.add(Nat.sub(Nat.add(a, b), c), c) == Nat.add(Nat.add(a, Nat.sub(b, c)), c) : Nat}

def ci5aux(a, b, c, e):
  %Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(a, b), c), c), Nat.add(a, b), cmp_gt_sub_add(Nat.add(a, b), c, cmp_gt_add_left(a, b, c, e))) : {_ == Nat.add(Nat.add(a, Nat.sub(b, c)), c) : Nat}
  %add_assoc_rev(a, Nat.sub(b, c), c) : {Nat.add(a, b) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(b, c), c), b, cmp_gt_sub_add(b, c, e)) : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

law ci5:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e: {Nat.cmp(b, c) == GT{} : Cmp}
  {Nat.sub(Nat.add(a, b), c) == Nat.add(a, Nat.sub(b, c)) : Nat}

def ci5(a, b, c, e):
  add_cancel(Nat.sub(Nat.add(a, b), c), Nat.add(a, Nat.sub(b, c)), c, ci5aux(a, b, c, e))

# ci6aux .. ci6: c > b, a + b > c -> (a + b) - c = a - (c - b)
law ci6aux:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(c, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.add(a, b), c) == GT{} : Cmp}
  {Nat.add(Nat.sub(Nat.add(a, b), c), c) == Nat.add(Nat.sub(a, Nat.sub(c, b)), c) : Nat}

def ci6aux(a, b, c, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(a, b), c), c), Nat.add(a, b), cmp_gt_sub_add(Nat.add(a, b), c, e2)) : {_ == Nat.add(Nat.sub(a, Nat.sub(c, b)), c) : Nat}
  %cmp_gt_sub_add(c, b, e1) : {Nat.add(a, b) == Nat.add(Nat.sub(a, Nat.sub(c, b)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, Nat.sub(c, b)), Nat.add(Nat.sub(c, b), b)), Nat.add(Nat.add(Nat.sub(a, Nat.sub(c, b)), Nat.sub(c, b)), b), add_assoc_rev(Nat.sub(a, Nat.sub(c, b)), Nat.sub(c, b), b)) : {Nat.add(a, b) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(a, Nat.sub(c, b)), Nat.sub(c, b)), a, cmp_gt_sub_add(a, Nat.sub(c, b), Equal.trans(Cmp, Nat.cmp(a, Nat.sub(c, b)), Nat.cmp(Nat.add(a, b), c), GT{}, Equal.sym(Cmp, Nat.cmp(Nat.add(a, b), c), Nat.cmp(a, Nat.sub(c, b)), cmp_add_sub(a, b, c, e1)), e2))) : {Nat.add(a, b) == Nat.add(_, b) : Nat}
  {==}

law ci6:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(c, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.add(a, b), c) == GT{} : Cmp}
  {Nat.sub(Nat.add(a, b), c) == Nat.sub(a, Nat.sub(c, b)) : Nat}

def ci6(a, b, c, e1, e2):
  add_cancel(Nat.sub(Nat.add(a, b), c), Nat.sub(a, Nat.sub(c, b)), c, ci6aux(a, b, c, e1, e2))

# ci7: c - (a + b) = (c - b) - a  (unconditional)
law ci7:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.sub(c, Nat.add(a, b)) == Nat.sub(Nat.sub(c, b), a) : Nat}

def ci7(a, b, c):
  %add_comm(b, a) : {Nat.sub(c, _) == Nat.sub(Nat.sub(c, b), a) : Nat}
  sub_add(c, b, a)

# ci9aux .. ci9: x > c, x - c < b -> (c + b) - x = b - (x - c)
law ci9aux:
  for +b: Nat
  for +c: Nat
  for +x: Nat
  for +e1: {Nat.cmp(x, c) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.sub(x, c), b) == LT{} : Cmp}
  {Nat.add(Nat.sub(Nat.add(c, b), x), x) == Nat.add(Nat.sub(b, Nat.sub(x, c)), x) : Nat}

def ci9aux(b, c, x, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(c, b), x), x), Nat.add(c, b), cmp_gt_sub_add(Nat.add(c, b), x, Equal.trans(Cmp, Nat.cmp(Nat.add(c, b), x), Cmp.flip(Nat.cmp(x, Nat.add(c, b))), GT{}, cmp_antisym(Nat.add(c, b), x), Equal.cong(Cmp, Cmp, Cmp.flip, Nat.cmp(x, Nat.add(c, b)), LT{}, cmp_lt_of_sub_lt(b, c, x, e1, e2))))) : {_ == Nat.add(Nat.sub(b, Nat.sub(x, c)), x) : Nat}
  %cmp_gt_sub_add(x, c, e1) : {Nat.add(c, b) == Nat.add(Nat.sub(b, Nat.sub(x, c)), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(b, Nat.sub(x, c)), Nat.add(Nat.sub(x, c), c)), Nat.add(Nat.add(Nat.sub(b, Nat.sub(x, c)), Nat.sub(x, c)), c), add_assoc_rev(Nat.sub(b, Nat.sub(x, c)), Nat.sub(x, c), c)) : {Nat.add(c, b) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(b, Nat.sub(x, c)), Nat.sub(x, c)), b, cmp_gt_sub_add(b, Nat.sub(x, c), Equal.trans(Cmp, Nat.cmp(b, Nat.sub(x, c)), Cmp.flip(Nat.cmp(Nat.sub(x, c), b)), GT{}, cmp_antisym(b, Nat.sub(x, c)), Equal.cong(Cmp, Cmp, Cmp.flip, Nat.cmp(Nat.sub(x, c), b), LT{}, e2)))) : {Nat.add(c, b) == Nat.add(_, c) : Nat}
  add_comm(c, b)

law ci9:
  for +b: Nat
  for +c: Nat
  for +x: Nat
  for +e1: {Nat.cmp(x, c) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.sub(x, c), b) == LT{} : Cmp}
  {Nat.sub(Nat.add(c, b), x) == Nat.sub(b, Nat.sub(x, c)) : Nat}

def ci9(b, c, x, e1, e2):
  add_cancel(Nat.sub(Nat.add(c, b), x), Nat.sub(b, Nat.sub(x, c)), x, ci9aux(b, c, x, e1, e2))

# ci10: 1+a > x -> (1 + (a + b)) - x = 1 + ((a - x) + b)
law ci10:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  for e: {Nat.cmp(1n+a, x) == GT{} : Cmp}
  {Nat.sub(1n+Nat.add(a, b), x) == 1n+Nat.add(Nat.sub(a, x), b) : Nat}

def ci10(a, b, x, e):
  match a x:
    case 0n 0n:
      {==}
    case 0n 1n+xp:
      Empty.absurd({Nat.sub(1n+Nat.add(0n, b), 1n+xp) == 1n+Nat.add(Nat.sub(0n, 1n+xp), b) : Nat}, cmp_zero_gt(xp, e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+xp:
      ci10(ap, b, xp, e)

# ci8aux .. ci8: x > y, y > z -> (x - y) + z = x - (y - z)
law ci8aux:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(x, y) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  {Nat.add(Nat.add(Nat.sub(x, y), z), Nat.sub(y, z)) == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}

def ci8aux(x, y, z, e1, e2):
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.sub(x, y), z), Nat.sub(y, z)), Nat.add(Nat.sub(x, y), Nat.add(z, Nat.sub(y, z))), add_assoc(Nat.sub(x, y), z, Nat.sub(y, z))) : {_ == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  %Equal.sym(Nat, Nat.add(z, Nat.sub(y, z)), Nat.add(Nat.sub(y, z), z), add_comm(z, Nat.sub(y, z))) : {Nat.add(Nat.sub(x, y), _) == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(y, z), z), y, cmp_gt_sub_add(y, z, e2)) : {Nat.add(Nat.sub(x, y), _) == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(x, y), y), x, cmp_gt_sub_add(x, y, e1)) : {_ == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}
  Equal.sym(Nat, Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)), x, cmp_gt_sub_add(x, Nat.sub(y, z), cmp_gt_sub(x, y, z, e1)))

law ci8:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(x, y) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  {Nat.add(Nat.sub(x, y), z) == Nat.sub(x, Nat.sub(y, z)) : Nat}

def ci8(x, y, z, e1, e2):
  add_cancel(Nat.add(Nat.sub(x, y), z), Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z), ci8aux(x, y, z, e1, e2))

# cmp_gt_of_lt / cmp_lt_of_gt: flip a comparison evidence
law cmp_gt_of_lt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.cmp(b, a) == GT{} : Cmp}

def cmp_gt_of_lt(a, b, e):
  Equal.trans(Cmp, Nat.cmp(b, a), Cmp.flip(Nat.cmp(a, b)), GT{},
    cmp_antisym(b, a),
    Equal.cong(Cmp, Cmp, Cmp.flip, Nat.cmp(a, b), LT{}, e))

law cmp_lt_of_gt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(b, a) == LT{} : Cmp}

def cmp_lt_of_gt(a, b, e):
  Equal.trans(Cmp, Nat.cmp(b, a), Cmp.flip(Nat.cmp(a, b)), LT{},
    cmp_antisym(b, a),
    Equal.cong(Cmp, Cmp, Cmp.flip, Nat.cmp(a, b), GT{}, e))

# flip_flip: flip is an involution
law flip_flip:
  for +c: Cmp
  {Cmp.flip(Cmp.flip(c)) == c : Cmp}

def flip_flip(c):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

# cmp_sub_gt_self: a > 1+b -> a > a - (1+b)
law cmp_sub_gt_self:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, 1n+b) == GT{} : Cmp}
  {Nat.cmp(a, Nat.sub(a, 1n+b)) == GT{} : Cmp}

def cmp_sub_gt_self(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.sub(0n, 1n)) == GT{} : Cmp}, lt_ne_gt(e))
    case 0n 1n+bp:
      Empty.absurd({Nat.cmp(0n, Nat.sub(0n, 2n+bp)) == GT{} : Cmp}, lt_ne_gt(e))
    case 1n+ap 0n:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, sub_zero(ap)) : {Nat.cmp(1n+ap, _) == GT{} : Cmp}
      cmp_gt_refl_succ(ap)
    case 1n+ap 1n+bp:
      cmp_gt_succ(ap, Nat.sub(ap, 1n+bp), cmp_sub_gt_self(ap, bp, e))

# cmp_lt_zero: cmp(a, 0) = LT is impossible
law cmp_lt_zero:
  for +a: Nat
  for e: {Nat.cmp(a, 0n) == LT{} : Cmp}
  Empty

def cmp_lt_zero(a, e):
  match a:
    case 0n:
      eq_ne_lt(e)
    case 1n+ap:
      gt_ne_lt(e)

# cmp_sub_flip_of: transport a cmp(c - a, b) result to flip of cmp(a, c - b)
law cmp_sub_flip_of:
  for +d: Cmp
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +ed: {d == Nat.cmp(Nat.sub(c, a), b) : Cmp}
  for +ea: {Nat.cmp(c, a) == GT{} : Cmp}
  for +eb: {Nat.cmp(c, b) == GT{} : Cmp}
  {Cmp.flip(d) == Nat.cmp(a, Nat.sub(c, b)) : Cmp}

def cmp_sub_flip_of(d, a, b, c, ed, ea, eb):
  Equal.trans(Cmp, Cmp.flip(d), Cmp.flip(Nat.cmp(Nat.sub(c, a), b)), Nat.cmp(a, Nat.sub(c, b)),
    Equal.cong(Cmp, Cmp, Cmp.flip, d, Nat.cmp(Nat.sub(c, a), b), ed),
    Equal.trans(Cmp, Cmp.flip(Nat.cmp(Nat.sub(c, a), b)), Cmp.flip(Cmp.flip(Nat.cmp(a, Nat.sub(c, b)))), Nat.cmp(a, Nat.sub(c, b)),
      Equal.cong(Cmp, Cmp, Cmp.flip, Nat.cmp(Nat.sub(c, a), b), Cmp.flip(Nat.cmp(a, Nat.sub(c, b))), cmp_sub_flip(a, b, c, ea, eb)),
      flip_flip(Nat.cmp(a, Nat.sub(c, b)))))
