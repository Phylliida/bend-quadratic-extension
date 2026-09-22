import Base
import ./int.bend as I
import ./nat.bend as N
import ./nat_proofs.bend as NP

# Int proofs
# =========
#
# Fills every law of int.bend. Nat evidence is called through N (the
# nat.bend alias); the nat_proofs.bend import is what fills those laws
# (the fill attaches to the nat.bend module, so N.<lemma> resolves).

def I.xor_comm(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def I.Int.mul_comm(x, y):
  match x y:
    case I.Int{xs, xm} I.Int{ys, ym}:
      %I.xor_comm(xs, ys) : {I.Int.mk(Bool.xor(xs, ys), Nat.mul(xm, ym)) == I.Int.mk(_, Nat.mul(ym, xm)) : I.Int}
      %N.mul_comm(xm, ym) : {I.Int.mk(Bool.xor(xs, ys), Nat.mul(xm, ym)) == I.Int.mk(Bool.xor(xs, ys), _) : I.Int}
      {==}

def I.Int.add.opp_comm(c, xs, ys, xm, ym):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      {==}

def I.Int.add.same_comm(s, xm, ym):
  match xm ym:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      %N.add_zero(yp) : {I.Int{s, 1n+_} == I.Int{s, 1n+Nat.add(yp, 0n)} : I.Int}
      {==}
    case 1n+xp 0n:
      %N.add_zero(xp) : {I.Int{s, 1n+Nat.add(xp, 0n)} == I.Int{s, 1n+_} : I.Int}
      {==}
    case 1n+xp 1n+yp:
      %N.add_comm_succ(xp, yp) : {I.Int{s, 1n+Nat.add(xp, 1n+yp)} == I.Int{s, 1n+_} : I.Int}
      {==}

def I.Int.add_comm(x, y):
  match x y:
    case I.Int{False{}, xm} I.Int{False{}, ym}:
      I.Int.add.same_comm(False{}, xm, ym)
    case I.Int{True{}, xm} I.Int{True{}, ym}:
      I.Int.add.same_comm(True{}, xm, ym)
    case I.Int{False{}, xm} I.Int{True{}, ym}:
      %Equal.sym(Cmp, Nat.cmp(ym, xm), N.Cmp.flip(Nat.cmp(xm, ym)), N.cmp_antisym(ym, xm)) : {I.Int.add.opp(Nat.cmp(xm, ym), False{}, xm, True{}, ym) == I.Int.add.opp(_, True{}, ym, False{}, xm) : I.Int}
      I.Int.add.opp_comm(Nat.cmp(xm, ym), False{}, True{}, xm, ym)
    case I.Int{True{}, xm} I.Int{False{}, ym}:
      %Equal.sym(Cmp, Nat.cmp(ym, xm), N.Cmp.flip(Nat.cmp(xm, ym)), N.cmp_antisym(ym, xm)) : {I.Int.add.opp(Nat.cmp(xm, ym), True{}, xm, False{}, ym) == I.Int.add.opp(_, False{}, ym, True{}, xm) : I.Int}
      I.Int.add.opp_comm(Nat.cmp(xm, ym), True{}, False{}, xm, ym)

def I.xor_assoc(a, b, c):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def I.Int.mul.mk_left(s, m, ys, ym):
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def I.Int.mul.mk_right(xs, xm, s, m):
  match m:
    case 0n:
      %Equal.sym(Nat, Nat.mul(xm, 0n), 0n, N.mul_zero(xm)) : {I.Int.mk(Bool.xor(xs, s), _) == I.Int.mk(Bool.xor(xs, False{}), Nat.mul(xm, 0n)) : I.Int}
      %Equal.sym(Nat, Nat.mul(xm, 0n), 0n, N.mul_zero(xm)) : {I.Int.mk(Bool.xor(xs, s), 0n) == I.Int.mk(Bool.xor(xs, False{}), _) : I.Int}
      {==}
    case 1n+p:
      {==}

def I.Int.mul_assoc(x, y, z):
  match x y z:
    case I.Int{xs, xm} I.Int{ys, ym} I.Int{zs, zm}:
      %I.Int.mul.mk_right(xs, xm, Bool.xor(ys, zs), Nat.mul(ym, zm)) : {I.Int.mul(I.Int.mk(Bool.xor(xs, ys), Nat.mul(xm, ym)), I.Int{zs, zm}) == _ : I.Int}
      %I.Int.mul.mk_left(Bool.xor(xs, ys), Nat.mul(xm, ym), zs, zm) : {_ == I.Int.mk(Bool.xor(xs, Bool.xor(ys, zs)), Nat.mul(xm, Nat.mul(ym, zm))) : I.Int}
      %I.xor_assoc(xs, ys, zs) : {I.Int.mk(Bool.xor(Bool.xor(xs, ys), zs), Nat.mul(Nat.mul(xm, ym), zm)) == I.Int.mk(_, Nat.mul(xm, Nat.mul(ym, zm))) : I.Int}
      %N.mul_assoc(xm, ym, zm) : {I.Int.mk(Bool.xor(Bool.xor(xs, ys), zs), Nat.mul(Nat.mul(xm, ym), zm)) == I.Int.mk(Bool.xor(Bool.xor(xs, ys), zs), _) : I.Int}
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

def I.Int.add.assoc.fff(xm, ym, zm):
  match xm:
    case 0n:
      match ym:
        case 0n:
          match zm:
            case 0n:
              {==}
            case 1n+zp:
              {==}
        case 1n+yp:
          {==}
    case 1n+xp:
      match ym:
        case 0n:
          match zm:
            case 0n:
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{False{}, 1n+Nat.add(_, 0n)} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
              {==}
            case 1n+zp:
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{False{}, 1n+Nat.add(_, 1n+zp)} == I.Int{False{}, 1n+Nat.add(xp, 1n+zp)} : I.Int}
              {==}
        case 1n+yp:
          %Equal.sym(Nat, Nat.add(Nat.add(xp, 1n+yp), zm), Nat.add(xp, Nat.add(1n+yp, zm)), N.add_assoc(xp, 1n+yp, zm)) : {I.Int{False{}, 1n+_} == I.Int{False{}, 1n+Nat.add(xp, 1n+Nat.add(yp, zm))} : I.Int}
          {==}

def I.Int.add.assoc.ttt(xm, ym, zm):
  match xm:
    case 0n:
      match ym:
        case 0n:
          match zm:
            case 0n:
              {==}
            case 1n+zp:
              {==}
        case 1n+yp:
          {==}
    case 1n+xp:
      match ym:
        case 0n:
          match zm:
            case 0n:
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{True{}, 1n+Nat.add(_, 0n)} == I.Int{True{}, 1n+xp} : I.Int}
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{True{}, 1n+_} == I.Int{True{}, 1n+xp} : I.Int}
              {==}
            case 1n+zp:
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{True{}, 1n+Nat.add(_, 1n+zp)} == I.Int{True{}, 1n+Nat.add(xp, 1n+zp)} : I.Int}
              {==}
        case 1n+yp:
          %Equal.sym(Nat, Nat.add(Nat.add(xp, 1n+yp), zm), Nat.add(xp, Nat.add(1n+yp, zm)), N.add_assoc(xp, 1n+yp, zm)) : {I.Int{True{}, 1n+_} == I.Int{True{}, 1n+Nat.add(xp, 1n+Nat.add(yp, zm))} : I.Int}
          {==}

def I.Int.add.assoc.ftf.ltgt(d, xm, ym, zm, ed, e1, e2):
  match d:
    case EQ{}:
      %ed : {I.Int.add.opp(_, True{}, Nat.sub(ym, xm), False{}, zm) == I.Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      %N.cmp_sub_flip_of(EQ{}, xm, zm, ym, ed, e1, e2) : {I.Int.add.opp(EQ{}, True{}, Nat.sub(ym, xm), False{}, zm) == I.Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      {==}
    case LT{}:
      %ed : {I.Int.add.opp(_, True{}, Nat.sub(ym, xm), False{}, zm) == I.Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      %N.cmp_sub_flip_of(LT{}, xm, zm, ym, ed, e1, e2) : {I.Int.add.opp(LT{}, True{}, Nat.sub(ym, xm), False{}, zm) == I.Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, Nat.sub(ym, xm)), Nat.sub(xm, Nat.sub(ym, zm)), N.ci3(xm, ym, zm, e1, e2, Equal.sym(Cmp, LT{}, Nat.cmp(Nat.sub(ym, xm), zm), ed))) : {I.Int{False{}, _} == I.Int{False{}, Nat.sub(xm, Nat.sub(ym, zm))} : I.Int}
      {==}
    case GT{}:
      %ed : {I.Int.add.opp(_, True{}, Nat.sub(ym, xm), False{}, zm) == I.Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      %N.cmp_sub_flip_of(GT{}, xm, zm, ym, ed, e1, e2) : {I.Int.add.opp(GT{}, True{}, Nat.sub(ym, xm), False{}, zm) == I.Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.sub(ym, xm), zm), Nat.sub(Nat.sub(ym, zm), xm), N.sub_sub_swap(xm, zm, ym)) : {I.Int{True{}, _} == I.Int{True{}, Nat.sub(Nat.sub(ym, zm), xm)} : I.Int}
      {==}

def I.Int.add.assoc.ftf(c1, c2, xm, ym, zm, e1, e2):
  match c1 c2:
    case GT{} GT{}:
      %e1 : {I.Int.add(I.Int.add.opp(_, False{}, xm, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, xm}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add(I.Int{False{}, Nat.sub(xm, ym)}, I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, xm}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(xm, Nat.sub(ym, zm)), GT{}, N.cmp_gt_sub(xm, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1))) : {I.Int.add.same(False{}, Nat.sub(xm, ym), zm) == I.Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(xm, ym), 1n+Nat.sub(xm, 1n+ym), N.sub_pos(xm, ym, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1))) : {I.Int.add.same(False{}, _, zm) == I.Int{False{}, Nat.sub(xm, Nat.sub(ym, zm))} : I.Int}
      %N.ci8(xm, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1), Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)) : {I.Int{False{}, 1n+Nat.add(Nat.sub(xm, 1n+ym), zm)} == I.Int{False{}, _} : I.Int}
      %Equal.sym(Nat, Nat.sub(xm, ym), 1n+Nat.sub(xm, 1n+ym), N.sub_pos(xm, ym, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1))) : {I.Int{False{}, 1n+Nat.add(Nat.sub(xm, 1n+ym), zm)} == I.Int{False{}, Nat.add(_, zm)} : I.Int}
      {==}
    case GT{} LT{}:
      match xm:
        case 0n:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add(I.Int.add.opp(GT{}, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          Empty.absurd({I.Int.add(I.Int.add.opp(GT{}, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(LT{}, True{}, ym, False{}, zm)) : I.Int}, N.cmp_zero_gt(ym, Equal.sym(Cmp, GT{}, Nat.cmp(0n, ym), e1)))
        case 1n+xp:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add.same(False{}, Nat.sub(1n+xp, ym), zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          %Equal.sym(Nat, Nat.sub(1n+xp, ym), 1n+Nat.sub(1n+xp, 1n+ym), N.sub_pos(1n+xp, ym, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1))) : {I.Int.add.same(False{}, _, zm) == I.Int{False{}, 1n+Nat.add(xp, Nat.sub(zm, ym))} : I.Int}
          %Equal.sym(Nat, Nat.add(Nat.sub(xp, ym), zm), Nat.add(xp, Nat.sub(zm, ym)), N.ci1(xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1), N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {I.Int{False{}, 1n+_} == I.Int{False{}, 1n+Nat.add(xp, Nat.sub(zm, ym))} : I.Int}
          {==}
    case GT{} EQ{}:
      match xm:
        case 0n:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add(I.Int.add.opp(GT{}, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          Empty.absurd({I.Int.add(I.Int.add.opp(GT{}, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(EQ{}, True{}, ym, False{}, zm)) : I.Int}, N.cmp_zero_gt(ym, Equal.sym(Cmp, GT{}, Nat.cmp(0n, ym), e1)))
        case 1n+xp:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add.same(False{}, Nat.sub(1n+xp, ym), zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          %Equal.sym(Nat, Nat.sub(1n+xp, ym), 1n+Nat.sub(1n+xp, 1n+ym), N.sub_pos(1n+xp, ym, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1))) : {I.Int.add.same(False{}, _, zm) == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int{False{}, 1n+Nat.add(Nat.sub(xp, ym), _)} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %Equal.sym(Nat, Nat.add(Nat.sub(xp, ym), ym), xp, N.ge_sub_add(xp, ym, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1))) : {I.Int{False{}, 1n+_} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{False{}, 1n+xp} == I.Int{False{}, 1n+_} : I.Int}
          {==}
    case EQ{} GT{}:
      match zm:
        case 0n:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, xm, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, xm}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 0n})) : I.Int}
          %e2 : {I.Int.add(I.Int{False{}, 0n}, I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, xm}, I.Int.add.opp(_, True{}, ym, False{}, 0n)) : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {I.Int{False{}, 0n} == I.Int.add.opp(Nat.cmp(xm, _), False{}, xm, True{}, Nat.sub(ym, 0n)) : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {I.Int{False{}, 0n} == I.Int.add.opp(Nat.cmp(xm, ym), False{}, xm, True{}, _) : I.Int}
          %e1 : {I.Int{False{}, 0n} == I.Int.add.opp(_, False{}, xm, True{}, ym) : I.Int}
          {==}
        case 1n+zp:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, xm, True{}, ym), I.Int{False{}, 1n+zp}) == I.Int.add(I.Int{False{}, xm}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 1n+zp})) : I.Int}
          %e2 : {I.Int.add.same(False{}, 0n, 1n+zp) == I.Int.add(I.Int{False{}, xm}, I.Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : I.Int}
          %Equal.sym(Cmp, Nat.cmp(xm, Nat.sub(ym, 1n+zp)), GT{},
            Equal.trans(Cmp, Nat.cmp(xm, Nat.sub(ym, 1n+zp)), Nat.cmp(ym, Nat.sub(ym, 1n+zp)), GT{},
              Equal.cong(Nat, Cmp, t => Nat.cmp(t, Nat.sub(ym, 1n+zp)), xm, ym, N.cmp_eq(xm, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(xm, ym), e1))),
              N.cmp_sub_gt_self(ym, zp, Equal.sym(Cmp, GT{}, Nat.cmp(ym, 1n+zp), e2))))
            : {I.Int{False{}, 1n+zp} == I.Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, 1n+zp)) : I.Int}
          %Equal.sym(Nat, xm, ym, N.cmp_eq(xm, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(xm, ym), e1))) : {I.Int{False{}, 1n+zp} == I.Int{False{}, Nat.sub(_, Nat.sub(ym, 1n+zp))} : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, Nat.sub(ym, 1n+zp)), 1n+zp, N.ci2(ym, 1n+zp, Equal.sym(Cmp, GT{}, Nat.cmp(ym, 1n+zp), e2))) : {I.Int{False{}, 1n+zp} == I.Int{False{}, _} : I.Int}
          {==}
    case EQ{} LT{}:
      match xm:
        case 0n:
          match zm:
            case 0n:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 0n})) : I.Int}
              %e2 : {I.Int.add.same(False{}, 0n, 0n) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, 0n)) : I.Int}
              Empty.absurd({I.Int.add(I.Int.add.opp(EQ{}, False{}, 0n, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(LT{}, True{}, ym, False{}, 0n)) : I.Int}, N.cmp_lt_zero(ym, Equal.sym(Cmp, LT{}, Nat.cmp(ym, 0n), e2)))
            case 1n+zp:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, 1n+zp}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 1n+zp})) : I.Int}
              %e2 : {I.Int.add.same(False{}, 0n, 1n+zp) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : I.Int}
              %Equal.sym(Nat, Nat.sub(1n+zp, ym), 1n+Nat.sub(1n+zp, 1n+ym), N.sub_pos(1n+zp, ym, N.cmp_gt_of_lt(ym, 1n+zp, Equal.sym(Cmp, LT{}, Nat.cmp(ym, 1n+zp), e2)))) : {I.Int{False{}, 1n+zp} == I.Int.mk(False{}, _) : I.Int}
              %N.cmp_eq(0n, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(0n, ym), e1)) : {I.Int{False{}, 1n+zp} == I.Int{False{}, 1n+Nat.sub(zp, _)} : I.Int}
              %Equal.sym(Nat, Nat.sub(zp, 0n), zp, N.sub_zero(zp)) : {I.Int{False{}, 1n+zp} == I.Int{False{}, 1n+_} : I.Int}
              {==}
        case 1n+xp:
          match zm:
            case 0n:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 0n})) : I.Int}
              %e2 : {I.Int.add.same(False{}, 0n, 0n) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, 0n)) : I.Int}
              Empty.absurd({I.Int.add(I.Int.add.opp(EQ{}, False{}, 1n+xp, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(LT{}, True{}, ym, False{}, 0n)) : I.Int}, N.cmp_lt_zero(ym, Equal.sym(Cmp, LT{}, Nat.cmp(ym, 0n), e2)))
            case 1n+zp:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, 1n+zp}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 1n+zp})) : I.Int}
              %e2 : {I.Int.mk(False{}, 1n+zp) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : I.Int}
              %N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1)) : {I.Int{False{}, 1n+zp} == I.Int{False{}, 1n+Nat.add(xp, Nat.sub(1n+zp, _))} : I.Int}
              %Equal.trans(Nat, zp, Nat.add(Nat.sub(zp, xp), xp), Nat.add(xp, Nat.sub(zp, xp)),
                Equal.sym(Nat, Nat.add(Nat.sub(zp, xp), xp), zp, N.cmp_lt_sub_add(xp, zp,
                  Equal.trans(Cmp, Nat.cmp(1n+xp, 1n+zp), Nat.cmp(ym, 1n+zp), LT{},
                    Equal.cong(Nat, Cmp, t => Nat.cmp(t, 1n+zp), 1n+xp, ym, N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1))),
                    Equal.sym(Cmp, LT{}, Nat.cmp(ym, 1n+zp), e2)))),
                N.add_comm(Nat.sub(zp, xp), xp))
                : {I.Int{False{}, 1n+zp} == I.Int{False{}, 1n+_} : I.Int}
              {==}
    case LT{} GT{}:
      %e1 : {I.Int.add(I.Int.add.opp(_, False{}, xm, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, xm}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add(I.Int{True{}, Nat.sub(ym, xm)}, I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, xm}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      I.Int.add.assoc.ftf.ltgt(Nat.cmp(Nat.sub(ym, xm), zm), xm, ym, zm, {==},
        N.cmp_gt_of_lt(xm, ym, Equal.sym(Cmp, LT{}, Nat.cmp(xm, ym), e1)),
        Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2))
    case LT{} LT{}:
      match xm:
        case 0n:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add(I.Int{True{}, Nat.sub(ym, 0n)}, I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          %Equal.sym(Cmp, Nat.cmp(Nat.sub(ym, 0n), zm), LT{}, N.cmp_lt_sub(0n, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {I.Int.add.opp(_, True{}, Nat.sub(ym, 0n), False{}, zm) == I.Int.add.same(False{}, 0n, Nat.sub(zm, ym)) : I.Int}
          %Equal.sym(Nat, Nat.sub(zm, ym), 1n+Nat.sub(zm, 1n+ym), N.sub_pos(zm, ym, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {I.Int{False{}, Nat.sub(zm, Nat.sub(ym, 0n))} == I.Int.mk(False{}, _) : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {I.Int{False{}, Nat.sub(zm, _)} == I.Int{False{}, 1n+Nat.sub(zm, 1n+ym)} : I.Int}
          %Equal.sym(Nat, Nat.sub(zm, ym), 1n+Nat.sub(zm, 1n+ym), N.sub_pos(zm, ym, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {I.Int{False{}, _} == I.Int{False{}, 1n+Nat.sub(zm, 1n+ym)} : I.Int}
          {==}
        case 1n+xp:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add(I.Int{True{}, Nat.sub(ym, 1n+xp)}, I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          %Equal.sym(Cmp, Nat.cmp(Nat.sub(ym, 1n+xp), zm), LT{}, N.cmp_lt_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {I.Int.add.opp(_, True{}, Nat.sub(ym, 1n+xp), False{}, zm) == I.Int.add.same(False{}, 1n+xp, Nat.sub(zm, ym)) : I.Int}
          %Equal.sym(Nat, Nat.sub(zm, Nat.sub(ym, 1n+xp)), Nat.add(1n+xp, Nat.sub(zm, ym)), N.ci4(1n+xp, ym, zm, N.cmp_gt_of_lt(1n+xp, ym, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, ym), e1)), N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {I.Int{False{}, _} == I.Int{False{}, 1n+Nat.add(xp, Nat.sub(zm, ym))} : I.Int}
          {==}
    case LT{} EQ{}:
      match xm:
        case 0n:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add(I.Int{True{}, Nat.sub(ym, 0n)}, I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int.add.opp(Nat.cmp(Nat.sub(ym, 0n), _), True{}, Nat.sub(ym, 0n), False{}, zm) == I.Int{False{}, 0n} : I.Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int.add.opp(Nat.cmp(Nat.sub(ym, 0n), ym), True{}, Nat.sub(ym, 0n), False{}, _) == I.Int{False{}, 0n} : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {I.Int.add.opp(Nat.cmp(_, ym), True{}, Nat.sub(ym, 0n), False{}, ym) == I.Int{False{}, 0n} : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {I.Int.add.opp(Nat.cmp(ym, ym), True{}, _, False{}, ym) == I.Int{False{}, 0n} : I.Int}
          %Equal.sym(Cmp, Nat.cmp(ym, ym), EQ{}, N.cmp_refl(ym)) : {I.Int.add.opp(_, True{}, ym, False{}, ym) == I.Int{False{}, 0n} : I.Int}
          {==}
        case 1n+xp:
          %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
          %e2 : {I.Int.add(I.Int{True{}, Nat.sub(ym, 1n+xp)}, I.Int{False{}, zm}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int.add.opp(Nat.cmp(Nat.sub(ym, 1n+xp), _), True{}, Nat.sub(ym, 1n+xp), False{}, zm) == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int.add.opp(Nat.cmp(Nat.sub(ym, 1n+xp), ym), True{}, Nat.sub(ym, 1n+xp), False{}, _) == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %Equal.sym(Cmp, Nat.cmp(Nat.sub(ym, 1n+xp), ym), LT{}, N.cmp_sub_lt(ym, xp, N.cmp_gt_of_lt(1n+xp, ym, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, ym), e1)))) : {I.Int.add.opp(_, True{}, Nat.sub(ym, 1n+xp), False{}, ym) == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %Equal.sym(Nat, Nat.sub(ym, Nat.sub(ym, 1n+xp)), 1n+xp, N.ci2(ym, 1n+xp, N.cmp_gt_of_lt(1n+xp, ym, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, ym), e1)))) : {I.Int{False{}, _} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
          %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{False{}, 1n+xp} == I.Int{False{}, 1n+_} : I.Int}
          {==}
    case EQ{} EQ{}:
      match xm:
        case 0n:
          match zm:
            case 0n:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(Nat.cmp(ym, 0n), True{}, ym, False{}, 0n)) : I.Int}
              %e2 : {I.Int{False{}, 0n} == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, 0n)) : I.Int}
              {==}
            case 1n+zp:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 0n, True{}, ym), I.Int{False{}, 1n+zp}) == I.Int.add(I.Int{False{}, 0n}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 1n+zp})) : I.Int}
              %e2 : {I.Int.add.same(False{}, 0n, 1n+zp) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : I.Int}
              Empty.absurd({I.Int.add.same(False{}, 0n, 1n+zp) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(EQ{}, True{}, ym, False{}, 1n+zp)) : I.Int},
                N.eq_ne_lt(Equal.trans(Cmp, EQ{}, Nat.cmp(ym, 1n+zp), LT{}, e2,
                  Equal.trans(Cmp, Nat.cmp(ym, 1n+zp), Nat.cmp(0n, 1n+zp), LT{},
                    Equal.cong(Nat, Cmp, t => Nat.cmp(t, 1n+zp), ym, 0n,
                      Equal.sym(Nat, 0n, ym, N.cmp_eq(0n, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(0n, ym), e1)))),
                    {==}))))
        case 1n+xp:
          match zm:
            case 0n:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, 0n}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 0n})) : I.Int}
              %e2 : {I.Int.add.same(False{}, 0n, 0n) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, 0n)) : I.Int}
              Empty.absurd({I.Int.add.same(False{}, 0n, 0n) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(EQ{}, True{}, ym, False{}, 0n)) : I.Int},
                N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(ym, 0n), GT{}, e2,
                  Equal.trans(Cmp, Nat.cmp(ym, 0n), Nat.cmp(1n+xp, 0n), GT{},
                    Equal.cong(Nat, Cmp, t => Nat.cmp(t, 0n), ym, 1n+xp,
                      Equal.sym(Nat, 1n+xp, ym, N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1)))),
                    {==}))))
            case 1n+zp:
              %e1 : {I.Int.add(I.Int.add.opp(_, False{}, 1n+xp, True{}, ym), I.Int{False{}, 1n+zp}) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, 1n+zp})) : I.Int}
              %e2 : {I.Int.add.same(False{}, 0n, 1n+zp) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : I.Int}
              %N.succ_inj(xp, zp,
                Equal.trans(Nat, 1n+xp, ym, 1n+zp,
                  N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1)),
                  N.cmp_eq(ym, 1n+zp, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, 1n+zp), e2)))) : {I.Int{False{}, 1n+_} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{False{}, 1n+xp} == I.Int{False{}, 1n+_} : I.Int}
              {==}

def I.Int.add.assoc.fft.zl(c, am, zm, e):
  match c:
    case EQ{}:
      %e : {I.Int.add.opp(_, False{}, am, True{}, zm) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : I.Int}
      %e : {I.Int{False{}, 0n} == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, False{}, am, True{}, zm)) : I.Int}
      {==}
    case GT{}:
      %e : {I.Int.add.opp(_, False{}, am, True{}, zm) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : I.Int}
      %e : {I.Int{False{}, Nat.sub(am, zm)} == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, False{}, am, True{}, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {I.Int{False{}, _} == I.Int.mk(False{}, Nat.sub(am, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {I.Int{False{}, 1n+Nat.sub(am, 1n+zm)} == I.Int.mk(False{}, _) : I.Int}
      {==}
    case LT{}:
      %e : {I.Int.add.opp(_, False{}, am, True{}, zm) == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : I.Int}
      %e : {I.Int{True{}, Nat.sub(zm, am)} == I.Int.add(I.Int{False{}, 0n}, I.Int.add.opp(_, False{}, am, True{}, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {I.Int{True{}, _} == I.Int.add(I.Int{False{}, 0n}, I.Int{True{}, Nat.sub(zm, am)}) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {I.Int{True{}, 1n+Nat.sub(zm, 1n+am)} == I.Int.add(I.Int{False{}, 0n}, I.Int{True{}, _}) : I.Int}
      {==}

def I.Int.add.assoc.fft.pos(c1, c2, xp, ym, zm, e1, e2):
  match c1 c2:
    case GT{} GT{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(GT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.add(1n+xp, Nat.sub(ym, zm)), N.ci5(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2))) : {I.Int{False{}, _} == I.Int{False{}, 1n+Nat.add(xp, Nat.sub(ym, zm))} : I.Int}
      {==}
    case GT{} EQ{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(GT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int{False{}, Nat.sub(1n+Nat.add(xp, ym), _)} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp, N.add_sub_cancel(1n+xp, ym)) : {I.Int{False{}, _} == I.Int{False{}, 1n+Nat.add(xp, 0n)} : I.Int}
      %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {I.Int{False{}, 1n+xp} == I.Int{False{}, 1n+_} : I.Int}
      {==}
    case GT{} LT{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(GT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), GT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), GT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {I.Int{False{}, Nat.sub(1n+Nat.add(xp, ym), zm)} == I.Int.add.opp(_, False{}, 1n+xp, True{}, Nat.sub(zm, ym)) : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.sub(1n+xp, Nat.sub(zm, ym)), N.ci6(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)), Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1))) : {I.Int{False{}, _} == I.Int{False{}, Nat.sub(1n+xp, Nat.sub(zm, ym))} : I.Int}
      {==}
    case EQ{} GT{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(GT{}, False{}, ym, True{}, zm)) : I.Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case EQ{} EQ{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(EQ{}, False{}, ym, True{}, zm)) : I.Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case EQ{} LT{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), EQ{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(1n+xp, 1n+xp), EQ{},
          Equal.cong(Nat, Cmp, t => Nat.cmp(1n+xp, t), Nat.sub(zm, ym), 1n+xp,
            Equal.trans(Nat, Nat.sub(zm, ym), Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp,
              Equal.cong(Nat, Nat, t => Nat.sub(t, ym), zm, Nat.add(1n+xp, ym),
                Equal.sym(Nat, Nat.add(1n+xp, ym), zm, N.cmp_eq(1n+Nat.add(xp, ym), zm, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))),
              N.add_sub_cancel(1n+xp, ym))),
          N.cmp_refl(1n+xp)))
        : {I.Int{False{}, 0n} == I.Int.add.opp(_, False{}, 1n+xp, True{}, Nat.sub(zm, ym)) : I.Int}
      {==}
    case LT{} GT{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(GT{}, False{}, ym, True{}, zm)) : I.Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case LT{} EQ{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(EQ{}, False{}, ym, True{}, zm)) : I.Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case LT{} LT{}:
      %e1 : {I.Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == I.Int.add(I.Int{False{}, 1n+xp}, I.Int.add.opp(_, False{}, ym, True{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), LT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), LT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, LT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {I.Int{True{}, Nat.sub(zm, 1n+Nat.add(xp, ym))} == I.Int.add.opp(_, False{}, 1n+xp, True{}, Nat.sub(zm, ym)) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, Nat.add(1n+xp, ym)), Nat.sub(Nat.sub(zm, ym), 1n+xp), N.ci7(1n+xp, ym, zm)) : {I.Int{True{}, _} == I.Int{True{}, Nat.sub(Nat.sub(zm, ym), 1n+xp)} : I.Int}
      {==}

def I.Int.add.assoc.fft(xm, ym, zm):
  match xm:
    case 0n:
      match ym:
        case 0n:
          match zm:
            case 0n:
              {==}
            case 1n+zp:
              {==}
        case 1n+yp:
          I.Int.add.assoc.fft.zl(Nat.cmp(1n+yp, zm), 1n+yp, zm, {==})
    case 1n+xp:
      I.Int.add.assoc.fft.pos(Nat.cmp(1n+Nat.add(xp, ym), zm), Nat.cmp(ym, zm), xp, ym, zm, {==}, {==})

def I.Int.add.assoc.rev(x, y, z, e):
  Equal.trans(I.Int,
    I.Int.add(I.Int.add(x, y), z),
    I.Int.add(z, I.Int.add(x, y)),
    I.Int.add(x, I.Int.add(y, z)),
    I.Int.add_comm(I.Int.add(x, y), z),
    Equal.trans(I.Int,
      I.Int.add(z, I.Int.add(x, y)),
      I.Int.add(z, I.Int.add(y, x)),
      I.Int.add(x, I.Int.add(y, z)),
      Equal.cong(I.Int, I.Int, v => I.Int.add(z, v),
        I.Int.add(x, y), I.Int.add(y, x), I.Int.add_comm(x, y)),
      Equal.trans(I.Int,
        I.Int.add(z, I.Int.add(y, x)),
        I.Int.add(I.Int.add(z, y), x),
        I.Int.add(x, I.Int.add(y, z)),
        Equal.sym(I.Int,
          I.Int.add(I.Int.add(z, y), x),
          I.Int.add(z, I.Int.add(y, x)),
          e),
        Equal.trans(I.Int,
          I.Int.add(I.Int.add(z, y), x),
          I.Int.add(x, I.Int.add(z, y)),
          I.Int.add(x, I.Int.add(y, z)),
          I.Int.add_comm(I.Int.add(z, y), x),
          Equal.cong(I.Int, I.Int, v => I.Int.add(x, v),
            I.Int.add(z, y), I.Int.add(y, z), I.Int.add_comm(z, y))))))

def I.Int.add.assoc.tff(xm, ym, zm):
  I.Int.add.assoc.rev(I.Int{True{}, xm}, I.Int{False{}, ym}, I.Int{False{}, zm}, I.Int.add.assoc.fft(zm, ym, xm))

def I.Int.add.assoc.ttf.zl(c, am, zm, e):
  match c:
    case EQ{}:
      %e : {I.Int.add.opp(_, True{}, am, False{}, zm) == I.Int.add(I.Int{True{}, 0n}, I.Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : I.Int}
      %e : {I.Int{False{}, 0n} == I.Int.add(I.Int{True{}, 0n}, I.Int.add.opp(_, True{}, am, False{}, zm)) : I.Int}
      {==}
    case GT{}:
      %e : {I.Int.add.opp(_, True{}, am, False{}, zm) == I.Int.add(I.Int{True{}, 0n}, I.Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : I.Int}
      %e : {I.Int{True{}, Nat.sub(am, zm)} == I.Int.add(I.Int{True{}, 0n}, I.Int.add.opp(_, True{}, am, False{}, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {I.Int{True{}, _} == I.Int.mk(True{}, Nat.sub(am, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {I.Int{True{}, 1n+Nat.sub(am, 1n+zm)} == I.Int.mk(True{}, _) : I.Int}
      {==}
    case LT{}:
      %e : {I.Int.add.opp(_, True{}, am, False{}, zm) == I.Int.add(I.Int{True{}, 0n}, I.Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : I.Int}
      %e : {I.Int{False{}, Nat.sub(zm, am)} == I.Int.add(I.Int{True{}, 0n}, I.Int.add.opp(_, True{}, am, False{}, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {I.Int{False{}, _} == I.Int.add(I.Int{True{}, 0n}, I.Int{False{}, Nat.sub(zm, am)}) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {I.Int{False{}, 1n+Nat.sub(zm, 1n+am)} == I.Int.add(I.Int{True{}, 0n}, I.Int{False{}, _}) : I.Int}
      {==}

def I.Int.add.assoc.ttf.pos(c1, c2, xp, ym, zm, e1, e2):
  match c1 c2:
    case GT{} GT{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(GT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.add(1n+xp, Nat.sub(ym, zm)), N.ci5(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2))) : {I.Int{True{}, _} == I.Int{True{}, 1n+Nat.add(xp, Nat.sub(ym, zm))} : I.Int}
      {==}
    case GT{} EQ{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(GT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {I.Int{True{}, Nat.sub(1n+Nat.add(xp, ym), _)} == I.Int.add(I.Int{True{}, 1n+xp}, I.Int{False{}, 0n}) : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp, N.add_sub_cancel(1n+xp, ym)) : {I.Int{True{}, _} == I.Int.add(I.Int{True{}, 1n+xp}, I.Int{False{}, 0n}) : I.Int}
      {==}
    case GT{} LT{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(GT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), GT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), GT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {I.Int{True{}, Nat.sub(1n+Nat.add(xp, ym), zm)} == I.Int.add.opp(_, True{}, 1n+xp, False{}, Nat.sub(zm, ym)) : I.Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.sub(1n+xp, Nat.sub(zm, ym)), N.ci6(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)), Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1))) : {I.Int{True{}, _} == I.Int{True{}, Nat.sub(1n+xp, Nat.sub(zm, ym))} : I.Int}
      {==}
    case EQ{} GT{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(GT{}, True{}, ym, False{}, zm)) : I.Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case EQ{} EQ{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(EQ{}, True{}, ym, False{}, zm)) : I.Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case EQ{} LT{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), EQ{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(1n+xp, 1n+xp), EQ{},
          Equal.cong(Nat, Cmp, t => Nat.cmp(1n+xp, t), Nat.sub(zm, ym), 1n+xp,
            Equal.trans(Nat, Nat.sub(zm, ym), Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp,
              Equal.cong(Nat, Nat, t => Nat.sub(t, ym), zm, Nat.add(1n+xp, ym),
                Equal.sym(Nat, Nat.add(1n+xp, ym), zm, N.cmp_eq(1n+Nat.add(xp, ym), zm, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))),
              N.add_sub_cancel(1n+xp, ym))),
          N.cmp_refl(1n+xp)))
        : {I.Int{False{}, 0n} == I.Int.add.opp(_, True{}, 1n+xp, False{}, Nat.sub(zm, ym)) : I.Int}
      {==}
    case LT{} GT{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(GT{}, True{}, ym, False{}, zm)) : I.Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case LT{} EQ{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      Empty.absurd({I.Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(EQ{}, True{}, ym, False{}, zm)) : I.Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case LT{} LT{}:
      %e1 : {I.Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add(I.Int{True{}, ym}, I.Int{False{}, zm})) : I.Int}
      %e2 : {I.Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == I.Int.add(I.Int{True{}, 1n+xp}, I.Int.add.opp(_, True{}, ym, False{}, zm)) : I.Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), LT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), LT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, LT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {I.Int{False{}, Nat.sub(zm, 1n+Nat.add(xp, ym))} == I.Int.add.opp(_, True{}, 1n+xp, False{}, Nat.sub(zm, ym)) : I.Int}
      %Equal.sym(Nat, Nat.sub(zm, Nat.add(1n+xp, ym)), Nat.sub(Nat.sub(zm, ym), 1n+xp), N.ci7(1n+xp, ym, zm)) : {I.Int{False{}, _} == I.Int{False{}, Nat.sub(Nat.sub(zm, ym), 1n+xp)} : I.Int}
      {==}

def I.Int.add.assoc.ttf(xm, ym, zm):
  match xm:
    case 0n:
      match ym:
        case 0n:
          match zm:
            case 0n:
              {==}
            case 1n+zp:
              {==}
        case 1n+yp:
          I.Int.add.assoc.ttf.zl(Nat.cmp(1n+yp, zm), 1n+yp, zm, {==})
    case 1n+xp:
      I.Int.add.assoc.ttf.pos(Nat.cmp(1n+Nat.add(xp, ym), zm), Nat.cmp(ym, zm), xp, ym, zm, {==}, {==})

def I.Int.add.assoc.ftt(xm, ym, zm):
  I.Int.add.assoc.rev(I.Int{False{}, xm}, I.Int{True{}, ym}, I.Int{True{}, zm}, I.Int.add.assoc.ttf(zm, ym, xm))

def I.Int.add.assoc.tft(xm, ym, zm):
  Equal.trans(I.Int,
    I.Int.add(I.Int.add(I.Int{True{}, xm}, I.Int{False{}, ym}), I.Int{True{}, zm}),
    I.Int.add(I.Int{True{}, zm}, I.Int.add(I.Int{True{}, xm}, I.Int{False{}, ym})),
    I.Int.add(I.Int{True{}, xm}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})),
    I.Int.add_comm(I.Int.add(I.Int{True{}, xm}, I.Int{False{}, ym}), I.Int{True{}, zm}),
    Equal.trans(I.Int,
      I.Int.add(I.Int{True{}, zm}, I.Int.add(I.Int{True{}, xm}, I.Int{False{}, ym})),
      I.Int.add(I.Int.add(I.Int{True{}, zm}, I.Int{True{}, xm}), I.Int{False{}, ym}),
      I.Int.add(I.Int{True{}, xm}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})),
      Equal.sym(I.Int,
        I.Int.add(I.Int.add(I.Int{True{}, zm}, I.Int{True{}, xm}), I.Int{False{}, ym}),
        I.Int.add(I.Int{True{}, zm}, I.Int.add(I.Int{True{}, xm}, I.Int{False{}, ym})),
        I.Int.add.assoc.ttf(zm, xm, ym)),
      Equal.trans(I.Int,
        I.Int.add(I.Int.add(I.Int{True{}, zm}, I.Int{True{}, xm}), I.Int{False{}, ym}),
        I.Int.add(I.Int.add(I.Int{True{}, xm}, I.Int{True{}, zm}), I.Int{False{}, ym}),
        I.Int.add(I.Int{True{}, xm}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})),
        Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int{False{}, ym}),
          I.Int.add(I.Int{True{}, zm}, I.Int{True{}, xm}), I.Int.add(I.Int{True{}, xm}, I.Int{True{}, zm}),
          I.Int.add_comm(I.Int{True{}, zm}, I.Int{True{}, xm})),
        Equal.trans(I.Int,
          I.Int.add(I.Int.add(I.Int{True{}, xm}, I.Int{True{}, zm}), I.Int{False{}, ym}),
          I.Int.add(I.Int{True{}, xm}, I.Int.add(I.Int{True{}, zm}, I.Int{False{}, ym})),
          I.Int.add(I.Int{True{}, xm}, I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm})),
          I.Int.add.assoc.ttf(xm, zm, ym),
          Equal.cong(I.Int, I.Int, v => I.Int.add(I.Int{True{}, xm}, v),
            I.Int.add(I.Int{True{}, zm}, I.Int{False{}, ym}), I.Int.add(I.Int{False{}, ym}, I.Int{True{}, zm}),
            I.Int.add_comm(I.Int{True{}, zm}, I.Int{False{}, ym}))))))

def I.Int.add_assoc(x, y, z):
  match x y z:
    case I.Int{False{}, xm} I.Int{False{}, ym} I.Int{False{}, zm}:
      I.Int.add.assoc.fff(xm, ym, zm)
    case I.Int{False{}, xm} I.Int{False{}, ym} I.Int{True{}, zm}:
      I.Int.add.assoc.fft(xm, ym, zm)
    case I.Int{False{}, xm} I.Int{True{}, ym} I.Int{False{}, zm}:
      I.Int.add.assoc.ftf(Nat.cmp(xm, ym), Nat.cmp(ym, zm), xm, ym, zm, {==}, {==})
    case I.Int{False{}, xm} I.Int{True{}, ym} I.Int{True{}, zm}:
      I.Int.add.assoc.ftt(xm, ym, zm)
    case I.Int{True{}, xm} I.Int{False{}, ym} I.Int{False{}, zm}:
      I.Int.add.assoc.tff(xm, ym, zm)
    case I.Int{True{}, xm} I.Int{False{}, ym} I.Int{True{}, zm}:
      I.Int.add.assoc.tft(xm, ym, zm)
    case I.Int{True{}, xm} I.Int{True{}, ym} I.Int{False{}, zm}:
      I.Int.add.assoc.ttf(xm, ym, zm)
    case I.Int{True{}, xm} I.Int{True{}, ym} I.Int{True{}, zm}:
      I.Int.add.assoc.ttt(xm, ym, zm)
