import Base
import ./nat.bend as N

# Int: signed integers as sign + magnitude
# ========================================
#
# sign = False means non-negative, True means non-positive. Constructors
# may build a non-canonical zero Int{True{}, 0n}, but every *operation*
# canonicalizes (Int.mk, and the EQ branch of Int.add.opp), so results
# compare correctly with ==.

type Int is Data:
  Int{sign: Bool, mag: Nat}

# canonical constructor: zero is always Int{False{}, 0n}
def Int.mk(s: Bool, m: Nat) -> Int:
  match m:
    case 0n:
      Int{False{}, 0n}
    case 1n+p:
      Int{s, 1n+p}

# opposite-sign addition, decided by the magnitudes' comparison
def Int.add.opp(c: Cmp, xs: Bool, xm: Nat, ys: Bool, ym: Nat) -> Int:
  match c:
    case EQ{}:
      Int{False{}, 0n}
    case GT{}:
      Int{xs, Nat.sub(xm, ym)}
    case LT{}:
      Int{ys, Nat.sub(ym, xm)}

# same-sign addition: x + y, both of sign s
def Int.add.same(s: Bool, xm: Nat, ym: Nat) -> Int:
  match xm:
    case 0n:
      Int.mk(s, ym)
    case 1n+xp:
      Int{s, 1n+Nat.add(xp, ym)}

def Int.add.go(xs: Bool, +xm: Nat, ys: Bool, +ym: Nat) -> Int:
  match xs ys:
    case False{} False{}:
      Int.add.same(False{}, xm, ym)
    case True{} True{}:
      Int.add.same(True{}, xm, ym)
    case False{} True{}:
      Int.add.opp(Nat.cmp(xm, ym), False{}, xm, True{}, ym)
    case True{} False{}:
      Int.add.opp(Nat.cmp(xm, ym), True{}, xm, False{}, ym)

def Int.add(x: Int, y: Int) -> Int:
  Int{xs, xm} = x
  Int{ys, ym} = y
  Int.add.go(xs, xm, ys, ym)

def Int.mul(x: Int, y: Int) -> Int:
  Int{xs, xm} = x
  Int{ys, ym} = y
  Int{Bool.xor(xs, ys), Nat.mul(xm, ym)}

# xor_comm: xor is commutative
law xor_comm:
  for +a: Bool
  for +b: Bool
  {Bool.xor(a, b) == Bool.xor(b, a) : Bool}

def xor_comm(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Int.mul_comm: x * y = y * x
law Int.mul_comm:
  for +x: Int
  for +y: Int
  {Int.mul(x, y) == Int.mul(y, x) : Int}

def Int.mul_comm(x, y):
  match x y:
    case Int{xs, xm} Int{ys, ym}:
      %xor_comm(xs, ys) : {Int{Bool.xor(xs, ys), Nat.mul(xm, ym)} == Int{_, Nat.mul(ym, xm)} : Int}
      %N.mul_comm(xm, ym) : {Int{Bool.xor(xs, ys), Nat.mul(xm, ym)} == Int{Bool.xor(xs, ys), _} : Int}
      {==}

# Int.add.opp_comm: opposite-sign addition commutes (via Cmp.flip)
law Int.add.opp_comm:
  for +c: Cmp
  for +xs: Bool
  for +ys: Bool
  for +xm: Nat
  for +ym: Nat
  {Int.add.opp(c, xs, xm, ys, ym) == Int.add.opp(N.Cmp.flip(c), ys, ym, xs, xm) : Int}

def Int.add.opp_comm(c, xs, ys, xm, ym):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      {==}

# Int.add.same_comm: same-sign addition commutes
law Int.add.same_comm:
  for +s: Bool
  for +xm: Nat
  for +ym: Nat
  {Int.add.same(s, xm, ym) == Int.add.same(s, ym, xm) : Int}

def Int.add.same_comm(s, xm, ym):
  match xm ym:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      %N.add_zero(yp) : {Int{s, 1n+_} == Int{s, 1n+Nat.add(yp, 0n)} : Int}
      {==}
    case 1n+xp 0n:
      %N.add_zero(xp) : {Int{s, 1n+Nat.add(xp, 0n)} == Int{s, 1n+_} : Int}
      {==}
    case 1n+xp 1n+yp:
      %N.add_comm_succ(xp, yp) : {Int{s, 1n+Nat.add(xp, 1n+yp)} == Int{s, 1n+_} : Int}
      {==}

# Int.add_comm: x + y = y + x
law Int.add_comm:
  for +x: Int
  for +y: Int
  {Int.add(x, y) == Int.add(y, x) : Int}

def Int.add_comm(x, y):
  match x y:
    case Int{False{}, xm} Int{False{}, ym}:
      Int.add.same_comm(False{}, xm, ym)
    case Int{True{}, xm} Int{True{}, ym}:
      Int.add.same_comm(True{}, xm, ym)
    case Int{False{}, xm} Int{True{}, ym}:
      %Equal.sym(Cmp, Nat.cmp(ym, xm), N.Cmp.flip(Nat.cmp(xm, ym)), N.cmp_antisym(ym, xm)) : {Int.add.opp(Nat.cmp(xm, ym), False{}, xm, True{}, ym) == Int.add.opp(_, True{}, ym, False{}, xm) : Int}
      Int.add.opp_comm(Nat.cmp(xm, ym), False{}, True{}, xm, ym)
    case Int{True{}, xm} Int{False{}, ym}:
      %Equal.sym(Cmp, Nat.cmp(ym, xm), N.Cmp.flip(Nat.cmp(xm, ym)), N.cmp_antisym(ym, xm)) : {Int.add.opp(Nat.cmp(xm, ym), True{}, xm, False{}, ym) == Int.add.opp(_, False{}, ym, True{}, xm) : Int}
      Int.add.opp_comm(Nat.cmp(xm, ym), True{}, False{}, xm, ym)

# xor_assoc: xor is associative
law xor_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}

def xor_assoc(a, b, c):
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

# Int.mul_assoc: (x * y) * z = x * (y * z)
law Int.mul_assoc:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.mul(Int.mul(x, y), z) == Int.mul(x, Int.mul(y, z)) : Int}

def Int.mul_assoc(x, y, z):
  match x y z:
    case Int{xs, xm} Int{ys, ym} Int{zs, zm}:
      %xor_assoc(xs, ys, zs) : {Int{Bool.xor(Bool.xor(xs, ys), zs), Nat.mul(Nat.mul(xm, ym), zm)} == Int{_, Nat.mul(xm, Nat.mul(ym, zm))} : Int}
      %N.mul_assoc(xm, ym, zm) : {Int{Bool.xor(Bool.xor(xs, ys), zs), Nat.mul(Nat.mul(xm, ym), zm)} == Int{Bool.xor(Bool.xor(xs, ys), zs), _} : Int}
      {==}

# Int.mul_swap: (a * b) * c = (a * c) * b
law Int.mul_swap:
  for +a: Int
  for +b: Int
  for +c: Int
  {Int.mul(Int.mul(a, b), c) == Int.mul(Int.mul(a, c), b) : Int}

def Int.mul_swap(a, b, c):
  Equal.trans(Int,
    Int.mul(Int.mul(a, b), c),
    Int.mul(a, Int.mul(b, c)),
    Int.mul(Int.mul(a, c), b),
    Int.mul_assoc(a, b, c),
    Equal.trans(Int,
      Int.mul(a, Int.mul(b, c)),
      Int.mul(a, Int.mul(c, b)),
      Int.mul(Int.mul(a, c), b),
      Equal.cong(Int, Int, v => Int.mul(a, v),
        Int.mul(b, c), Int.mul(c, b), Int.mul_comm(b, c)),
      Equal.sym(Int,
        Int.mul(Int.mul(a, c), b),
        Int.mul(a, Int.mul(c, b)),
        Int.mul_assoc(a, c, b))))

# Int.add_assoc: (x + y) + z = x + (y + z)
# ========================================
#
# Sign-magnitude associativity. Same-sign cases reduce to Nat.add_assoc.
# Mixed-sign cases case-split on the two inner Nat.cmp results (passed to
# helpers as Cmp parameters with flipped evidence {c == Nat.cmp(..)} so the
# goal's cmp occurrences can be rewritten to constructors).

# FFF: all non-negative
law Int.add.assoc.fff:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{False{}, xm}, Int{False{}, ym}), Int{False{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{False{}, ym}, Int{False{}, zm})) : Int}

def Int.add.assoc.fff(xm, ym, zm):
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
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{False{}, 1n+Nat.add(_, 0n)} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
              {==}
            case 1n+zp:
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{False{}, 1n+Nat.add(_, 1n+zp)} == Int{False{}, 1n+Nat.add(xp, 1n+zp)} : Int}
              {==}
        case 1n+yp:
          %Equal.sym(Nat, Nat.add(Nat.add(xp, 1n+yp), zm), Nat.add(xp, Nat.add(1n+yp, zm)), N.add_assoc(xp, 1n+yp, zm)) : {Int{False{}, 1n+_} == Int{False{}, 1n+Nat.add(xp, 1n+Nat.add(yp, zm))} : Int}
          {==}

# TTT: all non-positive
law Int.add.assoc.ttt:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{True{}, ym}), Int{True{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{True{}, ym}, Int{True{}, zm})) : Int}

def Int.add.assoc.ttt(xm, ym, zm):
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
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{True{}, 1n+Nat.add(_, 0n)} == Int{True{}, 1n+xp} : Int}
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{True{}, 1n+_} == Int{True{}, 1n+xp} : Int}
              {==}
            case 1n+zp:
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{True{}, 1n+Nat.add(_, 1n+zp)} == Int{True{}, 1n+Nat.add(xp, 1n+zp)} : Int}
              {==}
        case 1n+yp:
          %Equal.sym(Nat, Nat.add(Nat.add(xp, 1n+yp), zm), Nat.add(xp, Nat.add(1n+yp, zm)), N.add_assoc(xp, 1n+yp, zm)) : {Int{True{}, 1n+_} == Int{True{}, 1n+Nat.add(xp, 1n+Nat.add(yp, zm))} : Int}
          {==}

# FTF case, (LT, GT) sub-split: d = cmp(ym - xm, zm)
law Int.add.assoc.ftf.ltgt:
  for d: Cmp
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  for +ed: {d == Nat.cmp(Nat.sub(ym, xm), zm) : Cmp}
  for +e1: {Nat.cmp(ym, xm) == GT{} : Cmp}
  for +e2: {Nat.cmp(ym, zm) == GT{} : Cmp}
  {Int.add.opp(Nat.cmp(Nat.sub(ym, xm), zm), True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : Int}

def Int.add.assoc.ftf.ltgt(d, xm, ym, zm, ed, e1, e2):
  match d:
    case EQ{}:
      %ed : {Int.add.opp(_, True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      %N.cmp_sub_flip_of(EQ{}, xm, zm, ym, ed, e1, e2) : {Int.add.opp(EQ{}, True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      {==}
    case LT{}:
      %ed : {Int.add.opp(_, True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      %N.cmp_sub_flip_of(LT{}, xm, zm, ym, ed, e1, e2) : {Int.add.opp(LT{}, True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(zm, Nat.sub(ym, xm)), Nat.sub(xm, Nat.sub(ym, zm)), N.ci3(xm, ym, zm, e1, e2, Equal.sym(Cmp, LT{}, Nat.cmp(Nat.sub(ym, xm), zm), ed))) : {Int{False{}, _} == Int{False{}, Nat.sub(xm, Nat.sub(ym, zm))} : Int}
      {==}
    case GT{}:
      %ed : {Int.add.opp(_, True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(Nat.cmp(xm, Nat.sub(ym, zm)), False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      %N.cmp_sub_flip_of(GT{}, xm, zm, ym, ed, e1, e2) : {Int.add.opp(GT{}, True{}, Nat.sub(ym, xm), False{}, zm) == Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(Nat.sub(ym, xm), zm), Nat.sub(Nat.sub(ym, zm), xm), N.sub_sub_swap(xm, zm, ym)) : {Int{True{}, _} == Int{True{}, Nat.sub(Nat.sub(ym, zm), xm)} : Int}
      {==}

# FTF: x >= 0, y <= 0, z >= 0
law Int.add.assoc.ftf:
  for c1: Cmp
  for c2: Cmp
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  for +e1: {c1 == Nat.cmp(xm, ym) : Cmp}
  for +e2: {c2 == Nat.cmp(ym, zm) : Cmp}
  {Int.add(Int.add(Int{False{}, xm}, Int{True{}, ym}), Int{False{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}

def Int.add.assoc.ftf(c1, c2, xm, ym, zm, e1, e2):
  match c1 c2:
    case GT{} GT{}:
      %e1 : {Int.add(Int.add.opp(_, False{}, xm, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add(Int{False{}, Nat.sub(xm, ym)}, Int{False{}, zm}) == Int.add(Int{False{}, xm}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(xm, Nat.sub(ym, zm)), GT{}, N.cmp_gt_sub(xm, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1))) : {Int.add.same(False{}, Nat.sub(xm, ym), zm) == Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(xm, ym), 1n+Nat.sub(xm, 1n+ym), N.sub_pos(xm, ym, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1))) : {Int.add.same(False{}, _, zm) == Int{False{}, Nat.sub(xm, Nat.sub(ym, zm))} : Int}
      %N.ci8(xm, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1), Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)) : {Int{False{}, 1n+Nat.add(Nat.sub(xm, 1n+ym), zm)} == Int{False{}, _} : Int}
      %Equal.sym(Nat, Nat.sub(xm, ym), 1n+Nat.sub(xm, 1n+ym), N.sub_pos(xm, ym, Equal.sym(Cmp, GT{}, Nat.cmp(xm, ym), e1))) : {Int{False{}, 1n+Nat.add(Nat.sub(xm, 1n+ym), zm)} == Int{False{}, Nat.add(_, zm)} : Int}
      {==}
    case GT{} LT{}:
      match xm:
        case 0n:
          %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add(Int.add.opp(GT{}, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          Empty.absurd({Int.add(Int.add.opp(GT{}, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add.opp(LT{}, True{}, ym, False{}, zm)) : Int}, N.cmp_zero_gt(ym, Equal.sym(Cmp, GT{}, Nat.cmp(0n, ym), e1)))
        case 1n+xp:
          %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add.same(False{}, Nat.sub(1n+xp, ym), zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          %Equal.sym(Nat, Nat.sub(1n+xp, ym), 1n+Nat.sub(1n+xp, 1n+ym), N.sub_pos(1n+xp, ym, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1))) : {Int.add.same(False{}, _, zm) == Int{False{}, 1n+Nat.add(xp, Nat.sub(zm, ym))} : Int}
          %Equal.sym(Nat, Nat.add(Nat.sub(xp, ym), zm), Nat.add(xp, Nat.sub(zm, ym)), N.ci1(xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1), N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {Int{False{}, 1n+_} == Int{False{}, 1n+Nat.add(xp, Nat.sub(zm, ym))} : Int}
          {==}
    case GT{} EQ{}:
      match xm:
        case 0n:
          %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add(Int.add.opp(GT{}, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          Empty.absurd({Int.add(Int.add.opp(GT{}, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add.opp(EQ{}, True{}, ym, False{}, zm)) : Int}, N.cmp_zero_gt(ym, Equal.sym(Cmp, GT{}, Nat.cmp(0n, ym), e1)))
        case 1n+xp:
          %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add.same(False{}, Nat.sub(1n+xp, ym), zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          %Equal.sym(Nat, Nat.sub(1n+xp, ym), 1n+Nat.sub(1n+xp, 1n+ym), N.sub_pos(1n+xp, ym, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1))) : {Int.add.same(False{}, _, zm) == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int{False{}, 1n+Nat.add(Nat.sub(xp, ym), _)} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %Equal.sym(Nat, Nat.add(Nat.sub(xp, ym), ym), xp, N.ge_sub_add(xp, ym, Equal.sym(Cmp, GT{}, Nat.cmp(1n+xp, ym), e1))) : {Int{False{}, 1n+_} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{False{}, 1n+xp} == Int{False{}, 1n+_} : Int}
          {==}
    case EQ{} GT{}:
      match zm:
        case 0n:
          %e1 : {Int.add(Int.add.opp(_, False{}, xm, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, 0n})) : Int}
          %e2 : {Int.add(Int{False{}, 0n}, Int{False{}, 0n}) == Int.add(Int{False{}, xm}, Int.add.opp(_, True{}, ym, False{}, 0n)) : Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {Int{False{}, 0n} == Int.add.opp(Nat.cmp(xm, _), False{}, xm, True{}, Nat.sub(ym, 0n)) : Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {Int{False{}, 0n} == Int.add.opp(Nat.cmp(xm, ym), False{}, xm, True{}, _) : Int}
          %e1 : {Int{False{}, 0n} == Int.add.opp(_, False{}, xm, True{}, ym) : Int}
          {==}
        case 1n+zp:
          %e1 : {Int.add(Int.add.opp(_, False{}, xm, True{}, ym), Int{False{}, 1n+zp}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, 1n+zp})) : Int}
          %e2 : {Int.add.same(False{}, 0n, 1n+zp) == Int.add(Int{False{}, xm}, Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : Int}
          %Equal.sym(Cmp, Nat.cmp(xm, Nat.sub(ym, 1n+zp)), GT{},
            Equal.trans(Cmp, Nat.cmp(xm, Nat.sub(ym, 1n+zp)), Nat.cmp(ym, Nat.sub(ym, 1n+zp)), GT{},
              Equal.cong(Nat, Cmp, t => Nat.cmp(t, Nat.sub(ym, 1n+zp)), xm, ym, N.cmp_eq(xm, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(xm, ym), e1))),
              N.cmp_sub_gt_self(ym, zp, Equal.sym(Cmp, GT{}, Nat.cmp(ym, 1n+zp), e2))))
            : {Int{False{}, 1n+zp} == Int.add.opp(_, False{}, xm, True{}, Nat.sub(ym, 1n+zp)) : Int}
          %Equal.sym(Nat, xm, ym, N.cmp_eq(xm, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(xm, ym), e1))) : {Int{False{}, 1n+zp} == Int{False{}, Nat.sub(_, Nat.sub(ym, 1n+zp))} : Int}
          %Equal.sym(Nat, Nat.sub(ym, Nat.sub(ym, 1n+zp)), 1n+zp, N.ci2(ym, 1n+zp, Equal.sym(Cmp, GT{}, Nat.cmp(ym, 1n+zp), e2))) : {Int{False{}, 1n+zp} == Int{False{}, _} : Int}
          {==}
    case EQ{} LT{}:
      match xm:
        case 0n:
          match zm:
            case 0n:
              %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, 0n})) : Int}
              %e2 : {Int.add.same(False{}, 0n, 0n) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, 0n)) : Int}
              Empty.absurd({Int.add(Int.add.opp(EQ{}, False{}, 0n, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, 0n}, Int.add.opp(LT{}, True{}, ym, False{}, 0n)) : Int}, N.cmp_lt_zero(ym, Equal.sym(Cmp, LT{}, Nat.cmp(ym, 0n), e2)))
            case 1n+zp:
              %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, 1n+zp}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, 1n+zp})) : Int}
              %e2 : {Int.add.same(False{}, 0n, 1n+zp) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : Int}
              %Equal.sym(Nat, Nat.sub(1n+zp, ym), 1n+Nat.sub(1n+zp, 1n+ym), N.sub_pos(1n+zp, ym, N.cmp_gt_of_lt(ym, 1n+zp, Equal.sym(Cmp, LT{}, Nat.cmp(ym, 1n+zp), e2)))) : {Int{False{}, 1n+zp} == Int.mk(False{}, _) : Int}
              %N.cmp_eq(0n, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(0n, ym), e1)) : {Int{False{}, 1n+zp} == Int{False{}, 1n+Nat.sub(zp, _)} : Int}
              %Equal.sym(Nat, Nat.sub(zp, 0n), zp, N.sub_zero(zp)) : {Int{False{}, 1n+zp} == Int{False{}, 1n+_} : Int}
              {==}
        case 1n+xp:
          match zm:
            case 0n:
              %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, 0n})) : Int}
              %e2 : {Int.add.same(False{}, 0n, 0n) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, 0n)) : Int}
              Empty.absurd({Int.add(Int.add.opp(EQ{}, False{}, 1n+xp, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(LT{}, True{}, ym, False{}, 0n)) : Int}, N.cmp_lt_zero(ym, Equal.sym(Cmp, LT{}, Nat.cmp(ym, 0n), e2)))
            case 1n+zp:
              %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, 1n+zp}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, 1n+zp})) : Int}
              %e2 : {Int.mk(False{}, 1n+zp) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : Int}
              %N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1)) : {Int{False{}, 1n+zp} == Int{False{}, 1n+Nat.add(xp, Nat.sub(1n+zp, _))} : Int}
              %Equal.trans(Nat, zp, Nat.add(Nat.sub(zp, xp), xp), Nat.add(xp, Nat.sub(zp, xp)),
                Equal.sym(Nat, Nat.add(Nat.sub(zp, xp), xp), zp, N.cmp_lt_sub_add(xp, zp,
                  Equal.trans(Cmp, Nat.cmp(1n+xp, 1n+zp), Nat.cmp(ym, 1n+zp), LT{},
                    Equal.cong(Nat, Cmp, t => Nat.cmp(t, 1n+zp), 1n+xp, ym, N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1))),
                    Equal.sym(Cmp, LT{}, Nat.cmp(ym, 1n+zp), e2)))),
                N.add_comm(Nat.sub(zp, xp), xp))
                : {Int{False{}, 1n+zp} == Int{False{}, 1n+_} : Int}
              {==}
    case LT{} GT{}:
      %e1 : {Int.add(Int.add.opp(_, False{}, xm, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add(Int{True{}, Nat.sub(ym, xm)}, Int{False{}, zm}) == Int.add(Int{False{}, xm}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      Int.add.assoc.ftf.ltgt(Nat.cmp(Nat.sub(ym, xm), zm), xm, ym, zm, {==},
        N.cmp_gt_of_lt(xm, ym, Equal.sym(Cmp, LT{}, Nat.cmp(xm, ym), e1)),
        Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2))
    case LT{} LT{}:
      match xm:
        case 0n:
          %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add(Int{True{}, Nat.sub(ym, 0n)}, Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          %Equal.sym(Cmp, Nat.cmp(Nat.sub(ym, 0n), zm), LT{}, N.cmp_lt_sub(0n, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {Int.add.opp(_, True{}, Nat.sub(ym, 0n), False{}, zm) == Int.add.same(False{}, 0n, Nat.sub(zm, ym)) : Int}
          %Equal.sym(Nat, Nat.sub(zm, ym), 1n+Nat.sub(zm, 1n+ym), N.sub_pos(zm, ym, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {Int{False{}, Nat.sub(zm, Nat.sub(ym, 0n))} == Int.mk(False{}, _) : Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {Int{False{}, Nat.sub(zm, _)} == Int{False{}, 1n+Nat.sub(zm, 1n+ym)} : Int}
          %Equal.sym(Nat, Nat.sub(zm, ym), 1n+Nat.sub(zm, 1n+ym), N.sub_pos(zm, ym, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {Int{False{}, _} == Int{False{}, 1n+Nat.sub(zm, 1n+ym)} : Int}
          {==}
        case 1n+xp:
          %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add(Int{True{}, Nat.sub(ym, 1n+xp)}, Int{False{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          %Equal.sym(Cmp, Nat.cmp(Nat.sub(ym, 1n+xp), zm), LT{}, N.cmp_lt_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {Int.add.opp(_, True{}, Nat.sub(ym, 1n+xp), False{}, zm) == Int.add.same(False{}, 1n+xp, Nat.sub(zm, ym)) : Int}
          %Equal.sym(Nat, Nat.sub(zm, Nat.sub(ym, 1n+xp)), Nat.add(1n+xp, Nat.sub(zm, ym)), N.ci4(1n+xp, ym, zm, N.cmp_gt_of_lt(1n+xp, ym, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, ym), e1)), N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))) : {Int{False{}, _} == Int{False{}, 1n+Nat.add(xp, Nat.sub(zm, ym))} : Int}
          {==}
    case LT{} EQ{}:
      match xm:
        case 0n:
          %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add(Int{True{}, Nat.sub(ym, 0n)}, Int{False{}, zm}) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int.add.opp(Nat.cmp(Nat.sub(ym, 0n), _), True{}, Nat.sub(ym, 0n), False{}, zm) == Int{False{}, 0n} : Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int.add.opp(Nat.cmp(Nat.sub(ym, 0n), ym), True{}, Nat.sub(ym, 0n), False{}, _) == Int{False{}, 0n} : Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {Int.add.opp(Nat.cmp(_, ym), True{}, Nat.sub(ym, 0n), False{}, ym) == Int{False{}, 0n} : Int}
          %Equal.sym(Nat, Nat.sub(ym, 0n), ym, N.sub_zero(ym)) : {Int.add.opp(Nat.cmp(ym, ym), True{}, _, False{}, ym) == Int{False{}, 0n} : Int}
          %Equal.sym(Cmp, Nat.cmp(ym, ym), EQ{}, N.cmp_refl(ym)) : {Int.add.opp(_, True{}, ym, False{}, ym) == Int{False{}, 0n} : Int}
          {==}
        case 1n+xp:
          %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
          %e2 : {Int.add(Int{True{}, Nat.sub(ym, 1n+xp)}, Int{False{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int.add.opp(Nat.cmp(Nat.sub(ym, 1n+xp), _), True{}, Nat.sub(ym, 1n+xp), False{}, zm) == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int.add.opp(Nat.cmp(Nat.sub(ym, 1n+xp), ym), True{}, Nat.sub(ym, 1n+xp), False{}, _) == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %Equal.sym(Cmp, Nat.cmp(Nat.sub(ym, 1n+xp), ym), LT{}, N.cmp_sub_lt(ym, xp, N.cmp_gt_of_lt(1n+xp, ym, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, ym), e1)))) : {Int.add.opp(_, True{}, Nat.sub(ym, 1n+xp), False{}, ym) == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %Equal.sym(Nat, Nat.sub(ym, Nat.sub(ym, 1n+xp)), 1n+xp, N.ci2(ym, 1n+xp, N.cmp_gt_of_lt(1n+xp, ym, Equal.sym(Cmp, LT{}, Nat.cmp(1n+xp, ym), e1)))) : {Int{False{}, _} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
          %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{False{}, 1n+xp} == Int{False{}, 1n+_} : Int}
          {==}
    case EQ{} EQ{}:
      match xm:
        case 0n:
          match zm:
            case 0n:
              %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, 0n}, Int.add.opp(Nat.cmp(ym, 0n), True{}, ym, False{}, 0n)) : Int}
              %e2 : {Int{False{}, 0n} == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, 0n)) : Int}
              {==}
            case 1n+zp:
              %e1 : {Int.add(Int.add.opp(_, False{}, 0n, True{}, ym), Int{False{}, 1n+zp}) == Int.add(Int{False{}, 0n}, Int.add(Int{True{}, ym}, Int{False{}, 1n+zp})) : Int}
              %e2 : {Int.add.same(False{}, 0n, 1n+zp) == Int.add(Int{False{}, 0n}, Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : Int}
              Empty.absurd({Int.add.same(False{}, 0n, 1n+zp) == Int.add(Int{False{}, 0n}, Int.add.opp(EQ{}, True{}, ym, False{}, 1n+zp)) : Int},
                N.eq_ne_lt(Equal.trans(Cmp, EQ{}, Nat.cmp(ym, 1n+zp), LT{}, e2,
                  Equal.trans(Cmp, Nat.cmp(ym, 1n+zp), Nat.cmp(0n, 1n+zp), LT{},
                    Equal.cong(Nat, Cmp, t => Nat.cmp(t, 1n+zp), ym, 0n,
                      Equal.sym(Nat, 0n, ym, N.cmp_eq(0n, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(0n, ym), e1)))),
                    {==}))))
        case 1n+xp:
          match zm:
            case 0n:
              %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, 0n}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, 0n})) : Int}
              %e2 : {Int.add.same(False{}, 0n, 0n) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, 0n)) : Int}
              Empty.absurd({Int.add.same(False{}, 0n, 0n) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(EQ{}, True{}, ym, False{}, 0n)) : Int},
                N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(ym, 0n), GT{}, e2,
                  Equal.trans(Cmp, Nat.cmp(ym, 0n), Nat.cmp(1n+xp, 0n), GT{},
                    Equal.cong(Nat, Cmp, t => Nat.cmp(t, 0n), ym, 1n+xp,
                      Equal.sym(Nat, 1n+xp, ym, N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1)))),
                    {==}))))
            case 1n+zp:
              %e1 : {Int.add(Int.add.opp(_, False{}, 1n+xp, True{}, ym), Int{False{}, 1n+zp}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, 1n+zp})) : Int}
              %e2 : {Int.add.same(False{}, 0n, 1n+zp) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, 1n+zp)) : Int}
              %N.succ_inj(xp, zp,
                Equal.trans(Nat, 1n+xp, ym, 1n+zp,
                  N.cmp_eq(1n+xp, ym, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+xp, ym), e1)),
                  N.cmp_eq(ym, 1n+zp, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, 1n+zp), e2)))) : {Int{False{}, 1n+_} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
              %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{False{}, 1n+xp} == Int{False{}, 1n+_} : Int}
              {==}

# FFT: x >= 0, y >= 0, z <= 0
# zero-left sub-case: an opposite-sign sum w == 0 + w (w is canonical)
law Int.add.assoc.fft.zl:
  for c: Cmp
  for +am: Nat
  for +zm: Nat
  for +e: {c == Nat.cmp(am, zm) : Cmp}
  {Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm) == Int.add(Int{False{}, 0n}, Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : Int}

def Int.add.assoc.fft.zl(c, am, zm, e):
  match c:
    case EQ{}:
      %e : {Int.add.opp(_, False{}, am, True{}, zm) == Int.add(Int{False{}, 0n}, Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : Int}
      %e : {Int{False{}, 0n} == Int.add(Int{False{}, 0n}, Int.add.opp(_, False{}, am, True{}, zm)) : Int}
      {==}
    case GT{}:
      %e : {Int.add.opp(_, False{}, am, True{}, zm) == Int.add(Int{False{}, 0n}, Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : Int}
      %e : {Int{False{}, Nat.sub(am, zm)} == Int.add(Int{False{}, 0n}, Int.add.opp(_, False{}, am, True{}, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {Int{False{}, _} == Int.mk(False{}, Nat.sub(am, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {Int{False{}, 1n+Nat.sub(am, 1n+zm)} == Int.mk(False{}, _) : Int}
      {==}
    case LT{}:
      %e : {Int.add.opp(_, False{}, am, True{}, zm) == Int.add(Int{False{}, 0n}, Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : Int}
      %e : {Int{True{}, Nat.sub(zm, am)} == Int.add(Int{False{}, 0n}, Int.add.opp(_, False{}, am, True{}, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {Int{True{}, _} == Int.add(Int{False{}, 0n}, Int{True{}, Nat.sub(zm, am)}) : Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {Int{True{}, 1n+Nat.sub(zm, 1n+am)} == Int.add(Int{False{}, 0n}, Int{True{}, _}) : Int}
      {==}

# FFT, xm = 1+xp sub-case: c1 = cmp(1+(xp+ym), zm), c2 = cmp(ym, zm)
law Int.add.assoc.fft.pos:
  for +c1: Cmp
  for +c2: Cmp
  for +xp: Nat
  for +ym: Nat
  for +zm: Nat
  for +e1: {c1 == Nat.cmp(1n+Nat.add(xp, ym), zm) : Cmp}
  for +e2: {c2 == Nat.cmp(ym, zm) : Cmp}
  {Int.add(Int.add(Int{False{}, 1n+xp}, Int{False{}, ym}), Int{True{}, zm}) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}

def Int.add.assoc.fft.pos(c1, c2, xp, ym, zm, e1, e2):
  match c1 c2:
    case GT{} GT{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(GT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.add(1n+xp, Nat.sub(ym, zm)), N.ci5(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2))) : {Int{False{}, _} == Int{False{}, 1n+Nat.add(xp, Nat.sub(ym, zm))} : Int}
      {==}
    case GT{} EQ{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(GT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int{False{}, Nat.sub(1n+Nat.add(xp, ym), _)} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp, N.add_sub_cancel(1n+xp, ym)) : {Int{False{}, _} == Int{False{}, 1n+Nat.add(xp, 0n)} : Int}
      %Equal.sym(Nat, Nat.add(xp, 0n), xp, N.add_zero(xp)) : {Int{False{}, 1n+xp} == Int{False{}, 1n+_} : Int}
      {==}
    case GT{} LT{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(GT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), GT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), GT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {Int{False{}, Nat.sub(1n+Nat.add(xp, ym), zm)} == Int.add.opp(_, False{}, 1n+xp, True{}, Nat.sub(zm, ym)) : Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.sub(1n+xp, Nat.sub(zm, ym)), N.ci6(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)), Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1))) : {Int{False{}, _} == Int{False{}, Nat.sub(1n+xp, Nat.sub(zm, ym))} : Int}
      {==}
    case EQ{} GT{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      Empty.absurd({Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(GT{}, False{}, ym, True{}, zm)) : Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case EQ{} EQ{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      Empty.absurd({Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(EQ{}, False{}, ym, True{}, zm)) : Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case EQ{} LT{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(EQ{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), EQ{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(1n+xp, 1n+xp), EQ{},
          Equal.cong(Nat, Cmp, t => Nat.cmp(1n+xp, t), Nat.sub(zm, ym), 1n+xp,
            Equal.trans(Nat, Nat.sub(zm, ym), Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp,
              Equal.cong(Nat, Nat, t => Nat.sub(t, ym), zm, Nat.add(1n+xp, ym),
                Equal.sym(Nat, Nat.add(1n+xp, ym), zm, N.cmp_eq(1n+Nat.add(xp, ym), zm, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))),
              N.add_sub_cancel(1n+xp, ym))),
          N.cmp_refl(1n+xp)))
        : {Int{False{}, 0n} == Int.add.opp(_, False{}, 1n+xp, True{}, Nat.sub(zm, ym)) : Int}
      {==}
    case LT{} GT{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      Empty.absurd({Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(GT{}, False{}, ym, True{}, zm)) : Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case LT{} EQ{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      Empty.absurd({Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(EQ{}, False{}, ym, True{}, zm)) : Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case LT{} LT{}:
      %e1 : {Int.add.opp(_, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}
      %e2 : {Int.add.opp(LT{}, False{}, 1n+Nat.add(xp, ym), True{}, zm) == Int.add(Int{False{}, 1n+xp}, Int.add.opp(_, False{}, ym, True{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), LT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), LT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, LT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {Int{True{}, Nat.sub(zm, 1n+Nat.add(xp, ym))} == Int.add.opp(_, False{}, 1n+xp, True{}, Nat.sub(zm, ym)) : Int}
      %Equal.sym(Nat, Nat.sub(zm, Nat.add(1n+xp, ym)), Nat.sub(Nat.sub(zm, ym), 1n+xp), N.ci7(1n+xp, ym, zm)) : {Int{True{}, _} == Int{True{}, Nat.sub(Nat.sub(zm, ym), 1n+xp)} : Int}
      {==}

# FFT: x >= 0, y >= 0, z <= 0
law Int.add.assoc.fft:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{False{}, xm}, Int{False{}, ym}), Int{True{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}

def Int.add.assoc.fft(xm, ym, zm):
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
          Int.add.assoc.fft.zl(Nat.cmp(1n+yp, zm), 1n+yp, zm, {==})
    case 1n+xp:
      Int.add.assoc.fft.pos(Nat.cmp(1n+Nat.add(xp, ym), zm), Nat.cmp(ym, zm), xp, ym, zm, {==}, {==})

# Int.add.assoc.rev: associativity of the reversed triple gives associativity
law Int.add.assoc.rev:
  for +x: Int
  for +y: Int
  for +z: Int
  for +e: {Int.add(Int.add(z, y), x) == Int.add(z, Int.add(y, x)) : Int}
  {Int.add(Int.add(x, y), z) == Int.add(x, Int.add(y, z)) : Int}

def Int.add.assoc.rev(x, y, z, e):
  Equal.trans(Int,
    Int.add(Int.add(x, y), z),
    Int.add(z, Int.add(x, y)),
    Int.add(x, Int.add(y, z)),
    Int.add_comm(Int.add(x, y), z),
    Equal.trans(Int,
      Int.add(z, Int.add(x, y)),
      Int.add(z, Int.add(y, x)),
      Int.add(x, Int.add(y, z)),
      Equal.cong(Int, Int, v => Int.add(z, v),
        Int.add(x, y), Int.add(y, x), Int.add_comm(x, y)),
      Equal.trans(Int,
        Int.add(z, Int.add(y, x)),
        Int.add(Int.add(z, y), x),
        Int.add(x, Int.add(y, z)),
        Equal.sym(Int,
          Int.add(Int.add(z, y), x),
          Int.add(z, Int.add(y, x)),
          e),
        Equal.trans(Int,
          Int.add(Int.add(z, y), x),
          Int.add(x, Int.add(z, y)),
          Int.add(x, Int.add(y, z)),
          Int.add_comm(Int.add(z, y), x),
          Equal.cong(Int, Int, v => Int.add(x, v),
            Int.add(z, y), Int.add(y, z), Int.add_comm(z, y))))))

# TFF: x <= 0, y >= 0, z >= 0 (reverse of FFT)
law Int.add.assoc.tff:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{False{}, ym}), Int{False{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{False{}, zm})) : Int}

def Int.add.assoc.tff(xm, ym, zm):
  Int.add.assoc.rev(Int{True{}, xm}, Int{False{}, ym}, Int{False{}, zm}, Int.add.assoc.fft(zm, ym, xm))

# TTF: x <= 0, y <= 0, z >= 0 (sign mirror of FFT)
law Int.add.assoc.ttf.zl:
  for c: Cmp
  for +am: Nat
  for +zm: Nat
  for +e: {c == Nat.cmp(am, zm) : Cmp}
  {Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm) == Int.add(Int{True{}, 0n}, Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : Int}

def Int.add.assoc.ttf.zl(c, am, zm, e):
  match c:
    case EQ{}:
      %e : {Int.add.opp(_, True{}, am, False{}, zm) == Int.add(Int{True{}, 0n}, Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : Int}
      %e : {Int{False{}, 0n} == Int.add(Int{True{}, 0n}, Int.add.opp(_, True{}, am, False{}, zm)) : Int}
      {==}
    case GT{}:
      %e : {Int.add.opp(_, True{}, am, False{}, zm) == Int.add(Int{True{}, 0n}, Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : Int}
      %e : {Int{True{}, Nat.sub(am, zm)} == Int.add(Int{True{}, 0n}, Int.add.opp(_, True{}, am, False{}, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {Int{True{}, _} == Int.mk(True{}, Nat.sub(am, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(am, zm), 1n+Nat.sub(am, 1n+zm), N.sub_pos(am, zm, Equal.sym(Cmp, GT{}, Nat.cmp(am, zm), e))) : {Int{True{}, 1n+Nat.sub(am, 1n+zm)} == Int.mk(True{}, _) : Int}
      {==}
    case LT{}:
      %e : {Int.add.opp(_, True{}, am, False{}, zm) == Int.add(Int{True{}, 0n}, Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : Int}
      %e : {Int{False{}, Nat.sub(zm, am)} == Int.add(Int{True{}, 0n}, Int.add.opp(_, True{}, am, False{}, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {Int{False{}, _} == Int.add(Int{True{}, 0n}, Int{False{}, Nat.sub(zm, am)}) : Int}
      %Equal.sym(Nat, Nat.sub(zm, am), 1n+Nat.sub(zm, 1n+am), N.sub_pos(zm, am, N.cmp_gt_of_lt(am, zm, Equal.sym(Cmp, LT{}, Nat.cmp(am, zm), e)))) : {Int{False{}, 1n+Nat.sub(zm, 1n+am)} == Int.add(Int{True{}, 0n}, Int{False{}, _}) : Int}
      {==}

# TTF, xm = 1+xp sub-case: c1 = cmp(1+(xp+ym), zm), c2 = cmp(ym, zm)
law Int.add.assoc.ttf.pos:
  for c1: Cmp
  for c2: Cmp
  for +xp: Nat
  for +ym: Nat
  for +zm: Nat
  for +e1: {c1 == Nat.cmp(1n+Nat.add(xp, ym), zm) : Cmp}
  for +e2: {c2 == Nat.cmp(ym, zm) : Cmp}
  {Int.add(Int.add(Int{True{}, 1n+xp}, Int{True{}, ym}), Int{False{}, zm}) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}

def Int.add.assoc.ttf.pos(c1, c2, xp, ym, zm, e1, e2):
  match c1 c2:
    case GT{} GT{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(GT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.add(1n+xp, Nat.sub(ym, zm)), N.ci5(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2))) : {Int{True{}, _} == Int{True{}, 1n+Nat.add(xp, Nat.sub(ym, zm))} : Int}
      {==}
    case GT{} EQ{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(GT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      %N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)) : {Int{True{}, Nat.sub(1n+Nat.add(xp, ym), _)} == Int.add(Int{True{}, 1n+xp}, Int{False{}, 0n}) : Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp, N.add_sub_cancel(1n+xp, ym)) : {Int{True{}, _} == Int.add(Int{True{}, 1n+xp}, Int{False{}, 0n}) : Int}
      {==}
    case GT{} LT{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(GT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), GT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), GT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {Int{True{}, Nat.sub(1n+Nat.add(xp, ym), zm)} == Int.add.opp(_, True{}, 1n+xp, False{}, Nat.sub(zm, ym)) : Int}
      %Equal.sym(Nat, Nat.sub(Nat.add(1n+xp, ym), zm), Nat.sub(1n+xp, Nat.sub(zm, ym)), N.ci6(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)), Equal.sym(Cmp, GT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1))) : {Int{True{}, _} == Int{True{}, Nat.sub(1n+xp, Nat.sub(zm, ym))} : Int}
      {==}
    case EQ{} GT{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      Empty.absurd({Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(GT{}, True{}, ym, False{}, zm)) : Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case EQ{} EQ{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      Empty.absurd({Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(EQ{}, True{}, ym, False{}, zm)) : Int},
        N.eq_ne_gt(Equal.trans(Cmp, EQ{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case EQ{} LT{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(EQ{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), EQ{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(1n+xp, 1n+xp), EQ{},
          Equal.cong(Nat, Cmp, t => Nat.cmp(1n+xp, t), Nat.sub(zm, ym), 1n+xp,
            Equal.trans(Nat, Nat.sub(zm, ym), Nat.sub(Nat.add(1n+xp, ym), ym), 1n+xp,
              Equal.cong(Nat, Nat, t => Nat.sub(t, ym), zm, Nat.add(1n+xp, ym),
                Equal.sym(Nat, Nat.add(1n+xp, ym), zm, N.cmp_eq(1n+Nat.add(xp, ym), zm, Equal.sym(Cmp, EQ{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))),
              N.add_sub_cancel(1n+xp, ym))),
          N.cmp_refl(1n+xp)))
        : {Int{False{}, 0n} == Int.add.opp(_, True{}, 1n+xp, False{}, Nat.sub(zm, ym)) : Int}
      {==}
    case LT{} GT{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      Empty.absurd({Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(GT{}, True{}, ym, False{}, zm)) : Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          N.cmp_gt_add_left(1n+xp, ym, zm, Equal.sym(Cmp, GT{}, Nat.cmp(ym, zm), e2)))))
    case LT{} EQ{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      Empty.absurd({Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(EQ{}, True{}, ym, False{}, zm)) : Int},
        N.lt_ne_gt(Equal.trans(Cmp, LT{}, Nat.cmp(Nat.add(1n+xp, ym), zm), GT{}, e1,
          Equal.trans(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(Nat.add(1n+xp, ym), ym), GT{},
            Equal.cong(Nat, Cmp, t => Nat.cmp(Nat.add(1n+xp, ym), t), zm, ym,
              Equal.sym(Nat, ym, zm, N.cmp_eq(ym, zm, Equal.sym(Cmp, EQ{}, Nat.cmp(ym, zm), e2)))),
            N.cmp_gt_add(ym, xp)))))
    case LT{} LT{}:
      %e1 : {Int.add.opp(_, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}
      %e2 : {Int.add.opp(LT{}, True{}, 1n+Nat.add(xp, ym), False{}, zm) == Int.add(Int{True{}, 1n+xp}, Int.add.opp(_, True{}, ym, False{}, zm)) : Int}
      %Equal.sym(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), LT{},
        Equal.trans(Cmp, Nat.cmp(1n+xp, Nat.sub(zm, ym)), Nat.cmp(Nat.add(1n+xp, ym), zm), LT{},
          Equal.sym(Cmp, Nat.cmp(Nat.add(1n+xp, ym), zm), Nat.cmp(1n+xp, Nat.sub(zm, ym)), N.cmp_add_sub(1n+xp, ym, zm, N.cmp_gt_of_lt(ym, zm, Equal.sym(Cmp, LT{}, Nat.cmp(ym, zm), e2)))),
          Equal.sym(Cmp, LT{}, Nat.cmp(1n+Nat.add(xp, ym), zm), e1)))
        : {Int{False{}, Nat.sub(zm, 1n+Nat.add(xp, ym))} == Int.add.opp(_, True{}, 1n+xp, False{}, Nat.sub(zm, ym)) : Int}
      %Equal.sym(Nat, Nat.sub(zm, Nat.add(1n+xp, ym)), Nat.sub(Nat.sub(zm, ym), 1n+xp), N.ci7(1n+xp, ym, zm)) : {Int{False{}, _} == Int{False{}, Nat.sub(Nat.sub(zm, ym), 1n+xp)} : Int}
      {==}

# TTF: x <= 0, y <= 0, z >= 0
law Int.add.assoc.ttf:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{True{}, ym}), Int{False{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}

def Int.add.assoc.ttf(xm, ym, zm):
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
          Int.add.assoc.ttf.zl(Nat.cmp(1n+yp, zm), 1n+yp, zm, {==})
    case 1n+xp:
      Int.add.assoc.ttf.pos(Nat.cmp(1n+Nat.add(xp, ym), zm), Nat.cmp(ym, zm), xp, ym, zm, {==}, {==})

# FTT: x >= 0, y <= 0, z <= 0 (reverse of TTF)
law Int.add.assoc.ftt:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{False{}, xm}, Int{True{}, ym}), Int{True{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{True{}, zm})) : Int}

def Int.add.assoc.ftt(xm, ym, zm):
  Int.add.assoc.rev(Int{False{}, xm}, Int{True{}, ym}, Int{True{}, zm}, Int.add.assoc.ttf(zm, ym, xm))

# TFT: x <= 0, y >= 0, z <= 0 (two TTF instances plus commutativity)
law Int.add.assoc.tft:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{False{}, ym}), Int{True{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}

def Int.add.assoc.tft(xm, ym, zm):
  Equal.trans(Int,
    Int.add(Int.add(Int{True{}, xm}, Int{False{}, ym}), Int{True{}, zm}),
    Int.add(Int{True{}, zm}, Int.add(Int{True{}, xm}, Int{False{}, ym})),
    Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})),
    Int.add_comm(Int.add(Int{True{}, xm}, Int{False{}, ym}), Int{True{}, zm}),
    Equal.trans(Int,
      Int.add(Int{True{}, zm}, Int.add(Int{True{}, xm}, Int{False{}, ym})),
      Int.add(Int.add(Int{True{}, zm}, Int{True{}, xm}), Int{False{}, ym}),
      Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})),
      Equal.sym(Int,
        Int.add(Int.add(Int{True{}, zm}, Int{True{}, xm}), Int{False{}, ym}),
        Int.add(Int{True{}, zm}, Int.add(Int{True{}, xm}, Int{False{}, ym})),
        Int.add.assoc.ttf(zm, xm, ym)),
      Equal.trans(Int,
        Int.add(Int.add(Int{True{}, zm}, Int{True{}, xm}), Int{False{}, ym}),
        Int.add(Int.add(Int{True{}, xm}, Int{True{}, zm}), Int{False{}, ym}),
        Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})),
        Equal.cong(Int, Int, v => Int.add(v, Int{False{}, ym}),
          Int.add(Int{True{}, zm}, Int{True{}, xm}), Int.add(Int{True{}, xm}, Int{True{}, zm}),
          Int.add_comm(Int{True{}, zm}, Int{True{}, xm})),
        Equal.trans(Int,
          Int.add(Int.add(Int{True{}, xm}, Int{True{}, zm}), Int{False{}, ym}),
          Int.add(Int{True{}, xm}, Int.add(Int{True{}, zm}, Int{False{}, ym})),
          Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})),
          Int.add.assoc.ttf(xm, zm, ym),
          Equal.cong(Int, Int, v => Int.add(Int{True{}, xm}, v),
            Int.add(Int{True{}, zm}, Int{False{}, ym}), Int.add(Int{False{}, ym}, Int{True{}, zm}),
            Int.add_comm(Int{True{}, zm}, Int{False{}, ym}))))))

# Int.add_assoc: (x + y) + z = x + (y + z)
law Int.add_assoc:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.add(Int.add(x, y), z) == Int.add(x, Int.add(y, z)) : Int}

def Int.add_assoc(x, y, z):
  match x y z:
    case Int{False{}, xm} Int{False{}, ym} Int{False{}, zm}:
      Int.add.assoc.fff(xm, ym, zm)
    case Int{False{}, xm} Int{False{}, ym} Int{True{}, zm}:
      Int.add.assoc.fft(xm, ym, zm)
    case Int{False{}, xm} Int{True{}, ym} Int{False{}, zm}:
      Int.add.assoc.ftf(Nat.cmp(xm, ym), Nat.cmp(ym, zm), xm, ym, zm, {==}, {==})
    case Int{False{}, xm} Int{True{}, ym} Int{True{}, zm}:
      Int.add.assoc.ftt(xm, ym, zm)
    case Int{True{}, xm} Int{False{}, ym} Int{False{}, zm}:
      Int.add.assoc.tff(xm, ym, zm)
    case Int{True{}, xm} Int{False{}, ym} Int{True{}, zm}:
      Int.add.assoc.tft(xm, ym, zm)
    case Int{True{}, xm} Int{True{}, ym} Int{False{}, zm}:
      Int.add.assoc.ttf(xm, ym, zm)
    case Int{True{}, xm} Int{True{}, ym} Int{True{}, zm}:
      Int.add.assoc.ttt(xm, ym, zm)
