import Base
import ./nat.bend as N

# Int: signed integers as sign + magnitude
# ========================================
#
# sign = False means non-negative, True means non-positive. Constructors
# may build a non-canonical zero Int{True{}, 0n}, but every *operation*
# canonicalizes (Int.mk, and the EQ branch of Int.add.opp), so results
# compare correctly with ==.
#
# Laws are stated here and left open; int_proofs.bend fills them via
# `def I.<name>(...)`.

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

# Like every other operation, Int.mul canonicalizes through Int.mk: without
# that it hands back Int{xs, 0n} for a zero product, and no ring law can hold
# of a value that is 0 only by convention. (Checked counterexample, before the
# fix: Int.mul(Int{True,0}, Int{False,1} + Int{True,1}) = Int{True,0} but
# Int.mul(Int{True,0},Int{False,1}) + Int.mul(Int{True,0},Int{True,1}) =
# Int{False,0}.) See mul_distrib below.
def Int.mul(x: Int, y: Int) -> Int:
  Int{xs, xm} = x
  Int{ys, ym} = y
  Int.mk(Bool.xor(xs, ys), Nat.mul(xm, ym))

# Unfolding Int.mul on a canonicalized argument.
# =============================================
#
# Int.mk matches on its magnitude, so Int.mk(s, m) is a *stuck* term while m is
# symbolic -- and Int.mul destructures both of its arguments, so
# Int.mul(Int.mk(s, m), y) does not reduce either. Every composite product
# hits this, so the case split it needs is packaged as a law instead. Stated
# flipped (RHS = the stuck form) so `%e` rewrites left-to-right; see
# PROVING.md.

# Int.mul.mk_left: m * y, with m's sign forced by Int.mk
law Int.mul.mk_left:
  for +s: Bool
  for +m: Nat
  for +ys: Bool
  for +ym: Nat
  {Int.mk(Bool.xor(s, ys), Nat.mul(m, ym)) == Int.mul(Int.mk(s, m), Int{ys, ym}) : Int}

# Int.mul.mk_right: x * m, with m's sign forced by Int.mk
law Int.mul.mk_right:
  for +xs: Bool
  for +xm: Nat
  for +s: Bool
  for +m: Nat
  {Int.mk(Bool.xor(xs, s), Nat.mul(xm, m)) == Int.mul(Int{xs, xm}, Int.mk(s, m)) : Int}

# xor_comm: xor is commutative
law xor_comm:
  for +a: Bool
  for +b: Bool
  {Bool.xor(a, b) == Bool.xor(b, a) : Bool}

# Int.mul_comm: x * y = y * x
law Int.mul_comm:
  for +x: Int
  for +y: Int
  {Int.mul(x, y) == Int.mul(y, x) : Int}

# Int.add.opp_comm: opposite-sign addition commutes (via Cmp.flip)
law Int.add.opp_comm:
  for +c: Cmp
  for +xs: Bool
  for +ys: Bool
  for +xm: Nat
  for +ym: Nat
  {Int.add.opp(c, xs, xm, ys, ym) == Int.add.opp(N.Cmp.flip(c), ys, ym, xs, xm) : Int}

# Int.add.same_comm: same-sign addition commutes
law Int.add.same_comm:
  for +s: Bool
  for +xm: Nat
  for +ym: Nat
  {Int.add.same(s, xm, ym) == Int.add.same(s, ym, xm) : Int}

# Int.add_comm: x + y = y + x
law Int.add_comm:
  for +x: Int
  for +y: Int
  {Int.add(x, y) == Int.add(y, x) : Int}

# xor_assoc: xor is associative
law xor_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}

# Int.mul_assoc: (x * y) * z = x * (y * z)
law Int.mul_assoc:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.mul(Int.mul(x, y), z) == Int.mul(x, Int.mul(y, z)) : Int}

# Int.mul_swap: (a * b) * c = (a * c) * b
law Int.mul_swap:
  for +a: Int
  for +b: Int
  for +c: Int
  {Int.mul(Int.mul(a, b), c) == Int.mul(Int.mul(a, c), b) : Int}

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

# TTT: all non-positive
law Int.add.assoc.ttt:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{True{}, ym}), Int{True{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{True{}, ym}, Int{True{}, zm})) : Int}

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

# FFT: x >= 0, y >= 0, z <= 0
# zero-left sub-case: an opposite-sign sum w == 0 + w (w is canonical)
law Int.add.assoc.fft.zl:
  for c: Cmp
  for +am: Nat
  for +zm: Nat
  for +e: {c == Nat.cmp(am, zm) : Cmp}
  {Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm) == Int.add(Int{False{}, 0n}, Int.add.opp(Nat.cmp(am, zm), False{}, am, True{}, zm)) : Int}

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

# FFT: x >= 0, y >= 0, z <= 0
law Int.add.assoc.fft:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{False{}, xm}, Int{False{}, ym}), Int{True{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}

# Int.add.assoc.rev: associativity of the reversed triple gives associativity
law Int.add.assoc.rev:
  for +x: Int
  for +y: Int
  for +z: Int
  for +e: {Int.add(Int.add(z, y), x) == Int.add(z, Int.add(y, x)) : Int}
  {Int.add(Int.add(x, y), z) == Int.add(x, Int.add(y, z)) : Int}

# TFF: x <= 0, y >= 0, z >= 0 (reverse of FFT)
law Int.add.assoc.tff:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{False{}, ym}), Int{False{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{False{}, zm})) : Int}

# TTF: x <= 0, y <= 0, z >= 0 (sign mirror of FFT)
law Int.add.assoc.ttf.zl:
  for c: Cmp
  for +am: Nat
  for +zm: Nat
  for +e: {c == Nat.cmp(am, zm) : Cmp}
  {Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm) == Int.add(Int{True{}, 0n}, Int.add.opp(Nat.cmp(am, zm), True{}, am, False{}, zm)) : Int}

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

# TTF: x <= 0, y <= 0, z >= 0
law Int.add.assoc.ttf:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{True{}, ym}), Int{False{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{True{}, ym}, Int{False{}, zm})) : Int}

# FTT: x >= 0, y <= 0, z <= 0 (reverse of TTF)
law Int.add.assoc.ftt:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{False{}, xm}, Int{True{}, ym}), Int{True{}, zm}) == Int.add(Int{False{}, xm}, Int.add(Int{True{}, ym}, Int{True{}, zm})) : Int}

# TFT: x <= 0, y >= 0, z <= 0 (two TTF instances plus commutativity)
law Int.add.assoc.tft:
  for +xm: Nat
  for +ym: Nat
  for +zm: Nat
  {Int.add(Int.add(Int{True{}, xm}, Int{False{}, ym}), Int{True{}, zm}) == Int.add(Int{True{}, xm}, Int.add(Int{False{}, ym}, Int{True{}, zm})) : Int}

# Int.add_assoc: (x + y) + z = x + (y + z)
law Int.add_assoc:
  for +x: Int
  for +y: Int
  for +z: Int
  {Int.add(Int.add(x, y), z) == Int.add(x, Int.add(y, z)) : Int}
