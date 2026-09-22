import Base

# Nat laws
# ========
#
# The arithmetic inventory base.bend does not ship, stated as open laws.
# Proofs live in nat_proofs.bend, which fills every law here via
# `def NL.<name>(...)`. All lemmas are proved by structural induction on
# the first argument, with % rewrites oriented so no Equal.sym is ever
# needed.

# add_zero: x + 0 = x
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

# add_succ: 1 + (a + b) = a + (1 + b)  (stated flipped so rewrites fire left-to-right)
law add_succ:
  for a: Nat
  for b: Nat
  {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}

# add_comm: a + b = b + a
law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

# add_assoc: (a + b) + c = a + (b + c)
law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

# add_exchange: a + (b + c) = b + (a + c)
law add_exchange:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

# mul_zero: x * 0 = 0
law mul_zero:
  for +x: Nat
  {Nat.mul(x, 0n) == 0n : Nat}

# mul_succ: a + a*b = a*(1 + b)  (stated flipped so rewrites fire left-to-right)
law mul_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}

# mul_one: a = a*1  (stated flipped so rewrites fire left-to-right)
law mul_one:
  for +a: Nat
  {a == Nat.mul(a, 1n) : Nat}

# mul_comm: a * b = b * a
law mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

# Comparison bridges
# ==================
#
# Nat.cmp returns a bare Cmp with no evidence. These lemmas reconnect a
# cmp result to arithmetic facts, so proofs that hit a stuck cmp can
# case-split on it.

# Constructor discrimination: distinct Cmp constructors are never equal.
law lt_ne_eq:
  for e: {LT{} == EQ{} : Cmp}
  Empty

law gt_ne_eq:
  for e: {GT{} == EQ{} : Cmp}
  Empty

law eq_ne_gt:
  for e: {EQ{} == GT{} : Cmp}
  Empty

law lt_ne_gt:
  for e: {LT{} == GT{} : Cmp}
  Empty

# cmp_eq: if cmp(a,b) is EQ then a == b
law cmp_eq:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {a == b : Nat}

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

# cmp_gt_sub_add: if cmp(a,b) is GT then (a - b) + b = a
law cmp_gt_sub_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

# add_comm_succ: a + (1+b) = b + (1+a)
law add_comm_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == Nat.add(b, 1n+a) : Nat}

# add_assoc_rev: a + (b + c) = (a + b) + c  (flipped twin of add_assoc)
law add_assoc_rev:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

# mul_distrib: a*b + a*c = a*(b + c)  (stated flipped)
law mul_distrib:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}

# mul_add_left: x*z + y*z = (x + y)*z
law mul_add_left:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Nat.add(Nat.mul(x, z), Nat.mul(y, z)) == Nat.mul(Nat.add(x, y), z) : Nat}

# mul_assoc: (a * b) * c = a * (b * c)
law mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

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

# sub_self: a - a = 0
law sub_self:
  for +a: Nat
  {Nat.sub(a, a) == 0n : Nat}

# add_sub_cancel: (a + b) - b = a
law add_sub_cancel:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), b) == a : Nat}

# sub_add: a - (b + c) = (a - b) - c  (holds unconditionally for truncated sub)
law sub_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.sub(a, Nat.add(b, c)) == Nat.sub(Nat.sub(a, b), c) : Nat}

# sub_sub_swap: (c - a) - b = (c - b) - a
law sub_sub_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.sub(Nat.sub(c, a), b) == Nat.sub(Nat.sub(c, b), a) : Nat}

# sub_of_add: u + v = w -> w - v = u
law sub_of_add:
  for +u: Nat
  for +v: Nat
  for +w: Nat
  for e: {Nat.add(u, v) == w : Nat}
  {Nat.sub(w, v) == u : Nat}

# mul_sub_add: a >= b -> c*(a - b) + c*b = c*a  (multiplication distributes
# over truncated subtraction, stated in the form sub-cancellation consumes)
law mul_sub_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.add(Nat.mul(c, Nat.sub(a, b)), Nat.mul(c, b)) == Nat.mul(c, a) : Nat}

# mul_sub: a >= b -> c*(a - b) = c*a - c*b
law mul_sub:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.mul(c, Nat.sub(a, b)) == Nat.sub(Nat.mul(c, a), Nat.mul(c, b)) : Nat}

# eq_ne_lt / gt_ne_lt: remaining Cmp discriminations
law eq_ne_lt:
  for e: {EQ{} == LT{} : Cmp}
  Empty

law gt_ne_lt:
  for e: {GT{} == LT{} : Cmp}
  Empty

# cmp_refl: cmp(a, a) = EQ
law cmp_refl:
  for +a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

# cmp_lt_add: a < (1+b) + a
law cmp_lt_add:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, Nat.add(1n+b, a)) == LT{} : Cmp}

# cmp_gt_add: (1+b) + a > a
law cmp_gt_add:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.add(1n+b, a), a) == GT{} : Cmp}

# cmp_add_right: adding the same k to both sides preserves cmp
law cmp_add_right:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  {Nat.cmp(Nat.add(a, k), Nat.add(b, k)) == Nat.cmp(a, b) : Cmp}

# cmp_add_left: adding the same k on the left preserves cmp
law cmp_add_left:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.add(k, a), Nat.add(k, b)) == Nat.cmp(a, b) : Cmp}

# cmp_mul_right: scaling both sides by a positive k preserves cmp
law cmp_mul_right:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  {Nat.cmp(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k)) == Nat.cmp(a, b) : Cmp}

# cmp_gt_succ: a > b -> 1+a > b
law cmp_gt_succ:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(1n+a, b) == GT{} : Cmp}

# cmp_gt_refl_succ: 1+a > a
law cmp_gt_refl_succ:
  for +a: Nat
  {Nat.cmp(1n+a, a) == GT{} : Cmp}

# cmp_gt_sub: a > b -> a > b - c
law cmp_gt_sub:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(a, Nat.sub(b, c)) == GT{} : Cmp}

# cmp_lt_sub: z > y -> y - x < z
law cmp_lt_sub:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for e: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(y, x), z) == LT{} : Cmp}

# cmp_gt_add_left: b > c -> a + b > c
law cmp_gt_add_left:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(b, c) == GT{} : Cmp}
  {Nat.cmp(Nat.add(a, b), c) == GT{} : Cmp}

# cmp_lt_add_r: a < b -> a < b + c
law cmp_lt_add_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.cmp(a, Nat.add(b, c)) == LT{} : Cmp}

# cmp_lt_succ_r: a < b -> a < 1 + b
law cmp_lt_succ_r:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.cmp(a, 1n+b) == LT{} : Cmp}

# cmp_lt_succ_self: a < 1 + a
law cmp_lt_succ_self:
  for +a: Nat
  {Nat.cmp(a, 1n+a) == LT{} : Cmp}

# cmp_sub_lt: a > 1+b -> a - (1+b) < a
law cmp_sub_lt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, 1n+b) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(a, 1n+b), a) == LT{} : Cmp}

# cmp_lt_sub_add: cmp(a,b) = LT -> (b - a) + a = b  (LT twin of cmp_gt_sub_add)
law cmp_lt_sub_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.add(Nat.sub(b, a), a) == b : Nat}

# cmp_eq_sub_add: cmp(a,b) = EQ -> (a - b) + b = a
law cmp_eq_sub_add:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

# flip_eq_lt: flip(c) = LT -> c = GT
law flip_eq_lt:
  for +c: Cmp
  for e: {Cmp.flip(c) == LT{} : Cmp}
  {c == GT{} : Cmp}

# sub_pos: a > b -> a - b = 1 + (a - (1+b))
law sub_pos:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.sub(a, b) == 1n+Nat.sub(a, 1n+b) : Nat}

# cmp_add_sub: z > y -> cmp(x + y, z) = cmp(x, z - y)
law cmp_add_sub:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for e: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.cmp(Nat.add(x, y), z) == Nat.cmp(x, Nat.sub(z, y)) : Cmp}

# cmp_sub_add: a > c -> cmp(a - c, b) = cmp(a, c + b)
law cmp_sub_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, c) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(a, c), b) == Nat.cmp(a, Nat.add(c, b)) : Cmp}

# cmp_add_same_left: cmp(a, a + b) = cmp(0, b)
law cmp_add_same_left:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, Nat.add(a, b)) == Nat.cmp(0n, b) : Cmp}

# cmp_sub_flip: c > a, c > b -> cmp(c - a, b) = flip(cmp(a, c - b))
law cmp_sub_flip:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ea: {Nat.cmp(c, a) == GT{} : Cmp}
  for eb: {Nat.cmp(c, b) == GT{} : Cmp}
  {Nat.cmp(Nat.sub(c, a), b) == Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}

# succ_inj: 1+a = 1+b -> a = b
law succ_inj:
  for +a: Nat
  for +b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

# succ_add_ne: k = (1+b) + k is impossible
law succ_add_ne:
  for +b: Nat
  for +k: Nat
  for e: {k == Nat.add(1n+b, k) : Nat}
  Empty

# add_cancel: a + k = b + k -> a = b
law add_cancel:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for e: {Nat.add(a, k) == Nat.add(b, k) : Nat}
  {a == b : Nat}

# cmp_lt_of_sub_lt: x > c, x - c < b -> x < c + b
law cmp_lt_of_sub_lt:
  for +b: Nat
  for +c: Nat
  for +x: Nat
  for e1: {Nat.cmp(x, c) == GT{} : Cmp}
  for e2: {Nat.cmp(Nat.sub(x, c), b) == LT{} : Cmp}
  {Nat.cmp(x, Nat.add(c, b)) == LT{} : Cmp}

# cmp_zero_gt: cmp(0, x) = GT is impossible
law cmp_zero_gt:
  for +x: Nat
  for e: {Nat.cmp(0n, x) == GT{} : Cmp}
  Empty

# ge_sub_add: a >= b (stated as 1+a > b) -> (a - b) + b = a
law ge_sub_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(1n+a, b) == GT{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

# ci1aux .. ci1: a >= b, c > b -> (a - b) + c = a + (c - b)
# (via cancellation of b on the right; a >= b is stated as cmp(1+a, b) = GT)
law ci1aux:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(1n+a, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(c, b) == GT{} : Cmp}
  {Nat.add(Nat.add(Nat.sub(a, b), c), b) == Nat.add(Nat.add(a, Nat.sub(c, b)), b) : Nat}

law ci1:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(1n+a, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(c, b) == GT{} : Cmp}
  {Nat.add(Nat.sub(a, b), c) == Nat.add(a, Nat.sub(c, b)) : Nat}

# ci2aux .. ci2: a > c -> a - (a - c) = c  (via cancellation of a - c)
law ci2aux:
  for +a: Nat
  for +c: Nat
  for +e: {Nat.cmp(a, c) == GT{} : Cmp}
  {Nat.add(Nat.sub(1n+a, Nat.sub(a, c)), Nat.sub(a, c)) == Nat.add(1n+c, Nat.sub(a, c)) : Nat}

law ci2:
  for +a: Nat
  for +c: Nat
  for +e: {Nat.cmp(a, c) == GT{} : Cmp}
  {Nat.sub(a, Nat.sub(a, c)) == c : Nat}

# ci3aux .. ci3: y > x, y > z, y - x < z -> z - (y - x) = x - (y - z)
law ci3aux:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  for +e3: {Nat.cmp(Nat.sub(y, x), z) == LT{} : Cmp}
  {Nat.add(Nat.sub(z, Nat.sub(y, x)), y) == Nat.add(Nat.sub(x, Nat.sub(y, z)), y) : Nat}

law ci3:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  for +e3: {Nat.cmp(Nat.sub(y, x), z) == LT{} : Cmp}
  {Nat.sub(z, Nat.sub(y, x)) == Nat.sub(x, Nat.sub(y, z)) : Nat}

# ci4aux .. ci4: y > x, z > y -> z - (y - x) = x + (z - y)
law ci4aux:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.add(Nat.sub(z, Nat.sub(y, x)), y) == Nat.add(Nat.add(x, Nat.sub(z, y)), y) : Nat}

law ci4:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(y, x) == GT{} : Cmp}
  for +e2: {Nat.cmp(z, y) == GT{} : Cmp}
  {Nat.sub(z, Nat.sub(y, x)) == Nat.add(x, Nat.sub(z, y)) : Nat}

# ci5aux .. ci5: b > c -> (a + b) - c = a + (b - c)
law ci5aux:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e: {Nat.cmp(b, c) == GT{} : Cmp}
  {Nat.add(Nat.sub(Nat.add(a, b), c), c) == Nat.add(Nat.add(a, Nat.sub(b, c)), c) : Nat}

law ci5:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e: {Nat.cmp(b, c) == GT{} : Cmp}
  {Nat.sub(Nat.add(a, b), c) == Nat.add(a, Nat.sub(b, c)) : Nat}

# ci6aux .. ci6: c > b, a + b > c -> (a + b) - c = a - (c - b)
law ci6aux:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(c, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.add(a, b), c) == GT{} : Cmp}
  {Nat.add(Nat.sub(Nat.add(a, b), c), c) == Nat.add(Nat.sub(a, Nat.sub(c, b)), c) : Nat}

law ci6:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e1: {Nat.cmp(c, b) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.add(a, b), c) == GT{} : Cmp}
  {Nat.sub(Nat.add(a, b), c) == Nat.sub(a, Nat.sub(c, b)) : Nat}

# ci7: c - (a + b) = (c - b) - a  (unconditional)
law ci7:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.sub(c, Nat.add(a, b)) == Nat.sub(Nat.sub(c, b), a) : Nat}

# ci9aux .. ci9: x > c, x - c < b -> (c + b) - x = b - (x - c)
law ci9aux:
  for +b: Nat
  for +c: Nat
  for +x: Nat
  for +e1: {Nat.cmp(x, c) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.sub(x, c), b) == LT{} : Cmp}
  {Nat.add(Nat.sub(Nat.add(c, b), x), x) == Nat.add(Nat.sub(b, Nat.sub(x, c)), x) : Nat}

law ci9:
  for +b: Nat
  for +c: Nat
  for +x: Nat
  for +e1: {Nat.cmp(x, c) == GT{} : Cmp}
  for +e2: {Nat.cmp(Nat.sub(x, c), b) == LT{} : Cmp}
  {Nat.sub(Nat.add(c, b), x) == Nat.sub(b, Nat.sub(x, c)) : Nat}

# ci10: 1+a > x -> (1 + (a + b)) - x = 1 + ((a - x) + b)
law ci10:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  for e: {Nat.cmp(1n+a, x) == GT{} : Cmp}
  {Nat.sub(1n+Nat.add(a, b), x) == 1n+Nat.add(Nat.sub(a, x), b) : Nat}

# ci8aux .. ci8: x > y, y > z -> (x - y) + z = x - (y - z)
law ci8aux:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(x, y) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  {Nat.add(Nat.add(Nat.sub(x, y), z), Nat.sub(y, z)) == Nat.add(Nat.sub(x, Nat.sub(y, z)), Nat.sub(y, z)) : Nat}

law ci8:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +e1: {Nat.cmp(x, y) == GT{} : Cmp}
  for +e2: {Nat.cmp(y, z) == GT{} : Cmp}
  {Nat.add(Nat.sub(x, y), z) == Nat.sub(x, Nat.sub(y, z)) : Nat}

# cmp_gt_of_lt / cmp_lt_of_gt: flip a comparison evidence
law cmp_gt_of_lt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.cmp(b, a) == GT{} : Cmp}

law cmp_lt_of_gt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(b, a) == LT{} : Cmp}

# flip_flip: flip is an involution
law flip_flip:
  for +c: Cmp
  {Cmp.flip(Cmp.flip(c)) == c : Cmp}

# cmp_sub_gt_self: a > 1+b -> a > a - (1+b)
law cmp_sub_gt_self:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, 1n+b) == GT{} : Cmp}
  {Nat.cmp(a, Nat.sub(a, 1n+b)) == GT{} : Cmp}

# cmp_lt_zero: cmp(a, 0) = LT is impossible
law cmp_lt_zero:
  for +a: Nat
  for e: {Nat.cmp(a, 0n) == LT{} : Cmp}
  Empty

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

# Nat.divmod
# ==========
#
# base.bend's Nat.divmod.go(n, m, d, r) counts n down, either bumping r (while
# m has room) or rolling r into d (when m runs out), and Nat.divmod(a, b) =
# Nat.divmod.go(a, bp, 0, 0) for b = 1 + bp. So the loop state carries two
# facts that survive every step:
#
#   r + (1 + m) = b     the roll-over budget -- r is one short of rolling over
#   d*b + r + n = a     the total the loop is accounting for
#
# and at n = 0 the surviving state (d, r) satisfies d*b + r = a, i.e. division.
#
# The two facts are stated separately rather than as one conjunction so that
# each induction is readable; both are inductions on n, the fuel, which is why
# n is the first binder (Bend's descent check is structural, left-to-right).
#
# Shape notes, each of which buys a rewrite:
#   - r + n (not n + r) is the "clock": after the m-bump step it becomes
#     1 + (r + np), which is exactly what `add_succ` converts to the state's
#     new spelling, while n + r would leave a stuck term behind.
#   - 1 + m (not m + 1): 1 + m is a constructor, so the budget hypothesis of
#     the m-bump recursive call is convertible, and `cmp(0, 1 + m) = LT` in
#     the remainder bound falls out of reduction.

# divmod.go.spec: the Nat.divmod.go loop invariant. The conclusion projects
# the result with Nat.div.fin / Nat.mod.fin because a law statement cannot
# destructure a pair; e1 is the budget r + (1 + m) = b.
law divmod.go.spec:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +b: Nat
  for +e1: {Nat.add(r, Nat.add(1n, m)) == b : Nat}
  {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), b), Nat.mod.fin(Nat.divmod.go(n, m, d, r))) == Nat.add(Nat.mul(d, b), Nat.add(r, n)) : Nat}

# divmod.go.mod_lt: the companion bound. The budget alone is what bounds the
# remainder: b = r + (1 + m) says r is strictly below b, so no arithmetic on d
# or n is needed here at all.
law divmod.go.mod_lt:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +b: Nat
  for +e1: {Nat.add(r, Nat.add(1n, m)) == b : Nat}
  {Nat.cmp(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), b) == LT{} : Cmp}

# div_add_mod: a = (a / (1+b))* (1+b) + a % (1+b). Stated for the divisor
# written as 1 + b so no positivity hypothesis is needed at all: that spelling
# is exactly what Nat.divmod matches on.
law div_add_mod:
  for +a: Nat
  for +b: Nat
  {Nat.add(Nat.mul(Nat.div(a, 1n+b), 1n+b), Nat.mod(a, 1n+b)) == a : Nat}

# mod_lt: a % (1+b) < 1+b
law mod_lt:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.mod(a, 1n+b), 1n+b) == LT{} : Cmp}
