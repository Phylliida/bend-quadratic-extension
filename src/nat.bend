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

# The cross-sum lemmas
# ====================
#
# Int.canon.eqv.bwd -- "xp + yn = yp + xn forces canon x = canon y" -- needs
# two Nat facts, one per shape of its case split (the two comparisons agree, or
# they disagree):
#
#   - cross_gt_gt: the comparisons agree and are GT, so both canon forms are a
#     difference against zero and the cross sum has to yield the difference
#     itself.
#   - cross_cmp: the comparisons disagree, so the cross sum is impossible.
#     Stated as the comparison equation {c1 == c2} so the caller refutes it
#     with whichever of the six discrimination laws fits its branch
#     (gt_ne_eq, gt_ne_lt, ...) -- one lemma for all six branches, and none of
#     them needs any arithmetic: adding the same amount to both sides preserves
#     a comparison (cmp_add_right), so the cross sum carries cmp(xp,xn) to
#     cmp(yp,yn) by congruence and commutation alone.

# cross_gt_gt: sub(xp,xn) = sub(yp,yn) from the cross sum, when both
# comparisons are GT. A = sub(xp,xn) and B = sub(yp,yn) are the two canon
# coordinates, and A + xn = xp (B + yn = yp) by cmp_gt_sub_add, so the cross
# sum is an equation about A and B whose common add(xn,yn) cancels.
law cross_gt_gt:
  for +xp: Nat
  for +xn: Nat
  for +yp: Nat
  for +yn: Nat
  for +e1: {Nat.cmp(xp, xn) == GT{} : Cmp}
  for +e2: {Nat.cmp(yp, yn) == GT{} : Cmp}
  for +e: {Nat.add(xp, yn) == Nat.add(yp, xn) : Nat}
  {Nat.sub(xp, xn) == Nat.sub(yp, yn) : Nat}

# cross_cmp: the cross sum forces the two comparisons to agree. Both sides of
# the conclusion are the *same* comparison of the *same* two sums: c1 is
# reached by scaling cmp(xp,xn) on the right (cmp_add_right), c2 through the
# hypothesis, commutation and cmp_add_right on the other pair. d is not a
# parameter here -- the branches' evidence is worthless, the equation itself is
# what the caller refutes.
law cross_cmp:
  for c1: Cmp
  for +xp: Nat
  for +xn: Nat
  for c2: Cmp
  for +yp: Nat
  for +yn: Nat
  for +e1: {c1 == Nat.cmp(xp, xn) : Cmp}
  for +e2: {c2 == Nat.cmp(yp, yn) : Cmp}
  for +e: {Nat.add(xp, yn) == Nat.add(yp, xn) : Nat}
  {c1 == c2 : Cmp}

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

# Exact division
# ==============
#
# div_add_mod and mod_lt turn (div, mod) into a quotient-and-remainder *pair*
# for any dividend. What the Rat normalization needs on top of that is the
# other direction -- an exact division, i.e. the quotient of a dividend known
# to be a multiple:
#
#     div(a, g) == q   when   a == g * q,   g = 1 + b
#
# and its scaled form, div(a*s, g*s) == q for s = 1 + k, which is what makes
# normalization natural under scaling (gcd(m*k, d*k) = k*gcd(m,d) leaves the
# two quotients alone).
#
# The whole content is *uniqueness* of the quotient-and-remainder pair, which
# is div_unique below: two representations of the same a with remainders below
# g force equal quotients. It needs no division correctness at all -- only
# cancellation and the ordering facts, because a strictly smaller quotient
# would leave a difference of at least g to be made up by a remainder that is
# smaller than g.

# lt_ne_add: a < b and a == b + s is impossible.
#
# cmp_add_right moves the comparison to cmp(s, 0) (add_comm puts b on the left
# where add(0, b) reduces away), and cmp_lt_zero refutes that -- no sub, no
# cancellation, no induction.
law lt_ne_add:
  for +a: Nat
  for +b: Nat
  for +s: Nat
  for +e1: {Nat.cmp(a, b) == LT{} : Cmp}
  for +e2: {Nat.add(b, s) == a : Nat}
  Empty

# add_assoc_cancel: one common summand comes off both sides of an equation
# whose sides both start with it one level deep. This is the step div_unique's
# induction takes at every successor (Nat.mul on a successor is add(b0, ..), so
# the common b0 sits *inside* the left summand), and it is a law rather than an
# inline chain so that the induction stays readable.
law add_assoc_cancel:
  for +b0: Nat
  for +x: Nat
  for +r: Nat
  for +y: Nat
  for +s: Nat
  for +e: {Nat.add(Nat.add(b0, x), r) == Nat.add(Nat.add(b0, y), s) : Nat}
  {Nat.add(x, r) == Nat.add(y, s) : Nat}

# div_unique: d1*b + r1 == d2*b + r2 with both remainders below b = 1 + b0
# forces d1 == d2. This is the induction the whole exact-division block rests
# on, and it is structural on d1:
#
#   - d1 = 0: the equation reads r1 == d2*b + r2, so if d2 = 1 + d2' then
#     r1 == b + (d2'*b + r2), which lt_ne_add refutes with r1 < b; hence d2 = 0.
#   - d1 = 1 + d1': the same argument rules d2 = 0 out; for d2 = 1 + d2' both
#     sides have one factor b peeled off (Nat.mul on a successor is
#     add(b, ..)), add_cancel removes it and the induction hypothesis applies
#     to (d1', d2') at the same b and the same remainders.
#
# b is written 1 + b0 because both bounds are hypotheses of that shape (mod_lt
# states its bound about 1 + b), and because a successor is what keeps
# Nat.mul(d, 1 + b0) reducing.
law div_unique:
  for +d1: Nat
  for +r1: Nat
  for +d2: Nat
  for +r2: Nat
  for +b0: Nat
  for +e: {Nat.add(Nat.mul(d1, 1n+b0), r1) == Nat.add(Nat.mul(d2, 1n+b0), r2) : Nat}
  for +l1: {Nat.cmp(r1, 1n+b0) == LT{} : Cmp}
  for +l2: {Nat.cmp(r2, 1n+b0) == LT{} : Cmp}
  {d1 == d2 : Nat}

# div_exact: a == (1+b)*q gives div(a, 1+b) == q. One call of div_unique with
# the two representations (div(a,1+b), mod(a,1+b)) from div_add_mod and
# (q, 0) from the hypothesis.
law div_exact:
  for +a: Nat
  for +b: Nat
  for +q: Nat
  for +e: {a == Nat.mul(1n+b, q) : Nat}
  {Nat.div(a, 1n+b) == q : Nat}

# div_exact_mul: the scaled form. div(a*s, g*s) == q for s = 1 + k, from the
# same q: the scaled dividend is g*s*q up to mul_assoc/mul_comm, so div_exact
# applies to it verbatim.
law div_exact_mul:
  for +a: Nat
  for +b: Nat
  for +q: Nat
  for +k: Nat
  for +e: {a == Nat.mul(1n+b, q) : Nat}
  {Nat.div(Nat.mul(a, 1n+k), Nat.mul(1n+b, 1n+k)) == q : Nat}

# div_one: div(a, 1) == a, the case gcd = 1 of the Rat normalization. g = 1 is
# 1 + 0, so it is one call of div_exact with the hypothesis a == 1*a.
law div_one:
  for +a: Nat
  {Nat.div(a, 1n) == a : Nat}

# div_zero: 0 / d = 0, for *every* d -- and it is a law rather than a reduction
# because Nat.divmod matches on the divisor, so div(0, d) is stuck while d is a
# variable. Both of divmod's branches answer 0 for dividend 0 (the b = 0 branch
# returns the pair (0, 0), and the b = 1 + bp branch runs the loop from n = 0).
law div_zero:
  for +d: Nat
  {Nat.div(0n, d) == 0n : Nat}

# div_self: a/a = 1 for a = 1 + ap. One call of div_exact with q = 1, since
# mul_one already says a == a*1.
law div_self:
  for +ap: Nat
  {Nat.div(1n+ap, 1n+ap) == 1n : Nat}

# Difference-pair helpers
# =======================
#
# The Rat canonical form is the difference pair (sub(np,nn), sub(nn,np)), which
# always has one side zero. Moving between "the difference pair of np, nn" and
# "the raw coordinates np, nn" -- which is what Rat.mk does when it destructures
# a numerator it produced itself -- needs the three facts below.

# sub_zero_left: 0 - a = 0 (the left-hand twin of sub_zero)
law sub_zero_left:
  for +a: Nat
  {Nat.sub(0n, a) == 0n : Nat}

# sub_of_lt: a < b gives a - b = 0 -- the truncated difference is the whole
# thing. Case split on both arguments; the two impossible branches are the
# discriminations eq_ne_lt (0 vs 0) and gt_ne_lt (successor vs 0).
law sub_of_lt:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.cmp(a, b) == LT{} : Cmp}
  {Nat.sub(a, b) == 0n : Nat}

# pos_witness: 0 < n gives n == 1 + (n - 1) -- a *witness* that n is a
# successor, which is what turns a general divisor into the 1 + b spelling that
# div_exact and friends are stated over. One trans: sub_zero turns n into
# n - 0, and sub_pos (stated at b = 0) turns that into the successor form.
law pos_witness:
  for +n: Nat
  for +e: {Nat.cmp(0n, n) == LT{} : Cmp}
  {n == 1n+Nat.sub(n, 1n) : Nat}

# divides_pos: a positive multiple of g forces g to be a successor. Stated
# about a = 1 + ap (rather than cmp(0,a) = LT) because that is the spelling the
# callers have after sub_pos, and because the g = 0 branch then needs only
# mul(0,q) = 0 and a zero/successor discrimination.
law divides_pos:
  for +g: Nat
  for +q: Nat
  for +ap: Nat
  for +e: {1n+ap == Nat.mul(g, q) : Nat}
  {Nat.cmp(0n, g) == LT{} : Cmp}

# sub_diag: sub(sub(np,nn), sub(nn,np)) == sub(np,nn) -- truncating a difference
# pair's own side by its other side is a no-op, because one of the two is zero.
# The comparison is a parameter because it is what decides which side is zero:
# GT and LT reduce to sub_zero / sub_zero_left, and EQ turns the comparison into
# np == nn and collapses both sides with sub_self.
law sub_diag:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.sub(Nat.sub(np, nn), Nat.sub(nn, np)) == Nat.sub(np, nn) : Nat}

# Nat.gcd
# =======
#
# Subtractive Euclid. Nothing about the descent is structural -- each step
# replaces the larger argument by a difference, and Nat.sub of two variables
# is a computed value -- so, exactly like Nat.divmod.go, the loop counts an
# explicit fuel down from the front of its telescope. The fuel is the state's
# own measure x + y, which every step strictly reduces (both arguments stay
# positive inside the loop), so the fuel Nat.add(a, b) that Nat.gcd hands the
# loop is enough to reach a terminal state.
#
# cmp(x, y) is threaded in as a parameter for the usual reason (evidence as a
# parameter): a match scrutinee must be a parameter or a pattern-bound
# variable, never a computed value, and a body that matches a *stuck* Nat.cmp
# cannot reduce -- which would make every downstream term stuck. The proofs
# case on it, which is what puts x < y / x = y / x > y in scope as arithmetic
# evidence (cmp_gt_of_lt, cmp_lt_sub_add, ...).

# Nat.Div<g, a>: g divides a, with the quotient as a witness -- and with both
# the quotient and the equation *copyable*.
#
# This was `Exists(Nat, q => {a == Nat.mul(g, q)})` first, and the shape is not
# a style choice: it is what makes the proof writable at all. The loop step
# needs each field twice -- once to rebuild the witness for the old argument,
# once to feed divides_add -- and a Sigma's fields are linear. `Sigma<&2, &2,
# ..>` does not help (a field's *own* quantity is what counts, and Tuple's
# default is &1). The copy spelling for a live binder is a `+` re-bind, and
# there the checker stops: `+e = e` makes it re-check the field's type, a
# Sigma's dependent field type B(fst) reaches it as `App(<shared cell holding
# the lambda>, fst)` -- infer sees a cell, not a lambda -- and the whole def is
# rejected with "an annotated term (cannot infer)".
#
# Two properties of a +field make that obstacle disappear:
#   - a +field is Many at the declaration, so a plain pattern already yields it
#     Many and no re-bind is ever written;
#   - a constructor's field types mention its own earlier fields *directly*, so
#     no dependent field type is ever rebuilt as an application.
type Nat.Div<+g: Nat, +a: Nat> is Data:
  Div{+q: Nat, +e: {a == Nat.mul(g, q) : Nat}}

# Nat.divides(g, a): g divides a. A named alias so the law statements and the
# motives that rewrite over them spell the predicate once.
def Nat.divides(g: Nat, a: Nat) -> Type:
  Nat.Div<g, a>

# Nat.divides_both(g, a, b): g divides both a and b. A named pair so that the
# law statements below (and the motives that rewrite over them) stay single
# applications: "A & B" is the exists sugar wherever it follows a name, so a
# bare pair type is not writable in every position.
def Nat.divides_both(g: Nat, a: Nat, b: Nat) -> Type:
  Nat.divides(g, a) & Nat.divides(g, b)

def Nat.gcd.go(+s: Nat, +y: Nat, +c: Cmp, +x: Nat) -> Nat:
  match s:
    case 0n:
      0n
    case 1n+sp:
      match y:
        case 0n:
          x
        case 1n+yp:
          match c:
            case EQ{}:
              x
            case LT{}:
              Nat.gcd.go(sp, Nat.sub(y, x), Nat.cmp(x, Nat.sub(y, x)), x)
            case GT{}:
              Nat.gcd.go(sp, y, Nat.cmp(Nat.sub(x, y), y), Nat.sub(x, y))

# Two deviations from the sketch in PROVING.md, both found by proving:
#   - the GT step must leave the y slot alone and put the difference in the x
#     slot (the sketch has sub(x, y) in both). With the sketch's version the
#     state collapses to (x-y, x-y) and gcd(10, 4) answers 0 -- checked by
#     running both loops on literals before writing any proof.
#   - the a = 0 case (below).
#
# Nat.gcd(a, b): the loop started at x = a, y = b with fuel a + b.
#
# The a = 0 case is split out rather than left to the loop. With x = 0 and
# y > 0 the loop's LT step is a no-op (Nat.sub(y, 0) = y), so it would spin
# until the fuel ran out and then answer 0 -- but gcd(0, b) is b. Matching on
# a is the whole fix: from x >= 1 on, every step really does shrink x + y, and
# the LT step's new x is the old x.
def Nat.gcd(+a: Nat, +b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+ap:
      Nat.gcd.go(Nat.add(a, b), b, Nat.cmp(a, b), a)

# cmp_mul_right_of: transport a comparison result to the *scaled* comparison.
#
# Oriented for %: `%e` replaces occurrences of e's right side, and the goal at
# a scaled gcd call holds the scaled comparison, so the scaled term has to be
# on the right. d is a parameter so that the caller can pass the constructor
# it just matched (LT{} etc.) and have the whole match reduce.
law cmp_mul_right_of:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for d: Cmp
  for e: {d == Nat.cmp(a, b) : Cmp}
  {d == Nat.cmp(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k)) : Cmp}

# mul_sub_right: the right-scaled twin of mul_sub -- k multiplies the
# difference on the left of the equation and the minuend/subtrahend on the
# right, which is the orientation the scaled gcd branch needs (there the
# state's y slot holds sub(y*k, x*k) and the goal wants sub(y,x)*k).
law mul_sub_right:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.mul(Nat.sub(a, b), c) == Nat.sub(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

# gcd.go.scale: the loop is natural in its state under scaling by k = 1 + kp.
#
# This is the lemma that makes gcd scaling cheap: no gcd-specific reasoning,
# only the loop's own step-by-step equivariance (Nat.sub scales by mul_sub,
# Nat.cmp by cmp_mul_right). It holds for *every* fuel, including too little
# fuel, because both sides then run out together -- so there is no sufficiency
# hypothesis here.
law gcd.go.scale:
  for +s: Nat
  for +y: Nat
  for c: Cmp
  for +x: Nat
  for +kp: Nat
  for +e: {c == Nat.cmp(x, y) : Cmp}
  {Nat.gcd.go(s, Nat.mul(y, 1n+kp), Nat.cmp(Nat.mul(x, 1n+kp), Nat.mul(y, 1n+kp)), Nat.mul(x, 1n+kp)) == Nat.mul(1n+kp, Nat.gcd.go(s, y, c, x)) : Nat}

# add_mul_slack: (x + y) + (x*k + y*k) = x*(1+k) + y*(1+k).
#
# This is the "the scaled state's fuel is the unscaled fuel plus a slack"
# identity: Nat.gcd(m, d) runs the loop with fuel m + d, Nat.gcd(m*k, d*k)
# with fuel m*k + d*k, and gcd.go.fuel below trades that extra fuel for the
# scaling. Pure Nat shuffle, no hypotheses.
law add_mul_slack:
  for +x: Nat
  for +y: Nat
  for +k: Nat
  {Nat.add(Nat.add(x, y), Nat.add(Nat.mul(x, k), Nat.mul(y, k))) == Nat.add(Nat.mul(x, 1n+k), Nat.mul(y, 1n+k)) : Nat}

# gcd.slack_lt / gcd.slack_gt: the two slack identities gcd.go.fuel's step
# needs, one per branch of the loop.
#
# At each step both sides of gcd.go.fuel land on the same state, but their
# fuels are that state's "canonical" fuel plus the *same* slack u only if the
# new slack is chosen right: after a step the state measures x + y and x (for
# the LT and GT branches), so the old slack t has to be topped up with xp and
# yp respectively. These two lemmas are exactly those top-ups, stated over the
# terms that actually occur. They take the branch's comparison as evidence
# (rather than, say, a subtraction equation) because that is what the call
# sites have in hand, and because the subtraction facts then follow from
# cmp_lt_sub_add / cmp_gt_sub_add inside.
law gcd.slack_lt:
  for +xp: Nat
  for +yp: Nat
  for +t: Nat
  for +e: {Nat.cmp(1n+xp, 1n+yp) == LT{} : Cmp}
  {Nat.add(Nat.add(1n+xp, Nat.sub(yp, xp)), Nat.add(xp, t)) == Nat.add(Nat.add(xp, 1n+yp), t) : Nat}

law gcd.slack_gt:
  for +xp: Nat
  for +yp: Nat
  for +t: Nat
  for +e: {Nat.cmp(1n+xp, 1n+yp) == GT{} : Cmp}
  {Nat.add(Nat.add(1n+Nat.sub(xp, 1n+yp), 1n+yp), Nat.add(yp, t)) == Nat.add(Nat.add(xp, 1n+yp), t) : Nat}

# gcd.go.fuel: more fuel than the canonical x + y does not change the result.
#
# e2 says s1 is the canonical fuel plus a slack t and the conclusion compares
# the loop at s1 and at s1 + u, so the induction is on s1 (structural): one
# step of the loop takes s1 = 1 + sp to sp on both sides, and the *difference*
# u rides along untouched -- which is the whole point, since it is the slack
# that has to survive, not shrink.
#
# x is written 1 + xp (not x) for exactly one reason: the canonical fuel x + y
# must start with a constructor, otherwise the right-hand loop is stuck on its
# fuel match and the induction cannot start. The cost is that gcd.go.divides
# and Nat.gcd must carry the same spelling, and that the GT step has to undo
# the loop's own subtraction with sub_pos.
law gcd.go.fuel:
  for +s1: Nat
  for +y: Nat
  for c: Cmp
  for +xp: Nat
  for +t: Nat
  for +u: Nat
  for +e1: {c == Nat.cmp(1n+xp, y) : Cmp}
  for +e2: {Nat.add(Nat.add(1n+xp, y), t) == s1 : Nat}
  {Nat.gcd.go(Nat.add(s1, u), y, c, 1n+xp) == Nat.gcd.go(s1, y, c, 1n+xp) : Nat}

# divides_add: a multiple of g plus a multiple of g is a multiple of g, with
# the quotients added. This is the only arithmetic gcd.go.divides needs: the
# loop's two steps replace (x, y) by (x, y - x) or (x - y, y), and in both
# cases the original argument is the sum of the new pair.
law divides_add:
  for +g: Nat
  for +q1: Nat
  for +q2: Nat
  for +a: Nat
  for +b: Nat
  for +p1: {a == Nat.mul(g, q1) : Nat}
  for +p2: {b == Nat.mul(g, q2) : Nat}
  {Nat.add(a, b) == Nat.mul(g, Nat.add(q1, q2)) : Nat}

# gcd_scale: gcd(m*k, d*k) = k * gcd(m, d) for k = 1 + kp.
#
# The two loops are related by gcd.go.scale at one and the same fuel, and the
# leftover fuel difference (m*k + d*k against m + d) is exactly what
# gcd.go.fuel absorbs.
law gcd_scale:
  for +m: Nat
  for +d: Nat
  for +kp: Nat
  {Nat.gcd(Nat.mul(m, 1n+kp), Nat.mul(d, 1n+kp)) == Nat.mul(Nat.gcd(m, d), 1n+kp) : Nat}

# gcd divides both arguments
# ==========================
#
# The loop's two steps replace the state (x, y) -- x in the fourth slot of
# Nat.gcd.go, y in the second -- by (x, y - x) when c = LT and by (x - y, y)
# when c = GT. In both cases the *old* argument is the sum of the new pair
# (y = x + (y - x), x = (x - y) + y), so one induction yields both divisibility
# facts and divides_add adds the quotients.
#
# gcd.divides_lt / gcd.divides_gt are the assembly for one step each: a common
# multiple of the new pair is a multiple of the old argument. They are laws
# rather than inline steps because the induction hypothesis's witness pair
# cannot be taken apart where it is produced -- `match` scrutinizes a parameter
# or a pattern-bound field, never a computed value ("give it its own def") --
# so the pair has to arrive as a helper's parameter, where the destructure is
# legal. The helper then rebuilds the old half of the pair from the fields it
# destructured, which is exactly why Nat.Div's fields have to be copyable.
#
# gcd.divides_lt states the equation as {s + x == y}: s is the new y slot, so
# the old larger argument y is s + x.
law gcd.divides_lt:
  for +g: Nat
  for +x: Nat
  for +s: Nat
  for +y: Nat
  for d: Nat.divides_both(g, x, s)
  for +e: {Nat.add(s, x) == y : Nat}
  Nat.divides_both(g, x, y)

# gcd.divides_gt is the mirror: here the pair covers (x, y) with x the *new*
# x slot of the loop -- the difference -- and the old larger argument is
# s + x.  The x slot is spelled 1 + xp rather than s for one reason: the loop's
# recursive call has that slot as 1 + xp' (gcd.go.divides states the state's x
# slot as a successor so its own fuel x + y reduces), so this helper's d
# parameter is only ever fed a pair whose first dividend is a successor. The
# caller rewrites the loop's stuck Nat.sub into that spelling with sub_pos.
law gcd.divides_gt:
  for +g: Nat
  for +xp: Nat
  for +y: Nat
  for +x: Nat
  for d: Nat.divides_both(g, 1n+xp, y)
  for +e: {Nat.add(1n+xp, y) == x : Nat}
  Nat.divides_both(g, x, y)

# gcd.go.divides: the loop invariant. The conclusion is stated about the *loop
# value* (`Nat.divides_both` of `Nat.gcd.go(..)` applied to the state), not
# about a dividend, because that is what the recursive step hands back: the
# induction hypothesis's pair flows straight into gcd.divides_lt/gt as the
# helper parameter d.
#
# e2 says the fuel s is the state's own measure (x + y) plus a slack t -- the
# same hypothesis gcd.go.fuel carries, and the reason both laws spell the x
# slot 1 + xp: the step's new x slot has to start with a constructor for the
# recursive call's fuel to be a constructor, and 1 + xp is the spelling that
# makes x + y reduce.
law gcd.go.divides:
  for +s: Nat
  for +y: Nat
  for c: Cmp
  for +xp: Nat
  for +t: Nat
  for +e1: {c == Nat.cmp(1n+xp, y) : Cmp}
  for +e2: {Nat.add(Nat.add(1n+xp, y), t) == s : Nat}
  Nat.divides_both(Nat.gcd.go(s, y, c, 1n+xp), 1n+xp, y)

# gcd_divides: gcd(a, b) divides both a and b -- the obligation the Rat step
# downstream consumes, since the quotient witness of g | (num.pos + num.neg)
# is what cancels in the normalization.
#
# a = 0 is split out exactly as in Nat.gcd itself: the loop only ever sees
# x >= 1, and the divisor is then b (with quotient 0) and the dividend 0 (with
# quotient 1). For a = 1 + ap the loop starts at x = a, y = b with fuel a + b,
# which is gcd.go.divides at t = 0 with e2 = a + b = (a + b) + 0.
law gcd_divides:
  for +a: Nat
  for +b: Nat
  Nat.divides_both(Nat.gcd(a, b), a, b)

# div_scale: the exact-division cancellation of the Rat normalization, packaged
# for a divisor that arrives as a *divisibility witness* rather than as the
# literal 1 + b that div_exact_mul wants.
#
# The witness is a binder (not something the caller destructures) for the usual
# reason: the caller's witness comes from gcd_divides, i.e. it is a field of a
# computed pair, and a computed pair cannot be taken apart where it is
# produced. Pair.fst is how the caller gets one half of that pair out.
law div_scale:
  for +mag: Nat
  for +g: Nat
  for +kp: Nat
  for w: Nat.divides(g, mag)
  for +p: {Nat.cmp(0n, g) == LT{} : Cmp}
  {Nat.div(Nat.mul(mag, 1n+kp), Nat.mul(g, 1n+kp)) == Nat.div(mag, g) : Nat}

# div_self_scale: div(q*(1+b), 1+b) = q -- the cancellation at the centre of
# the Rat value lemma, and div_exact with the dividend left in the product shape
# the goal already has, so nothing has to be rearranged to apply it.
law div_self_scale:
  for +q: Nat
  for +b: Nat
  {Nat.div(Nat.mul(q, 1n+b), 1n+b) == q : Nat}

# divides_pos_wit: a positive multiple of g forces g to be a successor, stated
# over the divisibility witness -- the positivity half of what div_scale needs
# of its divisor.
law divides_pos_wit:
  for +g: Nat
  for +a: Nat
  for w: Nat.divides(g, a)
  for +p: {Nat.cmp(0n, a) == LT{} : Cmp}
  {Nat.cmp(0n, g) == LT{} : Cmp}

# mul_pos_right: from a positive product, the right factor is positive. Same
# discrimination as divides_pos, on the other factor: mul(g, 0) = 0 leaves a
# successor equal to zero.
law mul_pos_right:
  for +g: Nat
  for +q: Nat
  for +ap: Nat
  for +e: {1n+ap == Nat.mul(g, q) : Nat}
  {Nat.cmp(0n, q) == LT{} : Cmp}

# div_pos_wit: a positive dividend divided by a divisor of it is positive --
# the denominator of Rat.mk's output is never zero, which is the one
# canonicality clause of mk that the normalization proves by itself (the
# numerator is a difference pair by construction, and coprimality of the output
# is the deep part this route deliberately avoids).
law div_pos_wit:
  for +g: Nat
  for +ap: Nat
  for w: Nat.divides(g, 1n+ap)
  {Nat.cmp(0n, Nat.div(1n+ap, g)) == LT{} : Cmp}
