import Base
import ./nat.bend as N

# Helper laws for Nat
# ===================
#
# The laws a reader of `nat.bend` does not need: variants of the readable
# laws, and the structural plumbing the layers above lean on. Same statements,
# moved here, with their fills still in nat_proofs.bend.
#
# `nat.bend` does not import this file -- a helper law is stated over that
# file's types and operations, so the import only goes one way.

# add_exchange: a + (b + c) = b + (a + c)
law add_exchange:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

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

# cmp_gt_succ: a > b -> 1+a > b
law cmp_gt_succ:
  for +a: Nat
  for +b: Nat
  for e: {Nat.cmp(a, b) == GT{} : Cmp}
  {Nat.cmp(1n+a, b) == GT{} : Cmp}

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

# flip_eq_lt: flip(c) = LT -> c = GT
law flip_eq_lt:
  for +c: Cmp
  for e: {N.Cmp.flip(c) == LT{} : Cmp}
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
  {Nat.cmp(Nat.sub(c, a), b) == N.Cmp.flip(Nat.cmp(a, Nat.sub(c, b))) : Cmp}

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
  {N.Cmp.flip(N.Cmp.flip(c)) == c : Cmp}

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
  {N.Cmp.flip(d) == Nat.cmp(a, Nat.sub(c, b)) : Cmp}

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

# sub_diag_rev: sub(np,nn) == sub(sub(np,nn), sub(nn,np)) -- sub_diag read in
# the other orientation, so that a rewrite *under* a division's dividend can use
# it directly. The twin-law idiom of add_succ/mul_succ/add_assoc_rev/
# cmp_gt_of_lt: `Equal.cong` at a dividend takes its evidence in the direction
# "collapsed -> diagonal" (the goal's left side is what the operation was
# applied to), and `Equal.sym` cannot be composed with it at this shape (see
# PROVING.md). Stated rather than derived at each use.
law sub_diag_rev:
  for c: Cmp
  for +np: Nat
  for +nn: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  {Nat.sub(np, nn) == Nat.sub(Nat.sub(np, nn), Nat.sub(nn, np)) : Nat}

# sub_cross: the cross sum of a truncation pair -- (a - b) + b = (b - a) + a.
# Both sides are the larger argument, which is why it needs no hypothesis on a
# and b: the comparison decides which truncation is the difference and which is
# zero, and the two cases are cmp_gt_sub_add / cmp_lt_sub_add with the other
# truncation collapsed by sub_of_lt. It is what relates a *pair* of naturals to
# its own truncation pair -- the shape the canonical coordinates of a sum have --
# and it is the only place the sign information of such a sum is consumed, which
# is why the Rat additive laws can be pure ring shuffling on top of it.
#
# The comparison is a parameter with its evidence (the fill cases on it, and a
# computed Nat.cmp is not a legal scrutinee); callers pass Nat.cmp(a, b) and {==}.
law sub_cross:
  for c: Cmp
  for +a: Nat
  for +b: Nat
  for +e: {c == Nat.cmp(a, b) : Cmp}
  {Nat.add(Nat.sub(a, b), b) == Nat.add(Nat.sub(b, a), a) : Nat}

# cross_add: two equations with a common padding combine criss-cross. If
# A + t = A' + t' and B + t = B' + t', then A + B' = A' + B -- in integers both
# hypotheses say "A - A' = t' - t" and "B - B' = t' - t", so A - B = A' - B'.
# Stated over the two hypotheses rather than over subtractions because Nat has no
# negative values; the fill pads both sides by t + t' and cancels (add_cancel).
#
# This is the step that consumes the truncation cross sums sub_cross produces:
# the pair (A, t) is one side's scaled coordinate pair, and the common padding is
# what makes the two equations comparable at all.
law cross_add:
  for +A: Nat
  for +A2: Nat
  for +B: Nat
  for +B2: Nat
  for +t: Nat
  for +t2: Nat
  for e1: {Nat.add(A, t) == Nat.add(A2, t2) : Nat}
  for e2: {Nat.add(B, t) == Nat.add(B2, t2) : Nat}
  {Nat.add(A, B2) == Nat.add(A2, B) : Nat}

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
  {N.Nat.gcd.go(s, Nat.mul(y, 1n+kp), Nat.cmp(Nat.mul(x, 1n+kp), Nat.mul(y, 1n+kp)), Nat.mul(x, 1n+kp)) == Nat.mul(1n+kp, N.Nat.gcd.go(s, y, c, x)) : Nat}

# add_mul_slack: (x + y) + (x*k + y*k) = x*(1+k) + y*(1+k).
#
# This is the "the scaled state's fuel is the unscaled fuel plus a slack"
# identity: N.Nat.gcd(m, d) runs the loop with fuel m + d, N.Nat.gcd(m*k, d*k)
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
# and N.Nat.gcd must carry the same spelling, and that the GT step has to undo
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
  {N.Nat.gcd.go(Nat.add(s1, u), y, c, 1n+xp) == N.Nat.gcd.go(s1, y, c, 1n+xp) : Nat}

# gcd divides both arguments
# ==========================
#
# The loop's two steps replace the state (x, y) -- x in the fourth slot of
# N.Nat.gcd.go, y in the second -- by (x, y - x) when c = LT and by (x - y, y)
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
# destructured, which is exactly why N.Nat.Div's fields have to be copyable.
#
# gcd.divides_lt states the equation as {s + x == y}: s is the new y slot, so
# the old larger argument y is s + x.
law gcd.divides_lt:
  for +g: Nat
  for +x: Nat
  for +s: Nat
  for +y: Nat
  for d: N.Nat.divides_both(g, x, s)
  for +e: {Nat.add(s, x) == y : Nat}
  N.Nat.divides_both(g, x, y)

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
  for d: N.Nat.divides_both(g, 1n+xp, y)
  for +e: {Nat.add(1n+xp, y) == x : Nat}
  N.Nat.divides_both(g, x, y)

# gcd.go.divides: the loop invariant. The conclusion is stated about the *loop
# value* (`N.Nat.divides_both` of `N.Nat.gcd.go(..)` applied to the state), not
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
  N.Nat.divides_both(N.Nat.gcd.go(s, y, c, 1n+xp), 1n+xp, y)

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
  for w: N.Nat.divides(g, mag)
  for +p: {Nat.cmp(0n, g) == LT{} : Cmp}
  {Nat.div(Nat.mul(mag, 1n+kp), Nat.mul(g, 1n+kp)) == Nat.div(mag, g) : Nat}

# div_cross: the value of an exact division -- the cross product
#
#     div(p, g) * d == p * div(d, g)
#
# for a dividend and a cofactor that are both known to be multiples of g
# (p = g*q, d = g*r, which is what the two witness hypotheses say, one quotient
# per side). This is the Nat content of the Rat value lemma
# (num(mk(n,d))*d == n*den(mk(n,d))): each coordinate of that cross product is
# an instance, at g := the gcd mk cancels.
#
# The divisor is a *variable* with a positivity hypothesis rather than the
# literal 1 + b every other law in this block is stated over. That is the one
# deliberate difference: the Rat caller's divisor is a computed gcd, and
# re-spelling it as a successor at the call site would be an Equal.cong over
# the whole goal for every use, in every branch of a case split. The fill pays
# that rewrite once instead (pos_witness), after which div_exact applies to
# both divisions.
law div_cross:
  for +p: Nat
  for +g: Nat
  for +q: Nat
  for +d: Nat
  for +r: Nat
  for +gp: {Nat.cmp(0n, g) == LT{} : Cmp}
  for +e1: {p == Nat.mul(g, q) : Nat}
  for +e2: {d == Nat.mul(g, r) : Nat}
  {Nat.mul(Nat.div(p, g), d) == Nat.mul(p, Nat.div(d, g)) : Nat}

# divides_pos_wit: a positive multiple of g forces g to be a successor, stated
# over the divisibility witness -- the positivity half of what div_scale needs
# of its divisor.
law divides_pos_wit:
  for +g: Nat
  for +a: Nat
  for w: N.Nat.divides(g, a)
  for +p: {Nat.cmp(0n, a) == LT{} : Cmp}
  {Nat.cmp(0n, g) == LT{} : Cmp}

# mul_right_cancel: a positive scale can be cancelled on the right of a
# product. This is injectivity of "multiply by 1+kp" -- what a proof needs
# whenever it has scaled both sides of an equation up to a common denominator
# and then wants the unscaled equation back (the Rat composing laws scale a
# value equation by the other side's denominator, and the factor has to come
# off again before mk.eqv can see the cross product).
#
# By induction on a: a = 0 forces b = 0 (the other side would be a successor
# equal to zero), and a = 1+ap makes both sides successors -- succ_inj peels the
# outer one, add_cancel the kp that mul leaves inside, and the induction
# hypothesis does the rest.
law mul_right_cancel:
  for +a: Nat
  for +b: Nat
  for +kp: Nat
  for e: {Nat.mul(a, 1n+kp) == Nat.mul(b, 1n+kp) : Nat}
  {a == b : Nat}

# div_pos_wit: a positive dividend divided by a divisor of it is positive --
# the denominator of Rat.mk's output is never zero, which is the one
# canonicality clause of mk that the normalization proves by itself (the
# numerator is a difference pair by construction, and coprimality of the output
# is the deep part this route deliberately avoids).
law div_pos_wit:
  for +g: Nat
  for +ap: Nat
  for w: N.Nat.divides(g, 1n+ap)
  {Nat.cmp(0n, Nat.div(1n+ap, g)) == LT{} : Cmp}
