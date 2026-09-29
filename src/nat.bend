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

# cmp_gt_refl_succ: 1+a > a
law cmp_gt_refl_succ:
  for +a: Nat
  {Nat.cmp(1n+a, a) == GT{} : Cmp}

# cmp_lt_succ_self: a < 1 + a
law cmp_lt_succ_self:
  for +a: Nat
  {Nat.cmp(a, 1n+a) == LT{} : Cmp}

# cmp_eq_sub_add: cmp(a,b) = EQ -> (a - b) + b = a
law cmp_eq_sub_add:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {Nat.add(Nat.sub(a, b), b) == a : Nat}

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

# div_self.pos: a/a = 1 for a positive a that is *not* written as a successor.
# div_self's spelling is what div_exact consumes, and a successor is what keeps
# the divisor's match reducing; a divisor that arrives as an operation's output
# -- Nat.sub(np,nn) out of a GT branch, a div/gcd term out of a normalization --
# has neither, and carries its positivity as a witness instead, the same
# hypothesis Rat.add_neg takes. The fill is the case split div_self cannot do:
# a = 0 contradicts the witness (Nat.cmp(0,0) is EQ, and EQ is not LT), and
# a = 1 + ap is div_self itself.
law div_self.pos:
  for +a: Nat
  for +p: {Nat.cmp(0n, a) == LT{} : Cmp}
  {Nat.div(a, a) == 1n : Nat}

# Difference-pair helpers
# =======================
#
# The Rat canonical form is the difference pair (sub(np,nn), sub(nn,np)), which
# always has one side zero. Moving between "the difference pair of np, nn" and
# "the raw coordinates np, nn" -- which is what Rat.mk does when it destructures
# a numerator it produced itself -- needs the three facts below.

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

# gcd_self: gcd(a, a) = a, at a general a -- and the generality is the point.
#
# For a *variable* a the loop cannot start at all: Nat.gcd's fourth slot holds
# a and Nat.cmp(a, a) is stuck, so Nat.gcd(a, a) is a stuck term and no lemma
# stated at a fixed, successor-shaped argument can be used in its place -- the
# type gcd(1+d, 1+d) = 1+d is convertible with gcd(a, a) = a only at a = 1+d,
# never at a variable. So the case split has to happen inside the lemma, which
# is what this states: the successor case Nat.gcd_self opens is the one where
# the loop reduces, and there gcd_scale at k = 0 with m = d = 1 collapses the
# two equal arguments. (a = 0 is the def's own first branch.)
law gcd_self:
  for +a: Nat
  {Nat.gcd(a, a) == a : Nat}

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

# div_self_scale: div(q*(1+b), 1+b) = q -- the cancellation at the centre of
# the Rat value lemma, and div_exact with the dividend left in the product shape
# the goal already has, so nothing has to be rearranged to apply it.
law div_self_scale:
  for +q: Nat
  for +b: Nat
  {Nat.div(Nat.mul(q, 1n+b), 1n+b) == q : Nat}

# mul_pos_right: from a positive product, the right factor is positive. Same
# discrimination as divides_pos, on the other factor: mul(g, 0) = 0 leaves a
# successor equal to zero.
law mul_pos_right:
  for +g: Nat
  for +q: Nat
  for +ap: Nat
  for +e: {1n+ap == Nat.mul(g, q) : Nat}
  {Nat.cmp(0n, q) == LT{} : Cmp}

# mul_pos: a product of two positive factors is positive. Stated over the two
# positivity hypotheses (rather than over successor spellings) because that is
# what a caller holds: a denominator out of Rat.mk.den.pos is positive by its
# comparison, and a product of two of them has to be positive to be rewritten
# into the 1n+dp shape Rat.mk.eqv and its relatives are stated over. Both
# factors go to successor form with pos_witness, and then the comparison
# reduces: mul(1+ap, 1+bp) = add(1+bp, mul(ap, 1+bp)) = 1 + ..., a successor,
# and cmp(0n, 1n+k) is LT by computation.
law mul_pos:
  for +a: Nat
  for +b: Nat
  for +pa: {Nat.cmp(0n, a) == LT{} : Cmp}
  for +pb: {Nat.cmp(0n, b) == LT{} : Cmp}
  {Nat.cmp(0n, Nat.mul(a, b)) == LT{} : Cmp}
