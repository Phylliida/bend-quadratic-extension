import Base
import ./int.bend as I
import ./nat.bend as N

# Rat core: the definitions this layer needs, with the two laws `Rat.add_comm`
# and `Rat.mul_comm` restated here so that their fills can live in this
# namespace (\qrat_proofs.bend) instead of reaching into rat.bend's.
#
# Why a second file at all. `Rat.add_comm`/`Rat.mul_comm` are declared in
# rat.bend and *filled* in rat_proofs.bend, and rat_proofs.bend cannot be
# imported: the checker reads its proof-only helper defs out of another
# namespace and dies on the first of them ("expected : a defined name / observed
# : R.Rat.add.piece"). That is PROVING.md's measurement, re-measured here for
# this layer at several import orders. A fill may be attached from a *different*
# file (that is what this file's own laws are for), but the fills that
# rat_proofs.bend attaches cannot be reached from here, so the two Rat facts
# this layer consumes are declared and filled in this closure.
#
# The definitions are rat.bend's own, unchanged: Rat{num, den} with num/den
# standing for a rational, Rat.mk canonicalizing by arithmetic (no match, so no
# case analysis leaks into the laws), and add/neg/sub/mul written exactly as
# rat.bend writes them so that the fills below are the same proofs.

type Rat is Data:
  Rat{num: I.Int, den: Nat}

def Rat.numof(r: Rat) -> I.Int:
  Rat{+n, +d} = r
  n

def Rat.denof(r: Rat) -> Nat:
  Rat{+n, +d} = r
  d

def Rat.zero() -> Rat:
  Rat{I.Int.zero(), 1n}

def Rat.one() -> Rat:
  Rat{I.Int.one(), 1n}

def Rat.num(+np: Nat, +nn: Nat) -> I.Int:
  I.Int{Nat.sub(np, nn), Nat.sub(nn, np)}

def Rat.mag(+np: Nat, +nn: Nat) -> Nat:
  Nat.add(Nat.sub(np, nn), Nat.sub(nn, np))

def Rat.g(+np: Nat, +nn: Nat, +d: Nat) -> Nat:
  N.Nat.gcd(Rat.mag(np, nn), d)

def Rat.mk.go(+np: Nat, +nn: Nat, +d: Nat) -> Rat:
  Rat{I.Int{Nat.div(Nat.sub(np, nn), Rat.g(np, nn, d)),
            Nat.div(Nat.sub(nn, np), Rat.g(np, nn, d))},
      Nat.div(d, Rat.g(np, nn, d))}

def Rat.mk(n: I.Int, d: Nat) -> Rat:
  I.Int{+np, +nn} = n
  Rat.mk.go(np, nn, d)

def Rat.add(x: Rat, y: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat{+yn, +yd} = y
  Rat.mk(I.Int.add(I.Int.mul(xn, I.Int{yd, 0n}), I.Int.mul(yn, I.Int{xd, 0n})),
    Nat.mul(xd, yd))

def Rat.neg(x: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat.mk(I.Int.neg(xn), xd)

def Rat.sub(x: Rat, y: Rat) -> Rat:
  Rat.add(x, Rat.neg(y))

def Rat.mul(x: Rat, y: Rat) -> Rat:
  Rat{+xn, +xd} = x
  Rat{+yn, +yd} = y
  Rat.mk(I.Int.mul(xn, yn), Nat.mul(xd, yd))

# Rat.mk.canon: mk is the identity on a reduced fraction -- the gcd it cancels
# is 1, so every division is by 1 and the difference pair comes back unchanged.
# This is the shape every "normalization disappears" fact starts from, and the
# reason mk.go is stated over raw coordinates: the divisor it computes is
# literally Rat.g(np, nn, 1+dp), so the coprime hypothesis is about the same
# expression and no rewrite has to reach under a division.
law Rat.mk.canon:
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.mk.go(np, nn, 1n+dp) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# Rat.add_comm: x + y = y + x
law Rat.add_comm:
  for +x: Rat
  for +y: Rat
  {Rat.add(x, y) == Rat.add(y, x) : Rat}

# Rat.mul_comm: x * y = y * x
law Rat.mul_comm:
  for +x: Rat
  for +y: Rat
  {Rat.mul(x, y) == Rat.mul(y, x) : Rat}

# Rat.mk.fixed: a reduced fraction in the difference-pair presentation is a
# fixed point of mk -- the canonicality hypothesis the conditional laws take,
# discharged. Transcription-identical to rat.bend's law of the same name (the
# same statement, the same comment); it is restated here because its fill lives
# in this closure, exactly as Rat.add_comm's and Rat.mul_comm's do.
law Rat.mk.fixed:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.mk(Rat.num(np, nn), 1n+dp) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

# Rat.neg_neg: -(-x) = x for a canonical x. Transcription-identical to
# rat.bend's law of the same name: the coprime hypothesis is required for truth
# (== on Rat is structural, so negation of a non-canonical term comes back
# mk-headed), and it is Rat.mk.fixed's own hypothesis.
law Rat.neg_neg:
  for +c: Cmp
  for +np: Nat
  for +nn: Nat
  for +dp: Nat
  for +e: {c == Nat.cmp(np, nn) : Cmp}
  for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
  {Rat.neg(Rat.neg(Rat{Rat.num(np, nn), 1n+dp})) == Rat{Rat.num(np, nn), 1n+dp} : Rat}
