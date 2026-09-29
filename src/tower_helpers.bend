import Base
import ./rat.bend as R
import ./rat_helpers.bend as RH
import ./tower.bend as T

# Helper laws for Tower
# =====================
#
# The laws a reader of `tower.bend` does not need: variants of the readable
# laws, and the structural plumbing the layers above lean on. Same statements,
# moved here, with their fills still in tower_proofs.bend.
#
# `tower.bend` does not import this file -- a helper law is stated over that
# file's types and operations, so the import only goes one way.

law Tower.mul.fuel.zero:
  for +x: T.Tower
  for +y: T.Tower
  {T.Tower.mul(0n, x, y) == T.Fuel{} : T.Tower}

law Tower.mul.fuel.base:
  for +g: Nat
  for a: R.Rat
  for b: R.Rat
  T.Tower.clean(T.Tower.mul(1n+g, T.Base{a}, T.Base{b}))
