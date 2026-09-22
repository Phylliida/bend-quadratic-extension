import Base
import ./src/int.bend as I
import ./src/int_proofs.bend as IP

# Empirical check: does distributivity hold for the CURRENT Int.mul, which
# does not canonicalize its zero (Int{xs, 0n} stays Int{xs, 0n})?
#
# x = Int{True,0} is a legal (non-canonical) zero.  y = 1, z = -1, so y+z = 0.

def main() -> I.Int & I.Int:
  (I.Int.mul(I.Int{True{}, 0n}, I.Int.add(I.Int{False{}, 1n}, I.Int{True{}, 1n})),
   I.Int.add(I.Int.mul(I.Int{True{}, 0n}, I.Int{False{}, 1n}),
             I.Int.mul(I.Int{True{}, 0n}, I.Int{True{}, 1n})))
