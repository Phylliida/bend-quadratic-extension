import Base
import ./src/nat.bend as N
import ./src/nat_proofs.bend as NP
import ./src/int.bend as I
import ./src/int_proofs.bend as IP
import ./src/rat.bend as R
import ./src/rat_proofs.bend as RP

# probe: Rat.inv, both branches, at concrete coordinates.

def inv.gt() -> R.Rat:
  R.Rat.inv(5n, 3n, 7n, GT{}, {==})

def inv.lt() -> R.Rat:
  R.Rat.inv(3n, 5n, 7n, LT{}, {==})

def inv.eq() -> R.Rat:
  R.Rat.inv(3n, 3n, 7n, EQ{}, {==})

def main() -> R.Rat & R.Rat & R.Rat:
  (inv.gt(), inv.lt(), inv.eq())
