import Base
import ./src/int.bend as I
import ./src/int_proofs.bend as IP

# smoke: (3 + -5) + 7 and 3 + (-5 + 7), plus the Int.add_assoc proof term.
#
# An Int is a (pos, neg) difference pair, so both sides print as the same
# non-canonical representative of 5: 10 - 5. Collapsing that to a canonical
# representative is Int.canon's job (see int.bend).
def three() -> I.Int: I.Int{3n, 0n}
def nfive() -> I.Int: I.Int{0n, 5n}
def seven() -> I.Int: I.Int{7n, 0n}

def main() -> I.Int & I.Int:
  p = I.Int.add_assoc(three(), nfive(), seven())
  (I.Int.add(I.Int.add(three(), nfive()), seven()),
   I.Int.add(three(), I.Int.add(nfive(), seven())))
