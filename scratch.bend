import Base
import ./src/int.bend as I

# smoke: (3 + -5) + 7 == 3 + (-5 + 7)  == 5 ; and the proof term exists
def three() -> I.Int: I.Int{False{}, 3n}
def nfive() -> I.Int: I.Int{True{}, 5n}
def seven() -> I.Int: I.Int{False{}, 7n}

def main() -> I.Int:
  lhs = I.Int.add(I.Int.add(three(), nfive()), seven())
  rhs = I.Int.add(three(), I.Int.add(nfive(), seven()))
  p = I.Int.add_assoc(three(), nfive(), seven())
  lhs
