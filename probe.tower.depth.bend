import Base
import ./src/tower.bend as T
import ./src/tower_helpers.bend as TH
import ./src/tower_proofs.bend as TP
import ./src/rat.bend as R

# The depth-2 radicand-threading gate.
#
# Level 1 lives in Q(sqrt 5): a level-1 tower is Ext{p, q, Base{5}} standing for
# p + q*sqrt(5). Level 2 extends it by sqrt(D) with D the level-1 element 2, so a
# level-2 element is Ext{R, I, D} standing for R + I*sqrt(2).
#
# d1 is the control: sqrt(5) * sqrt(5) = 5 at level 1, where the radicand the
# multiplication needs is a Base. d2 is the test: (sqrt(5) + sqrt(2))^2, whose
# value is 5 + 2 + 2*sqrt(5)*sqrt(2) = 7 + (2*sqrt(5))*sqrt(2), written in the
# tower as Ext{Base{7}, Ext{Base{0}, Base{2}, Base{5}}, D}.
#
# Before the radicand fix d1 was right and d2 came back with Bad where the
# coordinates should be. Both are equalities the checker decides definitionally,
# so this file is the regression gate for it.

def five() -> T.Tower:
  T.Base{R.Rat.of(5n, 0n, 0n)}

def two() -> T.Tower:
  T.Base{R.Rat.of(2n, 0n, 0n)}

def seven() -> T.Tower:
  T.Base{R.Rat.of(7n, 0n, 0n)}

def one() -> T.Tower:
  T.Base{R.Rat.of(1n, 0n, 0n)}

def zero() -> T.Tower:
  T.Base{R.Rat.of(0n, 0n, 0n)}

def sq5() -> T.Tower:
  T.Ext{zero(), one(), five()}

def one1() -> T.Tower:
  T.Ext{one(), zero(), five()}

def bigD() -> T.Tower:
  T.Ext{two(), zero(), five()}

def x2() -> T.Tower:
  T.Ext{sq5(), one1(), bigD()}

def ctrl1() -> T.Tower:
  T.Tower.mul(2n, sq5(), sq5())

def test2() -> T.Tower:
  T.Tower.mul(3n, x2(), x2())

def want1() -> T.Tower:
  T.Ext{five(), zero(), five()}

# The coefficients of a level-2 element live at the radicand's level, so 7 here is
# the level-1 element 7 + 0*sqrt(5), not the level-0 tower Base{7}. Writing the
# level-0 form is what round thirty-four's first expectation did, and the checker
# rejected it: same number, different depth, and depth is the discipline.
def want2() -> T.Tower:
  T.Ext{T.Ext{seven(), zero(), five()}, T.Ext{zero(), two(), five()}, bigD()}

def mul.depth1.ok() -> {ctrl1() == want1() : T.Tower}:
  {==}

def mul.depth2.ok() -> {test2() == want2() : T.Tower}:
  {==}
