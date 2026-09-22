import Base
import ./int.bend as I

# QExt: quadratic extensions Q(sqrt d)
# ====================================
#
# Elements are re + im*sqrt(d) with re im : Int. The radicand d is a
# Nat parameter of the operations, not of the type, so one QExt type
# serves every extension level (and, later, towers).
#
# Laws are stated here and left open; qext_proofs.bend fills them via
# `def Q.<name>(...)`.

type QExt is Data:
  QExt{re: I.Int, im: I.Int}

# a natural radicand as an integer
def QExt.nat(d: Nat) -> I.Int:
  I.Int{False{}, d}

def QExt.add(x: QExt, y: QExt) -> QExt:
  QExt{+xr, +xi} = x
  QExt{+yr, +yi} = y
  QExt{I.Int.add(xr, yr), I.Int.add(xi, yi)}

def QExt.mul(+d: Nat, x: QExt, y: QExt) -> QExt:
  QExt{+xr, +xi} = x
  QExt{+yr, +yi} = y
  di = QExt.nat(d)
  QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(di, xi), yi)),
       I.Int.add(I.Int.mul(xr, yi), I.Int.mul(xi, yr))}

# QExt.add_comm: x + y = y + x
law QExt.add_comm:
  for +x: QExt
  for +y: QExt
  {QExt.add(x, y) == QExt.add(y, x) : QExt}

# QExt.mul_comm: x * y = y * x
law QExt.mul_comm:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  {QExt.mul(d, x, y) == QExt.mul(d, y, x) : QExt}
