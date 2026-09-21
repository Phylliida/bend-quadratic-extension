import Base
import ./nat.bend as N
import ./int.bend as I

# QExt: quadratic extensions Q(sqrt d)
# ====================================
#
# Elements are re + im*sqrt(d) with re im : Int. The radicand d is a
# Nat parameter of the operations, not of the type, so one QExt type
# serves every extension level (and, later, towers).

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

def QExt.add_comm(x, y):
  match x y:
    case QExt{xr, xi} QExt{yr, yi}:
      %I.Int.add_comm(xr, yr) : {QExt{I.Int.add(xr, yr), I.Int.add(xi, yi)} == QExt{_, I.Int.add(yi, xi)} : QExt}
      %I.Int.add_comm(xi, yi) : {QExt{I.Int.add(xr, yr), I.Int.add(xi, yi)} == QExt{I.Int.add(xr, yr), _} : QExt}
      {==}

# QExt.mul_comm: x * y = y * x
law QExt.mul_comm:
  for +d: Nat
  for +x: QExt
  for +y: QExt
  {QExt.mul(d, x, y) == QExt.mul(d, y, x) : QExt}

def QExt.mul_comm(d, x, y):
  match x y:
    case QExt{xr, xi} QExt{yr, yi}:
      %I.Int.mul_comm(xr, yr) : {QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(xr, yi), I.Int.mul(xi, yr))} == QExt{I.Int.add(_, I.Int.mul(I.Int.mul(I.Int{False{}, d}, yi), xi)), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : QExt}
      %I.Int.mul_swap(I.Int{False{}, d}, xi, yi) : {QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(xr, yi), I.Int.mul(xi, yr))} == QExt{I.Int.add(I.Int.mul(xr, yr), _), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : QExt}
      %I.Int.mul_comm(yr, xi) : {QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(xr, yi), _)} == QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : QExt}
      %I.Int.mul_comm(yi, xr) : {QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(_, I.Int.mul(yr, xi))} == QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : QExt}
      %I.Int.add_comm(I.Int.mul(yi, xr), I.Int.mul(yr, xi)) : {QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(yi, xr), I.Int.mul(yr, xi))} == QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), _} : QExt}
      {==}
