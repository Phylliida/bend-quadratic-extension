import Base
import ./qext.bend as Q
import ./int.bend as I
import ./int_proofs.bend as IP

# QExt proofs
# ==========
#
# Fills every law of qext.bend. Int evidence is called through I (the
# int.bend alias); the int_proofs.bend import fills those laws.

def Q.QExt.add_comm(x, y):
  match x y:
    case Q.QExt{xr, xi} Q.QExt{yr, yi}:
      %I.Int.add_comm(xr, yr) : {Q.QExt{I.Int.add(xr, yr), I.Int.add(xi, yi)} == Q.QExt{_, I.Int.add(yi, xi)} : Q.QExt}
      %I.Int.add_comm(xi, yi) : {Q.QExt{I.Int.add(xr, yr), I.Int.add(xi, yi)} == Q.QExt{I.Int.add(xr, yr), _} : Q.QExt}
      {==}

def Q.QExt.mul_comm(d, x, y):
  match x y:
    case Q.QExt{xr, xi} Q.QExt{yr, yi}:
      %I.Int.mul_comm(xr, yr) : {Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(xr, yi), I.Int.mul(xi, yr))} == Q.QExt{I.Int.add(_, I.Int.mul(I.Int.mul(I.Int{False{}, d}, yi), xi)), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : Q.QExt}
      %I.Int.mul_swap(I.Int{False{}, d}, xi, yi) : {Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(xr, yi), I.Int.mul(xi, yr))} == Q.QExt{I.Int.add(I.Int.mul(xr, yr), _), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : Q.QExt}
      %I.Int.mul_comm(yr, xi) : {Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(xr, yi), _)} == Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : Q.QExt}
      %I.Int.mul_comm(yi, xr) : {Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(_, I.Int.mul(yr, xi))} == Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(yr, xi), I.Int.mul(yi, xr))} : Q.QExt}
      %I.Int.add_comm(I.Int.mul(yi, xr), I.Int.mul(yr, xi)) : {Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), I.Int.add(I.Int.mul(yi, xr), I.Int.mul(yr, xi))} == Q.QExt{I.Int.add(I.Int.mul(xr, yr), I.Int.mul(I.Int.mul(I.Int{False{}, d}, xi), yi)), _} : Q.QExt}
      {==}
