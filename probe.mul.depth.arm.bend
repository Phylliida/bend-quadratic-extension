import Base
import ./src/tower.bend as T
import ./src/tower_helpers.bend as TH
import ./src/tower_proofs.bend as TP
import ./src/nat.bend as N
import ./src/nat_helpers.bend as NH
import ./src/nat_proofs.bend as NN

# The bookkeeping of mul.depth's Ext/Ext arm, with the recursive facts assumed.
#
# mul(1+g, Ext{rx,ix,dx}, Ext{ry,iy,dy}) unfolds to
#   Ext{add(M1, M2), add(...), dx}   M1 = mul(g, rx, ry), M2 = mul(g, mul(g, ix, iy), dx)
# so its depth is 1 + depth(add(M1, M2)), while depth(Ext{rx,ix,dx}) is 1 + depth(rx). What
# has to hold together is depth(add(M1, M2)) == depth(rx), through add.depth -- which needs
# depth(M1) == depth(M2) -- and the three recursive facts turn out to be one per product plus
# the inner one. This probe assumes those three and checks only the assembly.
def T.Tower.mul.depth.arm(+g: Nat, +rx: T.Tower, +ix: T.Tower, +dx: T.Tower,
    +ry: T.Tower, +iy: T.Tower, +dy: T.Tower,
    hi: {T.Tower.depth(ix) == T.Tower.depth(rx) : Nat},
    +hc1: {T.Tower.depth(T.Tower.mul(g, rx, ry)) == T.Tower.depth(rx) : Nat},
    hci: {T.Tower.depth(T.Tower.mul(g, ix, iy)) == T.Tower.depth(ix) : Nat},
    hc2: {T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))
          == T.Tower.depth(T.Tower.mul(g, ix, iy)) : Nat})
  -> {T.Tower.depth(T.Tower.mul(Nat.add(1n, g), T.Ext{rx, ix, dx}, T.Ext{ry, iy, dy}))
      == T.Tower.depth(T.Ext{rx, ix, dx}) : Nat}:
  +ei = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)), T.Tower.depth(ix),
          T.Tower.depth(rx), hci, hi)
  +em = Equal.trans(Nat, T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(rx),
          T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
          hc1, Equal.trans(Nat, T.Tower.depth(rx),
            T.Tower.depth(T.Tower.mul(g, ix, iy)),
            T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
            Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, ix, iy)), T.Tower.depth(rx), ei),
            Equal.sym(Nat, T.Tower.depth(T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx)),
              T.Tower.depth(T.Tower.mul(g, ix, iy)), hc2)))
  +ea = T.Tower.add.depth(T.Tower.mul(g, rx, ry),
          T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx), em)
  Equal.cong(Nat, Nat, u => Nat.add(1n, u),
    T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                              T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
    T.Tower.depth(rx),
    Equal.trans(Nat,
      T.Tower.depth(T.Tower.add(T.Tower.mul(g, rx, ry),
                                T.Tower.mul(g, T.Tower.mul(g, ix, iy), dx))),
      T.Tower.depth(T.Tower.mul(g, rx, ry)), T.Tower.depth(rx), ea, hc1))
