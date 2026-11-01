module DASHI.Physics.OrbitProfileComputedRootSystemB4 where

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

open import DASHI.Physics.OrbitProfileComputed as OPC
open import DASHI.Physics.RootSystemB4Carrier as B4
open import DASHI.Physics.RootSystemB4WeylAction as W

b4-shell1-computed : List Nat
b4-shell1-computed =
  OPC.sortDesc
    (OPC.orbitSizes
      B4.decEqB4Point
      W.allWeylB4
      W.actWeyl
      B4.shell1Points)

b4-shell2-computed : List Nat
b4-shell2-computed =
  OPC.sortDesc
    (OPC.orbitSizes
      B4.decEqB4Point
      W.allWeylB4
      W.actWeyl
      B4.shell2Points)
