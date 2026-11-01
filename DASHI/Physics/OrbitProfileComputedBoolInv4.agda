module DASHI.Physics.OrbitProfileComputedBoolInv4 where

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import Data.Vec using (Vec)

open import DASHI.Physics.OrbitProfileComputed as OPC
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM

mask31 : Vec IMQ.Sign 4
mask31 = SFM.oneMinusRestPlus {m = 3}

shell1_p3_q1_boolinv_computed : List Nat
shell1_p3_q1_boolinv_computed =
  OPC.sortDesc
    (OPC.orbitSizes
      OPC.decEqVec
      OPC.bools
      OPC.actBool
      (OPC.shellList 1 mask31))

shell2_p3_q1_boolinv_computed : List Nat
shell2_p3_q1_boolinv_computed =
  OPC.sortDesc
    (OPC.orbitSizes
      OPC.decEqVec
      OPC.bools
      OPC.actBool
      (OPC.shellList 2 mask31))
