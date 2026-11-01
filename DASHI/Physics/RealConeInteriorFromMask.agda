module DASHI.Physics.RealConeInteriorFromMask where

open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import UFTC_Lattice as UFTC
open import DASHI.Physics.MaskedConeStructure as MCS
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Algebra.Trit using (Trit)

-- Cone interior/boundary from a signature mask.
coneInteriorFromMask : ∀ {m : Nat} → Vec IMQ.Sign m → UFTC.ConeInterior {X = Vec Trit m}
coneInteriorFromMask {m} σ =
  record
    { InInterior = MCS.Timelike σ
    ; Boundary = MCS.Null σ
    }
