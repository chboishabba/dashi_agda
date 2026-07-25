module DASHI.Physics.Closure.NSPeriodicFarLowSupportGeometry where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteNearTriadSums as Near
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Executable far-low support geometry for both oriented placements.
------------------------------------------------------------------------

natLeq : Nat → Nat → Bool
natLeq zero n = true
natLeq (suc m) zero = false
natLeq (suc m) (suc n) = natLeq m n

_and_ : Bool → Bool → Bool
true and b = b
false and b = false

within : Nat → Nat → Nat → Bool
within radius a b = natLeq a (b + radius) and natLeq b (a + radius)

record FarLowGeometry : Set₁ where
  field
    shellLevel : Z3.FourierMode → Nat
    outputShell : Nat
    separation : Nat
    overlap : Nat

open FarLowGeometry public

farLowLeftSupported : FarLowGeometry → Near.ConcreteNearTriad → Bool
farLowLeftSupported G t =
  natLeq (shellLevel G (Near.p t) + separation G) (outputShell G)
  and within (overlap G) (shellLevel G (Near.q t)) (outputShell G)

farLowRightSupported : FarLowGeometry → Near.ConcreteNearTriad → Bool
farLowRightSupported G t =
  natLeq (shellLevel G (Near.q t) + separation G) (outputShell G)
  and within (overlap G) (shellLevel G (Near.p t)) (outputShell G)

data FarLowPlacement : Set where
  leftLow rightLow unsupported : FarLowPlacement

classifyFarLow : FarLowGeometry → Near.ConcreteNearTriad → FarLowPlacement
classifyFarLow G t with farLowLeftSupported G t
... | true = leftLow
... | false with farLowRightSupported G t
...   | true = rightLow
...   | false = unsupported

farLowSupportGeometryLevel : ProofLevel
farLowSupportGeometryLevel = machineChecked
