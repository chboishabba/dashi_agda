module DASHI.Physics.Closure.NSTriadKNABCLeafAssemblyRound58 where

------------------------------------------------------------------------
-- Lightweight A/B/C composition surface.
--
-- This package checks that the three new analytic boundaries are mutually
-- composable without importing the legacy closure consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalTransferSurfaceRound58 as A
import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as BHat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as BGram
import DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityLeafRound58 as C

record ABCLeafAssembly : Set₁ where
  field
    hhBadTransfer : A.PhysicalDyadicThreeMechanismTransfer

    comSupport : BHat.PhysicalOddPQCommonHatIdentification
    comGram : BGram.PhysicalNormalizedOddPQGramRealization comSupport
    comBounds : BGram.SameAdjacentNormalizedFibreMassBounds comGram

    integralCritical correctionHeadroom dataRemainder : Nat → ℚ
    ownerFluxBlock : C.PhysicalOwnerFluxBlockIdentification
    uniformCapacity :
      C.UniformFixedShiftProductCapacity
        integralCritical correctionHeadroom dataRemainder

open ABCLeafAssembly public

abcLeafBoundaryTyped : Bool
abcLeafBoundaryTyped = true

abcLeafBoundaryTypedIsTrue : abcLeafBoundaryTyped ≡ true
abcLeafBoundaryTypedIsTrue = refl

-- The assembly is a boundary only; no analytic witness is asserted here.
abcLeafAssemblyConstructed : Bool
abcLeafAssemblyConstructed = false
