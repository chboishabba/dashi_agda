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
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 as ASource
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceAdapterRound58 as BSource
import DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityLeafRound58 as C

record ABCLeafAssembly : Set₁ where
  field
    hhBadTransfer : A.PhysicalDyadicThreeMechanismTransfer
    hhBadPhysicalSource : ASource.PhysicalLocalizedDuhamelSource
    hhBadTransferUsesPhysicalSource :
      A.source hhBadTransfer
      ≡ ASource.asLocalizedSource hhBadPhysicalSource

    -- One canonical B source owns the literal output-fibre support, normalized
    -- Gram mass, off-support annihilation, and all three active bounds.
    comSource : BSource.PhysicalNormalizedOddPQSource

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
