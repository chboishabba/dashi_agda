module DASHI.Physics.Closure.NSTriadKNABCLeafAssemblyRound58 where

------------------------------------------------------------------------
-- Lightweight A/B/C composition surface.
--
-- Round60 makes A fail closed at one object: a physical source plus estimates
-- indexed by that source.  The transfer is a derived view, not an independently
-- supplied witness with a later same-object equality.
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
    hhBadPhysicalSource : ASource.PhysicalLocalizedDuhamelSource
    hhBadPhysicalEstimates :
      ASource.PhysicalLocalizedDuhamelEstimates hhBadPhysicalSource

    -- One canonical B source owns the literal output-fibre support, normalized
    -- Gram mass, off-support annihilation, and all three active bounds.
    comSource : BSource.PhysicalNormalizedOddPQSource

    integralCritical correctionHeadroom dataRemainder : Nat → ℚ
    ownerFluxBlock : C.PhysicalOwnerFluxBlockIdentification
    uniformCapacity :
      C.UniformFixedShiftProductCapacity
        integralCritical correctionHeadroom dataRemainder

open ABCLeafAssembly public

hhBadTransfer : ABCLeafAssembly → A.PhysicalDyadicThreeMechanismTransfer
hhBadTransfer assembly =
  ASource.physicalTransferFromSource
    (hhBadPhysicalSource assembly)
    (hhBadPhysicalEstimates assembly)

abcLeafBoundaryTyped : Bool
abcLeafBoundaryTyped = true

abcLeafBoundaryTypedIsTrue : abcLeafBoundaryTyped ≡ true
abcLeafBoundaryTypedIsTrue = refl

-- The assembly is a boundary only; no analytic witness is asserted here.
abcLeafAssemblyConstructed : Bool
abcLeafAssemblyConstructed = false
