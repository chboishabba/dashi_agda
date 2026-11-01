module DASHI.Interop.PointedSignAntipodal369SeparationExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION WITHOUT NUMERICAL CONFLATION
--
-- Two recurring repo constructions look similar but are not identical:
--
--   ternary antipodal plane:  9 = 1 + 4*2
--   pointed five-mode sign:   11 = 1 + 5*2
--
-- The second is the existing SSP15 `PointedSignedCarrier X`: one distinguished
-- observer plus a mode paired with direct/counter binary phase.  The first is
-- the strict-antipodal quotient decomposition of T^2: one fixed centre plus
-- four noncentral sign pairs.
--
-- Keeping both typed prevents the remembered `5*2+1` SSP motif from being
-- accidentally asserted as the cardinal decomposition of the nine-state plane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Biology.SSP15NineObserverAtlasExact as Atlas
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit

ternaryNineIsCentrePlusFourSignPairs : 9 ≡ 1 + 4 * 2
ternaryNineIsCentrePlusFourSignPairs = Orbit.nineDecomposesAsCentrePlusFourPairs

pointedFiveModeSignSizeIsEleven : Atlas.pointedSignedSizeFormula 5 ≡ 11
pointedFiveModeSignSizeIsEleven = Atlas.pointedSignedFiveIsEleven

nineIsNotEleven : 9 ≡ 11 → ⊥
nineIsNotEleven ()

ternaryNineCardinalityIsNotPointedFiveModeCardinality :
  9 ≡ Atlas.pointedSignedSizeFormula 5 → ⊥
ternaryNineCardinalityIsNotPointedFiveModeCardinality = nineIsNotEleven

record PointedSignAntipodal369Boundary : Set where
  constructor pointedSignAntipodal369Boundary
  field
    ternaryNineUsesFourNoncentralAntipodalModes : Bool
    pointedFiveModeCarrierHasElevenStates : Bool
    equalLookingModePhaseFormulaMeansSameCarrier : Bool
    eitherCardinalityEqualitySuppliesSemanticIdentification : Bool

canonicalPointedSignAntipodal369Boundary : PointedSignAntipodal369Boundary
canonicalPointedSignAntipodal369Boundary =
  pointedSignAntipodal369Boundary true true false false
