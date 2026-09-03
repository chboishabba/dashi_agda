module DASHI.Physics.QuantumVacuum.CasimirBishopSetoidBackendReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.BishopConstructedRealBackendExact as Bishop
import DASHI.Analysis.FastCauchyRationalRealBackendCutsetExact as LocalCutset

------------------------------------------------------------------------
-- CASIMIR CONSTRUCTIVE-REAL BACKEND CORRECTION
--
-- The repo already contains a concrete imported Bishop setoid real backend.
-- Casimir therefore does not need to rebuild the rational fast-Cauchy quotient
-- merely to obtain a complete ordered real carrier.  The local fast-Cauchy
-- cutset remains useful as an independent backend-development lane.
------------------------------------------------------------------------

casimirSetoidReal : Spine.SetoidOrderedCompleteReal
casimirSetoidReal = Bishop.bishopImportedSetoidOrderedCompleteReal

casimirConstructiveBackend : Spine.ConstructiveRealBackend
casimirConstructiveBackend = Bishop.bishopImportedConstructiveRealBackend

record BackendReuseReceipt : Set where
  field
    bishopCarrierImported : Bool
    bishopCompletenessImported : Bool
    bishopAlgebraOrderImported : Bool
    localFastCauchyBackendRequiredForCasimir : Bool

    bishopCarrierImportedIsTrue : bishopCarrierImported ≡ true
    bishopCompletenessImportedIsTrue : bishopCompletenessImported ≡ true
    bishopAlgebraOrderImportedIsTrue : bishopAlgebraOrderImported ≡ true
    localFastCauchyBackendRequiredForCasimirIsFalse :
      localFastCauchyBackendRequiredForCasimir ≡ false

canonicalBackendReuseReceipt : BackendReuseReceipt
canonicalBackendReuseReceipt = record
  { bishopCarrierImported = true
  ; bishopCompletenessImported = true
  ; bishopAlgebraOrderImported = true
  ; localFastCauchyBackendRequiredForCasimir = false
  ; bishopCarrierImportedIsTrue = refl
  ; bishopCompletenessImportedIsTrue = refl
  ; bishopAlgebraOrderImportedIsTrue = refl
  ; localFastCauchyBackendRequiredForCasimirIsFalse = refl
  }

------------------------------------------------------------------------
-- The remaining seam is not completeness.  It is representation: the legacy
-- Casimir scalar kernel uses propositional equality, while Bishop's concrete
-- backend is setoid-aware.  Either stay setoid-native through the analysis or
-- provide an explicit propositional quotient realization at the final weld.
------------------------------------------------------------------------

record LegacyKernelWeldObligations : Set₁ where
  field
    quotientOrSetoidNativeRouteChosen : Set
    casimirConstantsRepresented : Set
    casimirArithmeticRepresented : Set
    casimirPowerSemanticsRepresented : Set
    finalLegacyKernelWeld : Set
    reading : String

open LegacyKernelWeldObligations public

data ImportedCompletenessAutomaticallySuppliesLegacyEqualityWeld : Set where

completenessDoesNotCollapseSetoidToPropositionalEquality :
  ImportedCompletenessAutomaticallySuppliesLegacyEqualityWeld → ⊥
completenessDoesNotCollapseSetoidToPropositionalEquality ()
