{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySOTA2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- 2026 SOTA SOURCE BOUNDARY
--
-- External source only:
-- Arsalan Adil, Manuel S. Rudolph, Andrew Arrasmith, Zoë Holmes,
-- Andreas Albrecht, Andrew Sornborger,
-- "Search for classical subsystems in quantum worlds",
-- Phys. Rev. D 113, 103535 (2026), DOI 10.1103/vj4x-96fk.
--
-- The source reports several quasiclassical TPSs for fixed Hamiltonians and
-- emphasizes that decohering subsystems need not coincide with intuitive
-- classical locality.  These are source claims, not imported kernel theorems.
------------------------------------------------------------------------

record SOTA2026Boundary : Set where
  field
    sourceReportsSeveralQuasiclassicalFactorizations : Bool
    sourceReportsSeveralQuasiclassicalFactorizationsIsTrue :
      sourceReportsSeveralQuasiclassicalFactorizations ≡ true

    sourceReportsPointerRobustnessCriterion : Bool
    sourceReportsPointerRobustnessCriterionIsTrue :
      sourceReportsPointerRobustnessCriterion ≡ true

    sourceSaysDecoheringSubsystemsNeedNotMatchClassicalLocality : Bool
    sourceSaysDecoheringSubsystemsNeedNotMatchClassicalLocalityIsTrue :
      sourceSaysDecoheringSubsystemsNeedNotMatchClassicalLocality ≡ true

    sourceCreatesLocalNonuniquenessTheorem : Bool
    sourceCreatesLocalNonuniquenessTheoremIsFalse :
      sourceCreatesLocalNonuniquenessTheorem ≡ false

    sourceCreatesUniquePreferredTPS : Bool
    sourceCreatesUniquePreferredTPSIsFalse :
      sourceCreatesUniquePreferredTPS ≡ false

    sourceObjectiveIdentifiedWithCarrollSinghSchwingerScore : Bool
    sourceObjectiveIdentifiedWithCarrollSinghSchwingerScoreIsFalse :
      sourceObjectiveIdentifiedWithCarrollSinghSchwingerScore ≡ false

canonicalSOTA2026Boundary : SOTA2026Boundary
canonicalSOTA2026Boundary = record
  { sourceReportsSeveralQuasiclassicalFactorizations = true
  ; sourceReportsSeveralQuasiclassicalFactorizationsIsTrue = refl
  ; sourceReportsPointerRobustnessCriterion = true
  ; sourceReportsPointerRobustnessCriterionIsTrue = refl
  ; sourceSaysDecoheringSubsystemsNeedNotMatchClassicalLocality = true
  ; sourceSaysDecoheringSubsystemsNeedNotMatchClassicalLocalityIsTrue = refl
  ; sourceCreatesLocalNonuniquenessTheorem = false
  ; sourceCreatesLocalNonuniquenessTheoremIsFalse = refl
  ; sourceCreatesUniquePreferredTPS = false
  ; sourceCreatesUniquePreferredTPSIsFalse = refl
  ; sourceObjectiveIdentifiedWithCarrollSinghSchwingerScore = false
  ; sourceObjectiveIdentifiedWithCarrollSinghSchwingerScoreIsFalse = refl
  }

adilEtAl2026Claim : Sources.AttributionReceipt
adilEtAl2026Claim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Arsalan Adil et al., Phys. Rev. D 113, 103535 (2026), doi:10.1103/vj4x-96fk"
    "The source reports that fixed Hamiltonians can admit several quasiclassical tensor-product factorizations with pointer states robust to entanglement and that decohering subsystems need not coincide with intuitive classical locality. DASHI does not promote this to a universal local non-uniqueness theorem, a uniqueness theorem, or an identification with the Carroll--Singh Schwinger score."
