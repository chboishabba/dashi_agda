{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyGeneralizedTPS2026AuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- CROSS-PROVER AUTHORITY: FINITE-DIMENSIONAL OPERATOR-ALGEBRA g-TPS
--
-- Lean source owner:
--   RequestProject.QuantumMereologyGeneralizedTPS2026
--
-- Lean source-writes a literal finite-dimensional carrier consisting of two
-- complex matrix subalgebras with elementwise commutation and joint generation
-- of the full matrix algebra.  On any declared finite candidate family with a
-- real scrambling score and a nonempty admissible subset, the existing finite
-- minimum theorem yields a selected minimizer.
--
-- External scientific source:
--   Zanardi, Dallas, Andreadakis, Phys. Rev. A 113, 042201 (2026),
--   DOI 10.1103/r193-5s7w.
--
-- The source's actual scrambling functional, information-geometric metric,
-- algebra susceptibility and m-QPT theorem are NOT reconstructed by this
-- cross-prover receipt.  Nor is the g-TPS objective identified with the
-- Carroll--Singh Schwinger objective.
------------------------------------------------------------------------

record GeneralizedTPS2026Status : Set where
  field
    OperatorAlgebraGTPSCarrierSourceWritten : Bool
    OperatorAlgebraGTPSCarrierSourceWrittenIsTrue :
      OperatorAlgebraGTPSCarrierSourceWritten ≡ true

    FiniteGTPSFamilyHasMinimizerSourceWritten : Bool
    FiniteGTPSFamilyHasMinimizerSourceWrittenIsTrue :
      FiniteGTPSFamilyHasMinimizerSourceWritten ≡ true

    SourceScramblingFunctionalReconstructed : Bool
    SourceScramblingFunctionalReconstructedIsFalse :
      SourceScramblingFunctionalReconstructed ≡ false

    SourceInformationMetricReconstructed : Bool
    SourceInformationMetricReconstructedIsFalse :
      SourceInformationMetricReconstructed ≡ false

    AlgebraSusceptibilityReconstructed : Bool
    AlgebraSusceptibilityReconstructedIsFalse :
      AlgebraSusceptibilityReconstructed ≡ false

    FiniteSelectedArchitectureChangeCreatesMQPT : Bool
    FiniteSelectedArchitectureChangeCreatesMQPTIsFalse :
      FiniteSelectedArchitectureChangeCreatesMQPT ≡ false

    GeneralizedTPSCreatesPhysicalSubsystemAuthority : Bool
    GeneralizedTPSCreatesPhysicalSubsystemAuthorityIsFalse :
      GeneralizedTPSCreatesPhysicalSubsystemAuthority ≡ false

    GeneralizedTPSObjectiveEqualsCarrollSinghObjective : Bool
    GeneralizedTPSObjectiveEqualsCarrollSinghObjectiveIsFalse :
      GeneralizedTPSObjectiveEqualsCarrollSinghObjective ≡ false

canonicalGeneralizedTPS2026Status : GeneralizedTPS2026Status
canonicalGeneralizedTPS2026Status = record
  { OperatorAlgebraGTPSCarrierSourceWritten = true
  ; OperatorAlgebraGTPSCarrierSourceWrittenIsTrue = refl
  ; FiniteGTPSFamilyHasMinimizerSourceWritten = true
  ; FiniteGTPSFamilyHasMinimizerSourceWrittenIsTrue = refl
  ; SourceScramblingFunctionalReconstructed = false
  ; SourceScramblingFunctionalReconstructedIsFalse = refl
  ; SourceInformationMetricReconstructed = false
  ; SourceInformationMetricReconstructedIsFalse = refl
  ; AlgebraSusceptibilityReconstructed = false
  ; AlgebraSusceptibilityReconstructedIsFalse = refl
  ; FiniteSelectedArchitectureChangeCreatesMQPT = false
  ; FiniteSelectedArchitectureChangeCreatesMQPTIsFalse = refl
  ; GeneralizedTPSCreatesPhysicalSubsystemAuthority = false
  ; GeneralizedTPSCreatesPhysicalSubsystemAuthorityIsFalse = refl
  ; GeneralizedTPSObjectiveEqualsCarrollSinghObjective = false
  ; GeneralizedTPSObjectiveEqualsCarrollSinghObjectiveIsFalse = refl
  }

zanardiDallasAndreadakis2026GTPSClaim : Sources.AttributionReceipt
zanardiDallasAndreadakis2026GTPSClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w"
    "Uses variational operator-algebra families as generalized tensor-product structures, selects them by a scrambling functional and pulls back an information-geometric metric whose singular response is called algebra susceptibility. The citation does not create a DASHI implementation of those source formulas or a physical m-QPT theorem."

leanGeneralizedTPS2026SourceReceipt : Sources.AttributionReceipt
leanGeneralizedTPS2026SourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyGeneralizedTPS2026"
    "Source-written finite-dimensional two-subalgebra generalized-TPS carrier with exact commutation/joint-generation fields plus finite nonempty real-score minimizer existence. The paper-specific scrambling functional, metric and susceptibility remain unreconstructed."

dashiGeneralizedTPS2026CrossProverReceipt : Sources.AttributionReceipt
dashiGeneralizedTPS2026CrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the Lean operator-algebra g-TPS carrier and finite-family minimizer while preserving source-formula, physical-subsystem, m-QPT and Carroll--Singh-equivalence firewalls."
