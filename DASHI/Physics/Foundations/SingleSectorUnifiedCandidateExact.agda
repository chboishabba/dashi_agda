{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.SingleSectorUnifiedCandidateExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

------------------------------------------------------------------------
-- SINGLE-ACTIVE-SECTOR SPECIALISATION OF UnifiedCandidate
--
-- Preserve every carrier/recovery/dynamics field of U and change only the
-- QFT-totalisation policy:
--
--   qftTotalStressShared candidate
--     := actualQFTSectorStressShared U candidate (selectedGroup candidate)
--
-- with aggregation meaning exactly singleton selection.
--
-- This is a model-construction choice for a one-sector candidate, not a theorem
-- that an arbitrary physical candidate has only one active gauge sector.
------------------------------------------------------------------------

singleSectorUnifiedCandidate :
  (U : Weld.UnifiedCandidate) →
  (selectedGroup :
    Weld.Candidate U →
    QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  Weld.UnifiedCandidate
singleSectorUnifiedCandidate U selectedGroup = record
  { Weld.UnifiedCandidate.Candidate =
      Weld.Candidate U
  ; Weld.UnifiedCandidate.Regime =
      Weld.Regime U
  ; Weld.UnifiedCandidate.Observable =
      Weld.Observable U
  ; Weld.UnifiedCandidate.Measurement =
      Weld.Measurement U
  ; Weld.UnifiedCandidate.SharedStressEnergy =
      Weld.SharedStressEnergy U

  ; Weld.UnifiedCandidate.GRRecoveryToken =
      Weld.GRRecoveryToken U
  ; Weld.UnifiedCandidate.QFTRecoveryToken =
      Weld.QFTRecoveryToken U
  ; Weld.UnifiedCandidate.StressEnergyWeldToken =
      Weld.StressEnergyWeldToken U
  ; Weld.UnifiedCandidate.RegimeRecoveryToken =
      Weld.RegimeRecoveryToken U
  ; Weld.UnifiedCandidate.NovelObservableToken =
      Weld.NovelObservableToken U
  ; Weld.UnifiedCandidate.FalsifiableMeasurementToken =
      Weld.FalsifiableMeasurementToken U

  ; Weld.UnifiedCandidate.microscopicState =
      Weld.microscopicState U
  ; Weld.UnifiedCandidate.coarseGrain =
      Weld.coarseGrain U

  ; Weld.UnifiedCandidate.grTarget =
      Weld.grTarget U
  ; Weld.UnifiedCandidate.recoverGR =
      Weld.recoverGR U

  ; Weld.UnifiedCandidate.qftCarriers =
      Weld.qftCarriers U
  ; Weld.UnifiedCandidate.qftSemantics =
      Weld.qftSemantics U
  ; Weld.UnifiedCandidate.qftTarget =
      Weld.qftTarget U
  ; Weld.UnifiedCandidate.recoverQFT =
      Weld.recoverQFT U

  ; Weld.UnifiedCandidate.grRegime =
      Weld.grRegime U
  ; Weld.UnifiedCandidate.qftRegime =
      Weld.qftRegime U

  ; Weld.UnifiedCandidate.grStressToShared =
      Weld.grStressToShared U
  ; Weld.UnifiedCandidate.qftSectorStressToShared =
      Weld.qftSectorStressToShared U

  ; Weld.UnifiedCandidate.qftTotalStressShared =
      λ candidate →
        Weld.actualQFTSectorStressShared U candidate
          (selectedGroup candidate)

  ; Weld.UnifiedCandidate.QFTStressAggregation =
      λ candidate sectorFamily total →
        total ≡ sectorFamily (selectedGroup candidate)

  ; Weld.UnifiedCandidate.BackreactionConsistent =
      Weld.BackreactionConsistent U
  ; Weld.UnifiedCandidate.CorrectionsControlled =
      Weld.CorrectionsControlled U

  ; Weld.UnifiedCandidate.unifiedPredicts =
      Weld.unifiedPredicts U
  ; Weld.UnifiedCandidate.establishedGRQFTPredicts =
      Weld.establishedGRQFTPredicts U
  ; Weld.UnifiedCandidate.measurementTests =
      Weld.measurementTests U
  }

singleSectorCandidateCarrierPreserved :
  ∀ (U : Weld.UnifiedCandidate) selectedGroup →
  Weld.Candidate (singleSectorUnifiedCandidate U selectedGroup)
  ≡ Weld.Candidate U
singleSectorCandidateCarrierPreserved U selectedGroup = refl

singleSectorRegimeCarrierPreserved :
  ∀ (U : Weld.UnifiedCandidate) selectedGroup →
  Weld.Regime (singleSectorUnifiedCandidate U selectedGroup)
  ≡ Weld.Regime U
singleSectorRegimeCarrierPreserved U selectedGroup = refl

singleSectorQFTTargetPreserved :
  ∀ (U : Weld.UnifiedCandidate) selectedGroup candidate →
  Weld.qftTarget (singleSectorUnifiedCandidate U selectedGroup) candidate
  ≡ Weld.qftTarget U candidate
singleSectorQFTTargetPreserved U selectedGroup candidate = refl

singleSectorGRTargetPreserved :
  ∀ (U : Weld.UnifiedCandidate) selectedGroup candidate →
  Weld.grTarget (singleSectorUnifiedCandidate U selectedGroup) candidate
  ≡ Weld.grTarget U candidate
singleSectorGRTargetPreserved U selectedGroup candidate = refl

singleSectorDeclaredTotalIsSelectedStress :
  ∀ (U : Weld.UnifiedCandidate)
    (selectedGroup :
      Weld.Candidate U →
      QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate →
  Weld.qftTotalStressShared
    (singleSectorUnifiedCandidate U selectedGroup) candidate
  ≡
  Weld.actualQFTSectorStressShared
    (singleSectorUnifiedCandidate U selectedGroup)
    candidate
    (selectedGroup candidate)
singleSectorDeclaredTotalIsSelectedStress U selectedGroup candidate = refl

singleSectorAggregationIsDefinitional :
  ∀ (U : Weld.UnifiedCandidate)
    (selectedGroup :
      Weld.Candidate U →
      QFT.CompactSimpleGroup (Weld.qftCarriers U))
    candidate →
  Weld.QFTStressAggregation
    (singleSectorUnifiedCandidate U selectedGroup)
    candidate
    (Weld.actualQFTSectorStressShared
      (singleSectorUnifiedCandidate U selectedGroup) candidate)
    (Weld.qftTotalStressShared
      (singleSectorUnifiedCandidate U selectedGroup) candidate)
singleSectorAggregationIsDefinitional U selectedGroup candidate = refl

singleSectorTotalEqualityIsPrimitiveTheorem : Bool
singleSectorTotalEqualityIsPrimitiveTheorem = false

singleSectorTotalEqualityIsPrimitiveTheoremIsFalse :
  singleSectorTotalEqualityIsPrimitiveTheorem ≡ false
singleSectorTotalEqualityIsPrimitiveTheoremIsFalse = refl

singleSectorSpecialisationClaimsAllPhysicalCandidatesAreSingleSector : Bool
singleSectorSpecialisationClaimsAllPhysicalCandidatesAreSingleSector = false

singleSectorSpecialisationClaimsAllPhysicalCandidatesAreSingleSectorIsFalse :
  singleSectorSpecialisationClaimsAllPhysicalCandidatesAreSingleSector ≡ false
singleSectorSpecialisationClaimsAllPhysicalCandidatesAreSingleSectorIsFalse = refl
