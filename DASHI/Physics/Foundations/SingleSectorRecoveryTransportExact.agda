{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.SingleSectorRecoveryTransportExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SingleSectorUnifiedCandidateExact as Single
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

------------------------------------------------------------------------
-- RECOVERY RECEIPTS SURVIVE SINGLE-SECTOR TOTALISATION SPECIALISATION
--
-- The specialisation changes only qftTotalStressShared and
-- QFTStressAggregation.  GR/QFT recovery data is otherwise definitionally the
-- same, so existing receipts can be replayed field-for-field.
------------------------------------------------------------------------

transportGRRecoveryToSingleSector :
  ∀ {U : Weld.UnifiedCandidate}
    (selectedGroup :
      Weld.Candidate U →
      QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  Weld.GRRecoveryReceipt U →
  Weld.GRRecoveryReceipt (Single.singleSectorUnifiedCandidate U selectedGroup)
transportGRRecoveryToSingleSector selectedGroup receipt = record
  { Weld.GRRecoveryReceipt.geometryAdapter =
      Weld.geometryAdapter receipt
  ; Weld.GRRecoveryReceipt.continuumManifoldConstructed =
      Weld.continuumManifoldConstructed receipt
  ; Weld.GRRecoveryReceipt.lorentzianMetricConstructed =
      Weld.lorentzianMetricConstructed receipt
  ; Weld.GRRecoveryReceipt.tensorSourceConstructed =
      Weld.tensorSourceConstructed receipt
  ; Weld.GRRecoveryReceipt.bianchiIdentityProved =
      Weld.bianchiIdentityProved receipt
  ; Weld.GRRecoveryReceipt.covariantConservationProved =
      Weld.covariantConservationProved receipt
  ; Weld.GRRecoveryReceipt.equivalencePrincipleRecovered =
      Weld.equivalencePrincipleRecovered receipt
  ; Weld.GRRecoveryReceipt.geodesicLimitRecovered =
      Weld.geodesicLimitRecovered receipt
  ; Weld.GRRecoveryReceipt.gravitationalRadiationRecovered =
      Weld.gravitationalRadiationRecovered receipt
  ; Weld.GRRecoveryReceipt.einsteinEquationRecovered =
      Weld.einsteinEquationRecovered receipt
  ; Weld.GRRecoveryReceipt.correctionBoundProved =
      Weld.correctionBoundProved receipt
  ; Weld.GRRecoveryReceipt.grRecoveryCommutes =
      Weld.grRecoveryCommutes receipt
  ; Weld.GRRecoveryReceipt.grRecoveryAfterCoarseGrainingCommutes =
      Weld.grRecoveryAfterCoarseGrainingCommutes receipt
  ; Weld.GRRecoveryReceipt.grPromotionToken =
      Weld.grPromotionToken receipt
  }

transportQFTRecoveryToSingleSector :
  ∀ {U : Weld.UnifiedCandidate}
    (selectedGroup :
      Weld.Candidate U →
      QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  Weld.QFTRecoveryReceipt U →
  Weld.QFTRecoveryReceipt (Single.singleSectorUnifiedCandidate U selectedGroup)
transportQFTRecoveryToSingleSector selectedGroup receipt = record
  { Weld.QFTRecoveryReceipt.quantumAdapter =
      Weld.quantumAdapter receipt
  ; Weld.QFTRecoveryReceipt.hilbertStructureRecovered =
      Weld.hilbertStructureRecovered receipt
  ; Weld.QFTRecoveryReceipt.relativisticLocalityRecovered =
      Weld.relativisticLocalityRecovered receipt
  ; Weld.QFTRecoveryReceipt.spinorSectorRecovered =
      Weld.spinorSectorRecovered receipt
  ; Weld.QFTRecoveryReceipt.localGaugeConnectionRecovered =
      Weld.localGaugeConnectionRecovered receipt
  ; Weld.QFTRecoveryReceipt.fockConstructionRecovered =
      Weld.fockConstructionRecovered receipt
  ; Weld.QFTRecoveryReceipt.stableParticlesRecovered =
      Weld.stableParticlesRecovered receipt
  ; Weld.QFTRecoveryReceipt.standardModelRepresentationsRecovered =
      Weld.standardModelRepresentationsRecovered receipt
  ; Weld.QFTRecoveryReceipt.anomaliesCancelled =
      Weld.anomaliesCancelled receipt
  ; Weld.QFTRecoveryReceipt.continuumLimitProved =
      Weld.continuumLimitProved receipt
  ; Weld.QFTRecoveryReceipt.qftRecoveryCommutes =
      Weld.qftRecoveryCommutes receipt
  ; Weld.QFTRecoveryReceipt.qftRecoveryAfterCoarseGrainingCommutes =
      Weld.qftRecoveryAfterCoarseGrainingCommutes receipt
  ; Weld.QFTRecoveryReceipt.qftPromotionToken =
      Weld.qftPromotionToken receipt
  }

singleSectorTotalisationChangesRecoveryTheorems : Bool
singleSectorTotalisationChangesRecoveryTheorems = false

singleSectorTotalisationChangesRecoveryTheoremsIsFalse :
  singleSectorTotalisationChangesRecoveryTheorems ≡ false
singleSectorTotalisationChangesRecoveryTheoremsIsFalse = refl
