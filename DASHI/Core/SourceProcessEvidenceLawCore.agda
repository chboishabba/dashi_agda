module DASHI.Core.SourceProcessEvidenceLawCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.SourceProcessEvidenceCore as SourceProcessEvidence
import DASHI.Core.StatisticalEvidenceCore as StatisticalEvidence

------------------------------------------------------------------------
-- Reusable source-process law shapes.
--
-- Receipts state that canonical patterns exist (candidate-only behavior,
-- inclusion, and escalation flags).  This law layer extracts reusable
-- escalation/inclusion relations while preserving that source-wide
-- escalation remains blocked without a separate source-model receipt.

record SourceProcessEvidenceInclusionEscalationLaw
  (sourceSurface : SourceProcessEvidence.SourceProcessEvidenceSurface)
  (sourceReceipt : SourceProcessEvidence.SourceProcessEvidenceReceipt sourceSurface)
  (sourceModelSurface : StatisticalEvidence.StatisticalEvidenceSurface)
  (sourceModelReceipt : StatisticalEvidence.StatisticalEvidenceReceipt sourceModelSurface) :
  Set where
  constructor sourceProcessEvidenceInclusionEscalationLaw
  field
    restrictedSourceFiberInclusion :
      SourceProcessEvidence.sideEvidenceRestrictsFiber sourceSurface ≡ true

    anomalyCandidateOnly :
      SourceProcessEvidence.statisticalAnomalyCandidateOnly sourceSurface ≡ true

    anomalyNotAuthority :
      SourceProcessEvidence.statisticalAnomalySourceCompromiseAuthority sourceSurface
      ≡
      false

    anomalyNoSecurityAuthorityPromotion :
      SourceProcessEvidence.securityAuthority sourceSurface ≡ false

    recoveredWitnessArtifactLocalEscalation :
      SourceProcessEvidence.recoveredWitnessEscalatesArtifactOnly sourceSurface ≡ true

    sourceWideEscalationRequiresSourceModelReceipt :
      SourceProcessEvidence.sourceWideEscalationAuthority sourceSurface ≡ false

    sourceModelReceiptDoesNotEscalate :
      SourceProcessEvidence.sourceWideEscalationAuthority sourceSurface ≡ false

open SourceProcessEvidenceInclusionEscalationLaw public

mkSourceProcessEvidenceInclusionEscalationLaw :
  (sourceSurface : SourceProcessEvidence.SourceProcessEvidenceSurface)
  (sourceReceipt : SourceProcessEvidence.SourceProcessEvidenceReceipt sourceSurface) →
  (sourceModelSurface : StatisticalEvidence.StatisticalEvidenceSurface) →
  (sourceModelReceipt : StatisticalEvidence.StatisticalEvidenceReceipt sourceModelSurface) →
  SourceProcessEvidenceInclusionEscalationLaw
    sourceSurface
    sourceReceipt
    sourceModelSurface
    sourceModelReceipt
mkSourceProcessEvidenceInclusionEscalationLaw
  _ sourceReceipt _ _ =
  sourceProcessEvidenceInclusionEscalationLaw
    (SourceProcessEvidence.receiptSideEvidenceRestrictsFiberIsTrue sourceReceipt)
    (SourceProcessEvidence.receiptStatisticalAnomalyCandidateOnlyIsTrue sourceReceipt)
    (SourceProcessEvidence.receiptStatisticalAnomalySourceCompromiseAuthorityIsFalse
      sourceReceipt)
    (SourceProcessEvidence.receiptSecurityAuthorityIsFalse sourceReceipt)
    (SourceProcessEvidence.receiptRecoveredWitnessEscalatesArtifactOnlyIsTrue
      sourceReceipt)
    (SourceProcessEvidence.receiptSourceWideEscalationAuthorityIsFalse sourceReceipt)
    (SourceProcessEvidence.receiptSourceWideEscalationAuthorityIsFalse sourceReceipt)

------------------------------------------------------------------------
-- Canonical law shape over canonical core surfaces.

canonicalSourceProcessEvidenceInclusionEscalationLaw :
  SourceProcessEvidenceInclusionEscalationLaw
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
    SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt
    StatisticalEvidence.canonicalStatisticalEvidenceSurface
    StatisticalEvidence.canonicalStatisticalEvidenceReceipt
canonicalSourceProcessEvidenceInclusionEscalationLaw =
  mkSourceProcessEvidenceInclusionEscalationLaw
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
    SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt
    StatisticalEvidence.canonicalStatisticalEvidenceSurface
    StatisticalEvidence.canonicalStatisticalEvidenceReceipt

sourceProcessEvidenceRestrictedSourceFiberInclusionIsTrue :
  SourceProcessEvidence.sideEvidenceRestrictsFiber
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
sourceProcessEvidenceRestrictedSourceFiberInclusionIsTrue =
  restrictedSourceFiberInclusion
    canonicalSourceProcessEvidenceInclusionEscalationLaw

sourceProcessEvidenceAnomalyCandidateOnlyIsTrue :
  SourceProcessEvidence.statisticalAnomalyCandidateOnly
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
sourceProcessEvidenceAnomalyCandidateOnlyIsTrue =
  anomalyCandidateOnly canonicalSourceProcessEvidenceInclusionEscalationLaw

sourceProcessEvidenceAnomalyNotAuthorityIsFalse :
  SourceProcessEvidence.statisticalAnomalySourceCompromiseAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
sourceProcessEvidenceAnomalyNotAuthorityIsFalse =
  anomalyNotAuthority canonicalSourceProcessEvidenceInclusionEscalationLaw

sourceProcessEvidenceRecoveredWitnessArtifactLocalEscalationIsTrue :
  SourceProcessEvidence.recoveredWitnessEscalatesArtifactOnly
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
sourceProcessEvidenceRecoveredWitnessArtifactLocalEscalationIsTrue =
  recoveredWitnessArtifactLocalEscalation
    canonicalSourceProcessEvidenceInclusionEscalationLaw

sourceProcessEvidenceSourceWideEscalationIsFalseWithoutSourceModelReceipt :
  SourceProcessEvidence.sourceWideEscalationAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
sourceProcessEvidenceSourceWideEscalationIsFalseWithoutSourceModelReceipt =
  sourceWideEscalationRequiresSourceModelReceipt
    canonicalSourceProcessEvidenceInclusionEscalationLaw

sourceProcessEvidenceSourceWideEscalationIsFalseWithoutSourcePromotion :
  SourceProcessEvidence.sourceWideEscalationAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
sourceProcessEvidenceSourceWideEscalationIsFalseWithoutSourcePromotion =
  sourceModelReceiptDoesNotEscalate
    canonicalSourceProcessEvidenceInclusionEscalationLaw
