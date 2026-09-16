module DASHI.Applications.CounterUASNoveltyPromotionWorldMonitorBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASNoveltyPromotionExact as Promotion
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact as WorldMonitor
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthSourceAtlasExact as Sources

------------------------------------------------------------------------
-- THIN WORLDMONITOR -> NOVELTY-PROMOTION ADAPTER
--
-- WorldMonitor contributes an implementation precedent for evidence health:
-- freshness, explicit gaps, source genealogy/diversity, and baseline context.
-- CounterUASNoveltyPromotionExact remains the owner of same-object,
-- non-circularity, reference-integrity, external-label and contradiction gates.
------------------------------------------------------------------------

worldMonitorHealthGate : WorldMonitor.EvidenceHealthReceipt → Bool
worldMonitorHealthGate receipt with
  WorldMonitor.freshness receipt |
  WorldMonitor.genealogy receipt |
  WorldMonitor.diversity receipt |
  WorldMonitor.gapState receipt
... | WorldMonitor.freshState
    | WorldMonitor.independentSources
    | WorldMonitor.multipleSourceFamilies
    | WorldMonitor.noDeclaredGap = true
... | _ | _ | _ | _ = false

worldMonitorGapPaysPromotion : Bool
worldMonitorGapPaysPromotion =
  worldMonitorHealthGate WorldMonitor.canonicalGapEvidenceReceipt

worldMonitorHealthyEvidencePaysHealthGate : Bool
worldMonitorHealthyEvidencePaysHealthGate =
  worldMonitorHealthGate WorldMonitor.canonicalHealthyEvidenceReceipt

worldMonitorEvidenceHealthCreatesOperationalAuthority : Bool
worldMonitorEvidenceHealthCreatesOperationalAuthority = false

promotionStatusWithWorldMonitorHealth :
  Promotion.NoveltyPromotionReceipt →
  WorldMonitor.EvidenceHealthReceipt →
  Promotion.PromotionStatus
promotionStatusWithWorldMonitorHealth promotionReceipt healthReceipt with
  worldMonitorHealthGate healthReceipt
... | true = Promotion.promotionStatus promotionReceipt
... | false = Promotion.promotionBlocked

healthyExternalPromotionEligible :
  promotionStatusWithWorldMonitorHealth
    Promotion.externallyPaidReceipt
    WorldMonitor.canonicalHealthyEvidenceReceipt
  ≡ Promotion.promotionEligible
healthyExternalPromotionEligible = refl

gappedExternalPromotionBlocked :
  promotionStatusWithWorldMonitorHealth
    Promotion.externallyPaidReceipt
    WorldMonitor.canonicalGapEvidenceReceipt
  ≡ Promotion.promotionBlocked
gappedExternalPromotionBlocked = refl

healthySelfEchoStillBlocked :
  promotionStatusWithWorldMonitorHealth
    Promotion.selfEchoReceipt
    WorldMonitor.canonicalHealthyEvidenceReceipt
  ≡ Promotion.promotionBlocked
healthySelfEchoStillBlocked = refl

worldMonitorSourceAtlasCreatesAuthority : Bool
worldMonitorSourceAtlasCreatesAuthority =
  Sources.worldMonitorEvidenceHealthSourceAtlasCreatesAuthority

record CounterUASNoveltyPromotionWorldMonitorBoundary : Set where
  constructor counterUASNoveltyPromotionWorldMonitorBoundary
  field
    healthyEvidenceHealthAloneCreatesSemanticIdentity : Bool
    healthyEvidenceHealthAloneCreatesSemanticIdentityIsFalse :
      healthyEvidenceHealthAloneCreatesSemanticIdentity ≡ false
    gapStateCanPayPromotion : Bool
    gapStateCanPayPromotionIsFalse : gapStateCanPayPromotion ≡ false
    evidenceHealthCreatesOperationalAuthority : Bool
    evidenceHealthCreatesOperationalAuthorityIsFalse :
      evidenceHealthCreatesOperationalAuthority ≡ false
    implementationPrecedentCreatesProof : Bool
    implementationPrecedentCreatesProofIsFalse :
      implementationPrecedentCreatesProof ≡ false

canonicalCounterUASNoveltyPromotionWorldMonitorBoundary :
  CounterUASNoveltyPromotionWorldMonitorBoundary
canonicalCounterUASNoveltyPromotionWorldMonitorBoundary =
  counterUASNoveltyPromotionWorldMonitorBoundary
    false refl
    false refl
    false refl
    false refl
