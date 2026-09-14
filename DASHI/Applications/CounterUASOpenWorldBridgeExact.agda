module DASHI.Applications.CounterUASOpenWorldBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASOpenSetRFExact as RF
import DASHI.Applications.OpenClosedWorldRecognitionExact as OpenClosed
import DASHI.Applications.OpenWorldTemporalPromotionExact as Temporal
import DASHI.Applications.CounterUASNoveltyPromotionExact as Promotion

------------------------------------------------------------------------
-- DRONESHIELD / OPEN-WORLD RECOGNITION BRIDGE
--
-- This is a retrospective DASHI cross-domain bridge.  It does not claim that
-- DroneShield implements any academic open-world algorithm, nor that vendor
-- terminology is historically derived from the cited recognition literature.
------------------------------------------------------------------------

unknownSurfacingProvesFullOpenWorldLearning : Bool
unknownSurfacingProvesFullOpenWorldLearning = false

signatureReferenceAccumulationEqualsIncrementalClassLearning : Bool
signatureReferenceAccumulationEqualsIncrementalClassLearning = false

vendorClaimInheritsAcademicAlgorithmIdentity : Bool
vendorClaimInheritsAcademicAlgorithmIdentity = false

generalOpenWorldPaperValidatesVendorImplementation : Bool
generalOpenWorldPaperValidatesVendorImplementation = false

laterSignatureRetroactivelyRewritesEarlierObservation : Bool
laterSignatureRetroactivelyRewritesEarlierObservation = false

confidenceScoreCreatesKnownIdentity : Bool
confidenceScoreCreatesKnownIdentity = false

rfNoveltyEvidenceCreatesThreatAuthority : Bool
rfNoveltyEvidenceCreatesThreatAuthority = false

selfAgreementPaysSemanticPromotion : Bool
selfAgreementPaysSemanticPromotion = false

referenceMatchBypassesIntegrityCheck : Bool
referenceMatchBypassesIntegrityCheck = false

------------------------------------------------------------------------
-- Typed relationship:
--
-- The RF owner pays an open-set-like capability: novel activity can remain
-- unknown instead of being forced into a known catalogue label.
-- The generic open-world owner separately requires incremental incorporation.
-- The promotion owner further requires provenance/genealogy payment before a
-- repeated match can be promoted beyond characterization.
------------------------------------------------------------------------

rfUnknownHandlingRegime : OpenClosed.RecognitionRegime
rfUnknownHandlingRegime = OpenClosed.openSet

fullIncrementalRegime : OpenClosed.RecognitionRegime
fullIncrementalRegime = OpenClosed.openWorld

rfUnknownState : RF.RFDetectionState
rfUnknownState = RF.unknownRFActivity

rfUnknownThenLaterRecognizedReceipt : Temporal.TemporalKnowledgeReceipt
rfUnknownThenLaterRecognizedReceipt =
  Temporal.canonicalUnknownThenRecognizedReceipt

selfGeneratedAgreementReceipt : Promotion.NoveltyPromotionReceipt
selfGeneratedAgreementReceipt = Promotion.selfEchoReceipt

externallyPaidPromotionReceipt : Promotion.NoveltyPromotionReceipt
externallyPaidPromotionReceipt = Promotion.externallyPaidReceipt

selfGeneratedAgreementIsBlocked :
  Promotion.promotionStatus selfGeneratedAgreementReceipt ≡ Promotion.promotionBlocked
selfGeneratedAgreementIsBlocked = Promotion.selfEchoPromotionBlocked

externallyPaidPromotionIsEligible :
  Promotion.promotionStatus externallyPaidPromotionReceipt ≡ Promotion.promotionEligible
externallyPaidPromotionIsEligible = Promotion.externalPaymentPromotionEligible

record CounterUASOpenWorldBoundary : Set where
  constructor counterUASOpenWorldBoundary
  field
    unknownCanRemainUnknown : Bool
    unknownCanRemainUnknownIsTrue : unknownCanRemainUnknown ≡ true
    unknownHandlingImpliesIncrementalClassLearning : Bool
    unknownHandlingImpliesIncrementalClassLearningIsFalse :
      unknownHandlingImpliesIncrementalClassLearning ≡ false
    generatedReferenceImpliesSemanticClassIdentity : Bool
    generatedReferenceImpliesSemanticClassIdentityIsFalse :
      generatedReferenceImpliesSemanticClassIdentity ≡ false
    confidenceImpliesKnownIdentity : Bool
    confidenceImpliesKnownIdentityIsFalse : confidenceImpliesKnownIdentity ≡ false
    laterRecognitionRewritesEncounterUnknown : Bool
    laterRecognitionRewritesEncounterUnknownIsFalse :
      laterRecognitionRewritesEncounterUnknown ≡ false
    noveltyEvidenceImpliesThreatAuthority : Bool
    noveltyEvidenceImpliesThreatAuthorityIsFalse :
      noveltyEvidenceImpliesThreatAuthority ≡ false
    selfAgreementImpliesPromotionEligibility : Bool
    selfAgreementImpliesPromotionEligibilityIsFalse :
      selfAgreementImpliesPromotionEligibility ≡ false
    referenceMatchImpliesCleanGenealogy : Bool
    referenceMatchImpliesCleanGenealogyIsFalse :
      referenceMatchImpliesCleanGenealogy ≡ false
    retrospectiveCrossPollinationIsHistoricalIdentity : Bool
    retrospectiveCrossPollinationIsHistoricalIdentityIsFalse :
      retrospectiveCrossPollinationIsHistoricalIdentity ≡ false

canonicalCounterUASOpenWorldBoundary : CounterUASOpenWorldBoundary
canonicalCounterUASOpenWorldBoundary =
  counterUASOpenWorldBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
