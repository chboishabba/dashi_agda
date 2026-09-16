module DASHI.Applications.CounterUASNoveltyPromotionRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASNoveltyPromotionExact as Promotion
import DASHI.Applications.CounterUASNoveltyPromotionSourceAtlasExact as Sources
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact as WorldMonitor
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

record CounterUASNoveltyPromotionRegression : Set₁ where
  constructor counterUASNoveltyPromotionRegression
  field
    agreementCountDoesNotEstablishIndependentGenealogy :
      Promotion.agreementCountCreatesIndependentEvidence ≡ false
    pseudoLabelDoesNotCreateExternalCorroboration :
      Promotion.pseudoLabelCreatesExternalCorroboration ≡ false
    selfGeneratedReferenceDoesNotCreateSemanticIdentity :
      Promotion.selfGeneratedReferenceCreatesSemanticIdentity ≡ false
    promotionRequiresSameObjectPayment :
      Promotion.promotionRequiresSameObjectLink ≡ true
    promotionRequiresNonCircularPayment :
      Promotion.promotionRequiresNonCircularEvidence ≡ true
    contaminatedReferenceCannotPayPromotion :
      Promotion.contaminatedReferencePaysPromotion ≡ false
    agreementOnlyHasPromotionAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Promotion.agreementOnlyProjection
        Promotion.promotionSemantics
        Promotion.promotionEligibilityQuery
    referenceMatchOnlyHasIdentityAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Promotion.referenceMatchProjection
        Promotion.identitySemantics
        Promotion.semanticIdentityQuery
    worldMonitorGapCannotPayPromotion :
      Promotion.worldMonitorGapPaysPromotion ≡ false
    worldMonitorEvidenceHealthDoesNotCreateAuthority :
      Promotion.worldMonitorEvidenceHealthCreatesOperationalAuthority ≡ false
    worldMonitorSignalCountDefectRetained :
      Adequacy.QueryAdequacyDefect
        WorldMonitor.signalCountProjection
        WorldMonitor.evidenceHealthSemantics
        WorldMonitor.promotionEligibilityQuery
    sourceAtlasNonPromoting :
      Sources.noveltyPromotionSourceAtlasCreatesAuthority ≡ false

canonicalCounterUASNoveltyPromotionRegression :
  CounterUASNoveltyPromotionRegression
canonicalCounterUASNoveltyPromotionRegression =
  counterUASNoveltyPromotionRegression
    refl refl refl refl refl refl
    Promotion.agreementOnlyPromotionAdequacyDefect
    Promotion.referenceMatchOnlyIdentityAdequacyDefect
    refl refl
    WorldMonitor.signalCountEvidenceHealthAdequacyDefect
    Sources.noveltyPromotionSourceAtlasCreatesAuthorityIsFalse
