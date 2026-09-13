module DASHI.Applications.CounterUASOpenWorldBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASOpenWorldBridgeExact as Bridge
import DASHI.Applications.OpenWorldTemporalPromotionExact as Temporal

record CounterUASOpenWorldBridgeRegression : Set where
  constructor counterUASOpenWorldBridgeRegression
  field
    unknownSurfacingIsOpenSetLikeNotOpenWorldProof :
      Bridge.unknownSurfacingProvesFullOpenWorldLearning ≡ false
    signatureAccumulationIsNotIncrementalClassLearning :
      Bridge.signatureReferenceAccumulationEqualsIncrementalClassLearning ≡ false
    vendorClaimDoesNotInheritAcademicAlgorithm :
      Bridge.vendorClaimInheritsAcademicAlgorithmIdentity ≡ false
    generalPaperDoesNotValidateVendorImplementation :
      Bridge.generalOpenWorldPaperValidatesVendorImplementation ≡ false
    laterSignatureDoesNotRewriteEarlierUnknownObservation :
      Bridge.laterSignatureRetroactivelyRewritesEarlierObservation ≡ false
    confidenceDoesNotCreateKnownIdentity :
      Bridge.confidenceScoreCreatesKnownIdentity ≡ false
    noveltyEvidenceDoesNotCreateThreatAuthority :
      Bridge.rfNoveltyEvidenceCreatesThreatAuthority ≡ false
    temporalReceiptRetainsEncounterState :
      Temporal.encounterStateRetained Bridge.rfUnknownThenLaterRecognizedReceipt ≡ true
    temporalReceiptDoesNotRewriteEncounter :
      Temporal.laterLabelDoesNotRewriteEncounter Bridge.rfUnknownThenLaterRecognizedReceipt ≡ true
    noveltyPromotionReceiptIsNonAuthoritative :
      Temporal.stageCreatesOperationalAuthority Temporal.noveltyObservationReceipt ≡ false

canonicalCounterUASOpenWorldBridgeRegression :
  CounterUASOpenWorldBridgeRegression
canonicalCounterUASOpenWorldBridgeRegression =
  counterUASOpenWorldBridgeRegression
    refl refl refl refl refl refl refl refl refl refl
