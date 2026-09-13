module DASHI.Applications.CounterUASOpenWorldBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASOpenSetRFExact as RF
import DASHI.Applications.OpenClosedWorldRecognitionExact as OpenClosed

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

------------------------------------------------------------------------
-- Typed relationship:
--
-- The RF owner pays an open-set-like capability: novel activity can remain
-- unknown instead of being forced into a known catalogue label.
-- The generic open-world owner separately requires incremental incorporation.
-- Therefore the first capability alone cannot establish the second regime.
------------------------------------------------------------------------

rfUnknownHandlingRegime : OpenClosed.RecognitionRegime
rfUnknownHandlingRegime = OpenClosed.openSet

fullIncrementalRegime : OpenClosed.RecognitionRegime
fullIncrementalRegime = OpenClosed.openWorld

rfUnknownState : RF.RFDetectionState
rfUnknownState = RF.unknownRFActivity

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
