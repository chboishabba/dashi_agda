module DASHI.Applications.OpenClosedWorldRecognitionRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.OpenClosedWorldRecognitionExact as OpenClosed
import DASHI.Applications.OpenClosedWorldRecognitionSourceAtlasExact as Sources
import DASHI.Applications.OpenWorldTemporalPromotionExact as Temporal
import DASHI.Applications.OpenWorldTemporalPromotionSourceAtlasExact as TemporalSources
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

record OpenClosedWorldRecognitionRegression : Set where
  constructor openClosedWorldRecognitionRegression
  field
    closedSetRequiresAllTestClassesKnown :
      OpenClosed.closedSetAssumesKnownTestClasses ≡ true
    openSetAllowsUnknownTestClasses :
      OpenClosed.openSetAllowsUnknownTestClasses ≡ true
    openSetDoesNotRequireIncrementalIncorporation :
      OpenClosed.openSetRequiresIncrementalIncorporation ≡ false
    openWorldRequiresUnknownHandlingAndIncrementalLearning :
      OpenClosed.openWorldRequiresUnknownHandlingAndIncrementalLearning ≡ true
    oodDetectionIsNotOpenSetRecognition :
      OpenClosed.oodDetectionEqualsOpenSetRecognition ≡ false
    openSetRecognitionIsNotOpenWorldRecognition :
      OpenClosed.openSetEqualsOpenWorld ≡ false
    openWorldDetectionAddsLocalization :
      OpenClosed.openWorldObjectDetectionRequiresLocalization ≡ true
    unknownRecognitionDoesNotCreateKnownIdentity :
      OpenClosed.unknownRecognitionCreatesKnownIdentity ≡ false
    incrementalAdditionDoesNotRetroactivelyValidatePriorIdentity :
      OpenClosed.incrementalAdditionRetroactivelyValidatesPriorIdentity ≡ false
    closedSurfaceHasNoveltyAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        OpenClosed.closedProjection
        OpenClosed.recognitionSemantics
        OpenClosed.noveltyQuery
    openSetHandlingHasOpenWorldAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        OpenClosed.unknownHandlingProjection
        OpenClosed.learningSemantics
        OpenClosed.incrementalLearningQuery
    sourceAtlasNonPromoting :
      Sources.openClosedWorldSourceAtlasCreatesAuthority ≡ false

    uncertaintyIsNotUnknown :
      Temporal.uncertaintyEqualsUnknown ≡ false
    unknownNeedNotBeLowConfidence :
      Temporal.unknownRequiresLowConfidence ≡ false
    confidenceAloneHasNoveltyAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Temporal.confidenceOnlyProjection
        Temporal.noveltySemantics
        Temporal.noveltyStatusQuery
    laterRecognitionDoesNotRewriteEarlierUnknown :
      Temporal.laterRecognitionRewritesEncounterState ≡ false
    noveltyDetectionAloneIsNotContinualLearning :
      Temporal.noveltyDetectionEqualsContinualLearning ≡ false
    reportedScoreAloneHasEvaluationAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Temporal.reportedScoreProjection
        Temporal.evaluationSemantics
        Temporal.heldOutProtocolQuery
    testTunedThresholdIsNotHeldOutEvaluation :
      Temporal.testTunedThresholdCountsAsHeldOut ≡ false
    temporalSourceAtlasNonPromoting :
      TemporalSources.openWorldTemporalPromotionSourceAtlasCreatesAuthority ≡ false

canonicalOpenClosedWorldRecognitionRegression :
  OpenClosedWorldRecognitionRegression
canonicalOpenClosedWorldRecognitionRegression =
  openClosedWorldRecognitionRegression
    refl refl refl refl refl refl refl refl refl
    OpenClosed.closedSurfaceNoveltyAdequacyDefect
    OpenClosed.openSetSurfaceOpenWorldAdequacyDefect
    Sources.openClosedWorldSourceAtlasCreatesAuthorityIsFalse
    refl refl
    Temporal.confidenceOnlyNoveltyAdequacyDefect
    refl refl
    Temporal.reportedScoreOnlyAdequacyDefect
    refl
    TemporalSources.openWorldTemporalPromotionSourceAtlasCreatesAuthorityIsFalse
