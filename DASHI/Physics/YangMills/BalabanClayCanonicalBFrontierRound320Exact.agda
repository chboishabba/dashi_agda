{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound320Exact where

------------------------------------------------------------------------
-- ROUND320 / CURRENT B CUT AFTER CONSUMER-FIRST H1 PRODUCER REDUCTION
--
-- The canonical B consumer remains R317's five coordinates.  This round does
-- not delete H1.  It only minimizes the preferred source-native producer for
-- H1 to the exact selected consumer carrier.
--
-- Preferred H1 producer:
--
--   one selected-carrier mixed-log-derivative separation theorem
--     -> normalized-source / literal-J transport (compiler)
--     -> R295 H1.
--
-- R318's general sourceMagnitude/sourceRoot/sourceDistance applicability route
-- remains a compatibility/import adapter for an externally presented theorem.
-- It is not mandatory when proof search works directly on the selected carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound317Exact as R317
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as Direct


data PreferredH1Residual320 : Set where
  selectedMixedDerivativeSeparationDecay : PreferredH1Residual320

preferredH1Role320 :
  PreferredH1Residual320 → Introspective.ProofSearchTargetRole
preferredH1Role320 selectedMixedDerivativeSeparationDecay =
  Introspective.optionalProducerTactic

record Round320CanonicalBoundary : Set where
  constructor round320-canonical-boundary
  field
    canonicalConsumerStillHasFiveCoordinates : Bool
    canonicalConsumerStillHasFiveCoordinatesIsTrue :
      canonicalConsumerStillHasFiveCoordinates ≡ true

    preferredH1ProducerHasOneAnalyticField : Bool
    preferredH1ProducerHasOneAnalyticFieldIsTrue :
      preferredH1ProducerHasOneAnalyticField ≡ true

    normalizedSourceLiteralJTransportCreatesNewYMAnalysis : Bool
    normalizedSourceLiteralJTransportCreatesNewYMAnalysisIsFalse :
      normalizedSourceLiteralJTransportCreatesNewYMAnalysis ≡ false

    r318ThreeApplicabilityEqualitiesMandatory : Bool
    r318ThreeApplicabilityEqualitiesMandatoryIsFalse :
      r318ThreeApplicabilityEqualitiesMandatory ≡ false

    preferredSourceRouteMandatoryForCanonicalB : Bool
    preferredSourceRouteMandatoryForCanonicalBIsFalse :
      preferredSourceRouteMandatoryForCanonicalB ≡ false

    directH1ConsumerAlreadyPaid : Bool
    directH1ConsumerAlreadyPaidIsFalse :
      directH1ConsumerAlreadyPaid ≡ false

canonicalRound320CanonicalBoundary : Round320CanonicalBoundary
canonicalRound320CanonicalBoundary =
  round320-canonical-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

-- Canonical consumer levels remain unchanged.
round320CanonicalH1Level : ProofLevel
round320CanonicalH1Level = R317.round317H1SelectedTwoJMagnitudeLocalizationLevel

round320CanonicalH2aLevel : ProofLevel
round320CanonicalH2aLevel = R317.round317H2aPhysicalTimeSupportSemanticsLevel

round320CanonicalH2bLevel : ProofLevel
round320CanonicalH2bLevel = R317.round317H2bSelectedWilsonPresentationLevel

round320CanonicalH2cLevel : ProofLevel
round320CanonicalH2cLevel = R317.round317H2cScalarOrderClosureLevel

round320CanonicalH3Level : ProofLevel
round320CanonicalH3Level = R317.round317H3TransferEnergyDecayCoordinateLevel

-- Preferred direct H1 producer.
round320PreferredSelectedMarkedDecayLevel : ProofLevel
round320PreferredSelectedMarkedDecayLevel =
  Direct.round320DirectSelectedMarkedDecayLevel

round320PreferredLiteralJTransportLevel : ProofLevel
round320PreferredLiteralJTransportLevel =
  Direct.round320LiteralJTransportCompilerLevel

-- General external-presentation compatibility route remains available.
round320GeneralR318ApplicabilityLevel : ProofLevel
round320GeneralR318ApplicabilityLevel = R318.round318SelectedJApplicabilityLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
