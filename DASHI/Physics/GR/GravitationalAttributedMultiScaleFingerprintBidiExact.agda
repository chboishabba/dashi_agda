module DASHI.Physics.GR.GravitationalAttributedMultiScaleFingerprintBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact as Multi
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr

------------------------------------------------------------------------
-- ATTRIBUTION-PRESERVING MULTI-SCALE FINGERPRINT
--
-- Every scale prediction retains the exact attribution/proof-lineage carrier
-- for the prediction actually used in the physical fingerprint.  Attribution
-- cannot be dropped merely because several scales are aggregated.
------------------------------------------------------------------------

record AttributedScalePrediction : Set where
  constructor attributed-scale-prediction
  field
    scalePrediction : Multi.ScalePrediction
    attributedPrediction : Attr.AttributedGravitationalPrediction
    samePrediction :
      Attr.prediction attributedPrediction
        ≡ Multi.prediction scalePrediction

open AttributedScalePrediction public

record AttributedScaleComparison : Set where
  constructor attributed-scale-comparison
  field
    attributedScalePrediction : AttributedScalePrediction
    scaleComparison : Multi.ScaleComparison
    sameScalePrediction :
      scalePrediction attributedScalePrediction
        ≡ Multi.scalePrediction scaleComparison
    comparisonLineage :
      Attr.SinglePredictionComparisonLineage
        (attributedPrediction attributedScalePrediction)
        (Multi.observation scaleComparison)

open AttributedScaleComparison public

record AttributedMultiScaleTheoryFingerprint : Set where
  constructor attributed-multi-scale-theory-fingerprint
  field
    fingerprint : Multi.MultiScaleTheoryFingerprint
    laboratoryFreeFallAttribution : AttributedScalePrediction
    laboratoryClockAttribution : AttributedScalePrediction
    orbitalTimingAttribution : AttributedScalePrediction
    compactBinaryAttribution : AttributedScalePrediction
    nanohertzTimingAttribution : AttributedScalePrediction
    cosmologicalPropagationAttribution : AttributedScalePrediction
    freeFallMatchesFingerprint :
      scalePrediction laboratoryFreeFallAttribution
        ≡ Multi.laboratoryFreeFallPrediction fingerprint
    clockMatchesFingerprint :
      scalePrediction laboratoryClockAttribution
        ≡ Multi.laboratoryClockPrediction fingerprint
    orbitalMatchesFingerprint :
      scalePrediction orbitalTimingAttribution
        ≡ Multi.orbitalTimingPrediction fingerprint
    compactBinaryMatchesFingerprint :
      scalePrediction compactBinaryAttribution
        ≡ Multi.compactBinaryPrediction fingerprint
    nanohertzMatchesFingerprint :
      scalePrediction nanohertzTimingAttribution
        ≡ Multi.nanohertzTimingPrediction fingerprint
    cosmologicalMatchesFingerprint :
      scalePrediction cosmologicalPropagationAttribution
        ≡ Multi.cosmologicalPropagationPrediction fingerprint

open AttributedMultiScaleTheoryFingerprint public

record MultiScaleAttributionBoundary : Set where
  constructor multi-scale-attribution-boundary
  field
    aggregationMayDropSourceLineage : Bool
    oneScaleSourceMayBeReusedAsAuthorityForDifferentClaimWithoutReceipt : Bool
    internalTheoremMayBeRelabelledAsExternalPaper : Bool
    genericComparisonLineageMayFloatAcrossScaleInputs : Bool
    derivedCrossScaleComparisonIsExternalSourceClaim : Bool
    exactPredictionIdentityRequiredAtEveryScale : Bool

canonicalMultiScaleAttributionBoundary : MultiScaleAttributionBoundary
canonicalMultiScaleAttributionBoundary =
  multi-scale-attribution-boundary false false false false false true
