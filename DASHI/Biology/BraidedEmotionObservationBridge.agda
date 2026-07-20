module DASHI.Biology.BraidedEmotionObservationBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionProcessBoundary as Emotion

------------------------------------------------------------------------
-- Episode / label / proxy / report separation.
--
-- This is intentionally carrier-level.  It does not identify an emotion
-- episode with a body residual, neural proxy, public word, or first-person
-- report.  It provides the typed seam required for later empirical adapters.

data ObservationSurface : Set where
  episodeSurface : ObservationSurface
  bodilyResidualProxySurface : ObservationSurface
  neuralMeasurementProxySurface : ObservationSurface
  firstPersonReportSurface : ObservationSurface
  publicEmotionLabelSurface : ObservationSurface
  relationalContextSurface : ObservationSurface

data EmpiricalStatus : Set where
  directEpisodeIdentityStatus : EmpiricalStatus
  measurementProxyStatus : EmpiricalStatus
  situatedReportStatus : EmpiricalStatus
  conceptualCompressionStatus : EmpiricalStatus
  relationalContextStatus : EmpiricalStatus
  notDirectlyObservedStatus : EmpiricalStatus

record EmotionObservationRow : Set where
  constructor mkEmotionObservationRow
  field
    surface : ObservationSurface
    status : EmpiricalStatus
    reading : String
    identifiesWholeEpisode : Bool
    diagnosticAuthority : Bool
    causalClosureClaimed : Bool

open EmotionObservationRow public

canonicalObservationRows : List EmotionObservationRow
canonicalObservationRows =
  mkEmotionObservationRow episodeSurface notDirectlyObservedStatus
    "the complete temporally extended organism-world episode is not directly recovered by one measure"
    true false false
  ∷ mkEmotionObservationRow bodilyResidualProxySurface measurementProxyStatus
    "a bodily residual may condition or track an episode without being identical to it"
    false false false
  ∷ mkEmotionObservationRow neuralMeasurementProxySurface measurementProxyStatus
    "a neural measurement is a bounded population or mechanism proxy rather than mind reading"
    false false false
  ∷ mkEmotionObservationRow firstPersonReportSurface situatedReportStatus
    "first-person report contributes irreducible situated evidence while remaining revisable"
    false false false
  ∷ mkEmotionObservationRow publicEmotionLabelSurface conceptualCompressionStatus
    "an emotion word may disclose compress reshape or obscure the episode"
    false false false
  ∷ mkEmotionObservationRow relationalContextSurface relationalContextStatus
    "relationship history place and obligation may partly constitute episode meaning"
    false false false
  ∷ []

record ObservationSeparationReceipt : Set where
  constructor mkObservationSeparationReceipt
  field
    episode : Emotion.EmotionEpisode
    label : Emotion.EmotionLabel
    rows : List EmotionObservationRow
    labelIsNotEpisode : Bool
    reportIsNotEpisode : Bool
    bodilyProxyIsNotEpisode : Bool
    neuralProxyIsNotEpisode : Bool
    relationIsNotPrivateBrainState : Bool
    proxyIsNotDiagnosis : Bool
    observationSeparationHolds : Bool
    observationSeparationHoldsIsTrue : observationSeparationHolds ≡ true

open ObservationSeparationReceipt public

canonicalObservationSeparationReceipt : ObservationSeparationReceipt
canonicalObservationSeparationReceipt =
  mkObservationSeparationReceipt
    Emotion.canonicalBraidedEpisode
    Emotion.canonicalProvisionalLabel
    canonicalObservationRows
    true
    true
    true
    true
    true
    true
    true
    refl
