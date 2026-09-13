module DASHI.Empirical.DarkDimensionQuantitativeEnvelopeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- SOURCE-PRECISION-AWARE QUANTITATIVE ENVELOPES
--
-- This owner deliberately separates three kinds of numerical evidence:
--
--   * an exact source-reported fit coordinate (c' = 0.05 +/- 0.01);
--   * a source-reported interval (effective radius around 1-30 micrometres);
--   * a qualitative numerical scale (DAO amplitude described only as
--     "percent-level" in the primary abstract).
--
-- A source envelope is not a preregistered forecast.  In particular, the DAO
-- source does not supply one exact frozen amplitude in the inspected primary
-- surface, so no exact cross-model numerical separation is manufactured here.
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

------------------------------------------------------------------------
-- Canonical SI interval for the short-range-gravity / dark-dimension radius.
------------------------------------------------------------------------

record SIInterval (dimension : SI.Dimension) (scale : SI.DecimalScale) : Set where
  constructor siInterval
  field
    lower : SI.Quantity dimension scale
    upper : SI.Quantity dimension scale

open SIInterval public

darkDimensionRadiusLowerMicrometre : SI.Quantity SI.Length SI.microScale
darkDimensionRadiusLowerMicrometre = SI.posQ 1

darkDimensionRadiusUpperMicrometre : SI.Quantity SI.Length SI.microScale
darkDimensionRadiusUpperMicrometre = SI.posQ 30

darkDimensionRadiusEnvelope : SIInterval SI.Length SI.microScale
darkDimensionRadiusEnvelope =
  siInterval
    darkDimensionRadiusLowerMicrometre
    darkDimensionRadiusUpperMicrometre

lawSmithEtAl2024 : Source.AttributedSource
lawSmithEtAl2024 =
  Source.mkDOISource
    "Jamie A. P. Law-Smith; Georges Obied; Anirudh Prabhu; Cumrun Vafa"
    "Astrophysical constraints on decaying dark gravitons"
    "Journal of High Energy Physics 2024, 47"
    "2024"
    "10.1007/JHEP06(2024)047"
    "https://doi.org/10.1007/JHEP06(2024)047"
    Source.academicArticleSource
    "source for the natural effective-size interval around 1-30 micrometres in the decaying-dark-graviton Dark-Dimension scenario; this interval is not a laboratory detection claim"
    Source.publicAttribution

------------------------------------------------------------------------
-- Dimensionless evolving-dark-sector coupling coordinate.
------------------------------------------------------------------------

record RatioEstimate : Set where
  constructor ratioEstimate
  field
    central : Discrimination.DecimalRatio
    uncertainty : Discrimination.DecimalRatio
    externalUpperBound : Discrimination.DecimalRatio
    retrospectiveFit : Bool
    heldOutPrediction : Bool

open RatioEstimate public

bedroyaCPrimeEnvelope : RatioEstimate
bedroyaCPrimeEnvelope =
  ratioEstimate
    Discrimination.cPrimeBestFitFiveHundredths
    Discrimination.cPrimeUncertaintyOneHundredth
    Discrimination.cPrimeFifthForceUpperBoundTwoTenths
    true
    false

bedroyaSource : Source.AttributedSource
bedroyaSource = DarkDimension.bedroyaObiedVafaWu2026

------------------------------------------------------------------------
-- DAO precision boundary.
------------------------------------------------------------------------

data AmplitudePrecision : Set where
  exactAmplitude : AmplitudePrecision
  intervalAmplitude : AmplitudePrecision
  qualitativeScaleAmplitude : AmplitudePrecision

data QualitativeAmplitudeBand : Set where
  percentLevelAmplitude : QualitativeAmplitudeBand

record DAOAmplitudeEnvelope : Set where
  constructor daoAmplitudeEnvelope
  field
    source : Source.AttributedSource
    precision : AmplitudePrecision
    qualitativeBand : QualitativeAmplitudeBand
    exactNumericalAmplitudeLocked : Bool
    futureFullShapeScrutinyNamed : Bool

open DAOAmplitudeEnvelope public

daoPercentLevelAmplitudeBand : DAOAmplitudeEnvelope
daoPercentLevelAmplitudeBand =
  daoAmplitudeEnvelope
    Discrimination.darkAcousticOscillationSource
    qualitativeScaleAmplitude
    percentLevelAmplitude
    false
    true

------------------------------------------------------------------------
-- Cross-model numerical-separation status.
------------------------------------------------------------------------

record QuantitativeEnvelopeStatus : Set where
  constructor quantitativeEnvelopeStatus
  field
    darkDimensionRadiusRangeRecorded : Bool
    bedroyaCPrimeFitRecorded : Bool
    daoPercentLevelScaleRecorded : Bool
    daoExactAmplitudeRecorded : Bool
    sourceValuesFrozenAsProspectivePrediction : Bool
    crossModelNumericalSeparationLocked : Bool
    preregistrationIdentifierRecorded : Bool
    heldOutFutureComparisonPerformed : Bool

open QuantitativeEnvelopeStatus public

canonicalQuantitativeEnvelopeStatus : QuantitativeEnvelopeStatus
canonicalQuantitativeEnvelopeStatus =
  quantitativeEnvelopeStatus
    true
    true
    true
    false
    false
    false
    false
    false

crossModelNumericalSeparationStillOpen :
  crossModelNumericalSeparationLocked canonicalQuantitativeEnvelopeStatus ≡ false
crossModelNumericalSeparationStillOpen = refl

prospectiveQuantitativeSeparationStillOpen :
  sourceValuesFrozenAsProspectivePrediction canonicalQuantitativeEnvelopeStatus ≡ false
prospectiveQuantitativeSeparationStillOpen = refl

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data QualitativeBandManufacturesExactAmplitude : Set where

data SourceEnvelopeEqualsLockedPrediction : Set where

qualitativeBandCannotManufactureExactAmplitude :
  QualitativeBandManufacturesExactAmplitude → ⊥
qualitativeBandCannotManufactureExactAmplitude ()

sourceEnvelopeDoesNotEqualLockedPrediction :
  SourceEnvelopeEqualsLockedPrediction → ⊥
sourceEnvelopeDoesNotEqualLockedPrediction ()

sourceEnvelopeDoesNotPayDASHIDerivedPrediction :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
sourceEnvelopeDoesNotPayDASHIDerivedPrediction =
  Prediction.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

------------------------------------------------------------------------
-- SI -> GR/quantum prediction-quantity residual.
--
-- Canonical SI has a signed DecimalScale, while the currently unused
-- Prediction.ScaledQuantity surface stores a Nat `decimalExponent` and a
-- separate empirical PhysicalUnit.  No repository owner currently states the
-- sign/conversion convention between those carriers.  We therefore retain the
-- missing weld explicitly rather than manufacture a `ScaledQuantity` value.
------------------------------------------------------------------------

record PredictionQuantityAdapterResidual : Set where
  constructor predictionQuantityAdapterResidual
  field
    canonicalSIQuantityAvailable : Bool
    predictionScaledQuantitySurfaceAvailable : Bool
    signedScaleConventionWelded : Bool
    physicalUnitCarrierWelded : Bool
    adapterScope : String

open PredictionQuantityAdapterResidual public

canonicalPredictionQuantityAdapterResidual : PredictionQuantityAdapterResidual
canonicalPredictionQuantityAdapterResidual =
  predictionQuantityAdapterResidual
    true
    true
    false
    false
    "the 1-30 micrometre interval is typed in DASHI.Physics.Units.SI; conversion into GRQuantumPredictionProtocol.ScaledQuantity remains unpaid until the decimal-exponent sign and PhysicalUnit correspondence are explicitly owned"

signedScaleConventionStillOpen :
  signedScaleConventionWelded canonicalPredictionQuantityAdapterResidual ≡ false
signedScaleConventionStillOpen = refl

physicalUnitWeldStillOpen :
  physicalUnitCarrierWelded canonicalPredictionQuantityAdapterResidual ≡ false
physicalUnitWeldStillOpen = refl

------------------------------------------------------------------------
-- Source coordinates retained explicitly.  Citation imports neither proof nor
-- framework authority through AttributedSourceCore.
------------------------------------------------------------------------

bedroyaDOI : String
bedroyaDOI = "10.1103/1rsq-cv2m"

daoDOI : String
daoDOI = "10.1103/y31p-9g5k"

lawSmithDOI : String
lawSmithDOI = "10.1007/JHEP06(2024)047"
