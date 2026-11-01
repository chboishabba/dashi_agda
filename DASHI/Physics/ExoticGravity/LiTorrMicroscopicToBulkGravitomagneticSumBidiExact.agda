module DASHI.Physics.ExoticGravity.LiTorrMicroscopicToBulkGravitomagneticSumBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LI/TORR MICROSCOPIC -> BULK GRAVITOMAGNETIC SUM
--
-- Source scope: Torr and Li (1993) give a single-ion estimate Bg,ion ~ 1e-37 Hz,
-- then scale to ~1e28 coherently rotating superlattice ions in an arbitrary
-- 0.1 m^3 volume and report a total field of order 1e-9 Hz.
--
-- This owner does not promote that scaling. It makes explicit the conditions
-- under which an N-fold microscopic sum can equal a macroscopic external field.
------------------------------------------------------------------------

record SingleIonEstimate : Set where
  constructor single-ion-estimate
  field
    sourceReference : String
    fieldPerIon : String
    fieldPerIonUnits : String
    observerDistance : String
    ionAngularMomentumModel : String

canonicalSingleIonEstimate : SingleIonEstimate
canonicalSingleIonEstimate = single-ion-estimate
  "Torr and Li 1993, Eq. (3.9)-(3.10) discussion"
  "~1e-37"
  "Hz"
  "paper uses dimensions consistent with laboratory scales"
  "spin angular momentum only"

record BulkEstimate : Set where
  constructor bulk-estimate
  field
    coherentIonCount : String
    coherentVolume : String
    claimedBulkField : String
    claimedBulkFieldUnits : String

canonicalBulkEstimate : BulkEstimate
canonicalBulkEstimate = bulk-estimate
  "~1e28"
  "0.1 m^3 (explicitly described as arbitrary in the source discussion)"
  "~1e-9"
  "Hz"

------------------------------------------------------------------------
-- The algebra 1e28 * 1e-37 = 1e-9 is arithmetically consistent.
-- Physical field addition requires much more than arithmetic.
------------------------------------------------------------------------

record NSumAdmissibility : Set where
  constructor n-sum-admissibility
  field
    commonObservationPoint : Bool
    compatibleSourceDistances : Bool
    vectorOrientationsAligned : Bool
    angularMomentaAligned : Bool
    phaseRelationSpecified : Bool
    sourcePositionsSpecified : Bool
    nearFarFieldRegimeSpecified : Bool
    linearWeakFieldSuperpositionApplicable : Bool

record NSumPromotionBoundary : Set where
  constructor n-sum-promotion-boundary
  field
    arithmeticNMultiplicationSufficientForExternalField : Bool
    arithmeticNMultiplicationSufficientForExternalFieldIsFalse :
      arithmeticNMultiplicationSufficientForExternalField ≡ false

    coherenceAloneFixesGeometryFactors : Bool
    coherenceAloneFixesGeometryFactorsIsFalse :
      coherenceAloneFixesGeometryFactors ≡ false

    coherenceAloneFixesVectorOrientation : Bool
    coherenceAloneFixesVectorOrientationIsFalse :
      coherenceAloneFixesVectorOrientation ≡ false

    bulkFieldRequiresSpatialSourceSumOrIntegral : Bool
    bulkFieldRequiresSpatialSourceSumOrIntegralIsTrue :
      bulkFieldRequiresSpatialSourceSumOrIntegral ≡ true

canonicalNSumPromotionBoundary : NSumPromotionBoundary
canonicalNSumPromotionBoundary =
  n-sum-promotion-boundary false refl false refl false refl true refl

------------------------------------------------------------------------
-- Ordinary weak-field source object.
--
-- The correct bulk object is a source distribution (or discrete sum) carrying
-- mass-current/angular-momentum and source-observer geometry. The individual
-- contributions add linearly only after their full vector/geometric kernels are
-- evaluated.
------------------------------------------------------------------------

record MicroscopicSource : Set where
  constructor microscopic-source
  field
    sourcePosition : String
    observationPoint : String
    angularMomentumVector : String
    distanceKernel : String
    orientationKernel : String

record BulkSourceIntegral : Set where
  constructor bulk-source-integral
  field
    sourceDensity : String
    massCurrentDensity : String
    angularMomentumDensity : String
    greenKernel : String
    bulkFieldExpression : String

canonicalBulkSourceIntegral : BulkSourceIntegral
canonicalBulkSourceIntegral = bulk-source-integral
  "rho(x)"
  "J_m(x)"
  "ell(x)"
  "weak-field gravitomagnetic Green kernel with source-observer geometry"
  "Bg(x_obs) = integral d^3x K(x_obs,x) · J_m/ell source data (up to GEM convention)"

------------------------------------------------------------------------
-- BIDI acquisition router for validating the 1e-9 Hz aggregate estimate.
------------------------------------------------------------------------

data MicroscopicBulkLeaf : Set where
  singleIonFormulaLeaf : MicroscopicBulkLeaf
  ionCountLeaf : MicroscopicBulkLeaf
  sourceDistributionLeaf : MicroscopicBulkLeaf
  angularMomentumAlignmentLeaf : MicroscopicBulkLeaf
  observationGeometryLeaf : MicroscopicBulkLeaf
  vectorSumLeaf : MicroscopicBulkLeaf
  standardGRComparisonLeaf : MicroscopicBulkLeaf
  closedMicroscopicBulkWeld : MicroscopicBulkLeaf

record MicroscopicBulkClosureState : Set where
  constructor microscopic-bulk-closure-state
  field
    singleIonFormulaOwned : Bool
    ionCountOwned : Bool
    sourceDistributionOwned : Bool
    angularMomentumAlignmentOwned : Bool
    observationGeometryOwned : Bool
    vectorSumOwned : Bool
    standardGRComparisonOwned : Bool

firstOpenMicroscopicBulkLeaf : MicroscopicBulkClosureState -> MicroscopicBulkLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state false b c d e f g) = singleIonFormulaLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true false c d e f g) = ionCountLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true true false d e f g) = sourceDistributionLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true true true false e f g) = angularMomentumAlignmentLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true true true true false f g) = observationGeometryLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true true true true true false g) = vectorSumLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true true true true true true false) = standardGRComparisonLeaf
firstOpenMicroscopicBulkLeaf (microscopic-bulk-closure-state true true true true true true true) = closedMicroscopicBulkWeld

currentMicroscopicBulkFrontier : MicroscopicBulkClosureState
currentMicroscopicBulkFrontier =
  microscopic-bulk-closure-state true true false false false false false

currentFirstOpenMicroscopicBulkLeaf : MicroscopicBulkLeaf
currentFirstOpenMicroscopicBulkLeaf =
  firstOpenMicroscopicBulkLeaf currentMicroscopicBulkFrontier
