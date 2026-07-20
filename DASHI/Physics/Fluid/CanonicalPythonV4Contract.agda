module DASHI.Physics.Fluid.CanonicalPythonV4Contract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.Fluid.BandedVorticitySpinTwist using
  (SolverMode; fastMode; vortexFaithfulMode)
open import DASHI.Physics.Fluid.BandedVorticityCrossPollination using
  (CrossPollinationClaim; finiteSupportSignClaim; finiteMirrorSymmetryClaim;
   hierarchicalAddressClaim; candidateWorldTubeClaim; mdlSelectionReceiptClaim)

------------------------------------------------------------------------
-- Exact audit surface for the canonical Python v4 path in dashiCFD.
--
-- This module records what the current implementation actually carries and
-- what remains absent.  It does not infer a numerical theorem from names,
-- plots, or comments in the Python source.


data Never : Set where

data PythonV4Feature : Set where
  periodicFFTGeometry : PythonV4Feature
  retainedLowComplexModes : PythonV4Feature
  retainedTopKMidComplexModes : PythonV4Feature
  residualBandEnergySummaries : PythonV4Feature
  ternarySupportSignMask : PythonV4Feature
  deterministicFrameSeed : PythonV4Feature
  optionalGaussianAtomSplat : PythonV4Feature

  periodicSmoothing : PythonV4Feature
  hermitianResidualSynthesis : PythonV4Feature
  normalizedCirculationRasterizer : PythonV4Feature
  canonicalAtomExtraction : PythonV4Feature
  canonicalAtomTransport : PythonV4Feature
  substantiveTemporalAssociation : PythonV4Feature
  heldOutEvaluation : PythonV4Feature
  applicationAdequacyReceipt : PythonV4Feature

canonicalPythonV4Features : List PythonV4Feature
canonicalPythonV4Features =
  periodicFFTGeometry
  ∷ retainedLowComplexModes
  ∷ retainedTopKMidComplexModes
  ∷ residualBandEnergySummaries
  ∷ ternarySupportSignMask
  ∷ deterministicFrameSeed
  ∷ optionalGaussianAtomSplat
  ∷ periodicSmoothing
  ∷ hermitianResidualSynthesis
  ∷ normalizedCirculationRasterizer
  ∷ canonicalAtomExtraction
  ∷ canonicalAtomTransport
  ∷ substantiveTemporalAssociation
  ∷ heldOutEvaluation
  ∷ applicationAdequacyReceipt
  ∷ []

FeatureImplemented : PythonV4Feature → Set
FeatureImplemented periodicFFTGeometry = ⊤
FeatureImplemented retainedLowComplexModes = ⊤
FeatureImplemented retainedTopKMidComplexModes = ⊤
FeatureImplemented residualBandEnergySummaries = ⊤
FeatureImplemented ternarySupportSignMask = ⊤
FeatureImplemented deterministicFrameSeed = ⊤
FeatureImplemented optionalGaussianAtomSplat = ⊤

FeatureImplemented periodicSmoothing = Never
FeatureImplemented hermitianResidualSynthesis = Never
FeatureImplemented normalizedCirculationRasterizer = Never
FeatureImplemented canonicalAtomExtraction = Never
FeatureImplemented canonicalAtomTransport = Never
FeatureImplemented substantiveTemporalAssociation = Never
FeatureImplemented heldOutEvaluation = Never
FeatureImplemented applicationAdequacyReceipt = Never

periodicFFTGeometryImplemented : FeatureImplemented periodicFFTGeometry
periodicFFTGeometryImplemented = tt

retainedTopKMidComplexModesImplemented :
  FeatureImplemented retainedTopKMidComplexModes
retainedTopKMidComplexModesImplemented = tt

periodicSmoothingNotYetImplemented :
  FeatureImplemented periodicSmoothing → Never
periodicSmoothingNotYetImplemented impossible = impossible

canonicalAtomExtractionNotYetImplemented :
  FeatureImplemented canonicalAtomExtraction → Never
canonicalAtomExtractionNotYetImplemented impossible = impossible

heldOutEvaluationNotYetImplemented :
  FeatureImplemented heldOutEvaluation → Never
heldOutEvaluationNotYetImplemented impossible = impossible

------------------------------------------------------------------------
-- Fast and faithful promotion gates.

record FastNumericalContract : Set where
  constructor fastNumericalContract
  field
    fastPeriodicSmoothing : FeatureImplemented periodicSmoothing
    fastHermitianResidual : FeatureImplemented hermitianResidualSynthesis
    fastHeldOutEvaluation : FeatureImplemented heldOutEvaluation
    fastAdequacyReceipt : FeatureImplemented applicationAdequacyReceipt
open FastNumericalContract public

record FaithfulNumericalContract : Set where
  constructor faithfulNumericalContract
  field
    faithfulFastBase : FastNumericalContract
    faithfulNormalizedCirculation :
      FeatureImplemented normalizedCirculationRasterizer
    faithfulAtomExtraction : FeatureImplemented canonicalAtomExtraction
    faithfulAtomTransport : FeatureImplemented canonicalAtomTransport
    faithfulTemporalAssociation :
      FeatureImplemented substantiveTemporalAssociation
open FaithfulNumericalContract public

FastModePromotable : Set
FastModePromotable = FastNumericalContract

FaithfulModePromotable : Set
FaithfulModePromotable = FaithfulNumericalContract

currentFastModePromotionBlocked : FastModePromotable → Never
currentFastModePromotionBlocked c =
  periodicSmoothingNotYetImplemented (fastPeriodicSmoothing c)

currentFaithfulModePromotionBlocked : FaithfulModePromotable → Never
currentFaithfulModePromotionBlocked c =
  canonicalAtomExtractionNotYetImplemented (faithfulAtomExtraction c)

------------------------------------------------------------------------
-- Distinguish implementation facts from interpretation bridges.

pythonV4CompatibleFiniteClaims : List CrossPollinationClaim
pythonV4CompatibleFiniteClaims =
  finiteSupportSignClaim
  ∷ finiteMirrorSymmetryClaim
  ∷ hierarchicalAddressClaim
  ∷ candidateWorldTubeClaim
  ∷ mdlSelectionReceiptClaim
  ∷ []

data PythonV4Claim : Set where
  implementationCarrierClaim : PythonV4Claim
  aggregateFastDecoderClaim : PythonV4Claim
  coherentVortexDecodeHookClaim : PythonV4Claim
  validatedFastSolverClaim : PythonV4Claim
  validatedFaithfulSolverClaim : PythonV4Claim
  generalizationClaim : PythonV4Claim
  navierStokesClosureClaim : PythonV4Claim

ClaimAvailable : PythonV4Claim → Set
ClaimAvailable implementationCarrierClaim = ⊤
ClaimAvailable aggregateFastDecoderClaim = ⊤
ClaimAvailable coherentVortexDecodeHookClaim = ⊤
ClaimAvailable validatedFastSolverClaim = Never
ClaimAvailable validatedFaithfulSolverClaim = Never
ClaimAvailable generalizationClaim = Never
ClaimAvailable navierStokesClosureClaim = Never

validatedFastSolverRejected :
  ClaimAvailable validatedFastSolverClaim → Never
validatedFastSolverRejected impossible = impossible

validatedFaithfulSolverRejected :
  ClaimAvailable validatedFaithfulSolverClaim → Never
validatedFaithfulSolverRejected impossible = impossible

generalizationRejected : ClaimAvailable generalizationClaim → Never
generalizationRejected impossible = impossible

navierStokesClosureRejected :
  ClaimAvailable navierStokesClosureClaim → Never
navierStokesClosureRejected impossible = impossible

------------------------------------------------------------------------
-- Measurement obligations for the first falsifiable handoff.


data RequiredMetric : Set where
  relativeL2Metric : RequiredMetric
  correlationMetric : RequiredMetric
  spectralBandErrorMetric : RequiredMetric
  energyErrorMetric : RequiredMetric
  enstrophyErrorMetric : RequiredMetric
  supportFractionErrorMetric : RequiredMetric
  temporalCorrelationMetric : RequiredMetric
  corePositionErrorMetric : RequiredMetric
  circulationErrorMetric : RequiredMetric
  trackSurvivalMetric : RequiredMetric
  mergeSplitAccuracyMetric : RequiredMetric
  runtimeMetric : RequiredMetric
  memoryMetric : RequiredMetric
  descriptionLengthMetric : RequiredMetric

requiredFastMetrics : List RequiredMetric
requiredFastMetrics =
  relativeL2Metric
  ∷ correlationMetric
  ∷ spectralBandErrorMetric
  ∷ energyErrorMetric
  ∷ enstrophyErrorMetric
  ∷ supportFractionErrorMetric
  ∷ temporalCorrelationMetric
  ∷ runtimeMetric
  ∷ memoryMetric
  ∷ descriptionLengthMetric
  ∷ []

requiredFaithfulMetrics : List RequiredMetric
requiredFaithfulMetrics =
  corePositionErrorMetric
  ∷ circulationErrorMetric
  ∷ trackSurvivalMetric
  ∷ mergeSplitAccuracyMetric
  ∷ requiredFastMetrics

record NumericalReceipt : Set where
  constructor numericalReceipt
  field
    receiptMode : SolverMode
    receiptTrainingSeed : Nat
    receiptEvaluationSeed : Nat
    receiptUsesHeldOutData : Bool
    receiptPeriodicSmoother : Bool
    receiptHermitianResidual : Bool
    receiptNormalizedCirculation : Bool
    receiptAtomExtraction : Bool
    receiptAtomTransport : Bool
    receiptTemporalAssociation : Bool
    receiptMetrics : List RequiredMetric
    receiptPromoted : Bool
    receiptNote : String
open NumericalReceipt public

canonicalCurrentV4Receipt : NumericalReceipt
canonicalCurrentV4Receipt =
  numericalReceipt
    fastMode
    0
    0
    false
    false
    false
    false
    false
    false
    false
    requiredFastMetrics
    false
    "Canonical v4 has a phase-carrying low/top-K-mid proxy and aggregate residual decoder, but the faithful extraction/transport/evaluation contract is open."

currentReceiptNotPromoted : receiptPromoted canonicalCurrentV4Receipt ≡ false
currentReceiptNotPromoted = refl

canonicalImplementationNotes : List String
canonicalImplementationNotes =
  "top-K mid-band complex coefficients mean the residual is not wholly phase-free"
  ∷ "the remaining mid/high texture is still synthesized from seeded phases"
  ∷ "the current smoother is not periodic even though the PDE grid is periodic"
  ∷ "the Gaussian atom hook is a decoder hook, not an extractor or transport law"
  ∷ "gamma is not yet certified as discrete circulation"
  ∷ "the canonical learned rollout is evaluated on its fitting trajectory"
  ∷ "fast and faithful promotion remain blocked pending measured receipts"
  ∷ "no Navier--Stokes closure or inertial-manifold theorem follows"
  ∷ []
