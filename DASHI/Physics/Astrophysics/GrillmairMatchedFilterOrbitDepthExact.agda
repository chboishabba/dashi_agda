module DASHI.Physics.Astrophysics.GrillmairMatchedFilterOrbitDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Carl J. Grillmair, At a Crossroads: Stellar Streams in the South Galactic Cap,
-- ApJ 847:119 (2017), DOI 10.3847/1538-4357/aa8872.

data StreamAnalysisStage : Set where
  colourMagnitudeFilter
  foregroundModel
  distanceModulusScan
  skyProjection
  streamTrackFit
  orbitFit
  progenitorTest
  kinematicConfirmation
  : StreamAnalysisStage

record MatchedFilterPipeline : Set where
  constructor matched-filter-pipeline
  field
    signalPopulation : String
    foregroundPopulation : String
    colourCombination : String
    distanceSampling : String
    projectionSensitivity : String
    reddeningControl : String
    sourceReference : String

open MatchedFilterPipeline public

canonicalMatchedFilter : MatchedFilterPipeline
canonicalMatchedFilter = matched-filter-pipeline
  "old metal-poor population; NGC 5053 locus used as matched-filter basis"
  "foreground sampled over about half the south Galactic cap while excluding known major substructures/clusters"
  "signal/foreground probabilities computed per colour, multiplied, then summed by sky position"
  "filters shifted in 0.1 mag intervals over distance equivalents from 1 to 100 kpc"
  "tenuous features can strengthen or fade under different map projections"
  "dereddening applied; no corresponding E(B-V) structures matching stream tracks"
  "Grillmair 2017 Sec. II and Figs. 1-3"

record DetectionSensitivity : Set where
  constructor detection-sensitivity
  field
    distanceMismatchThreshold : String
    effect : String
    sourceReference : String

open DetectionSensitivity public

plusMinusPointThreeMag : DetectionSensitivity
plusMinusPointThreeMag = detection-sensitivity
  "more than about +/-0.3 mag away from the correct distance modulus"
  "streams largely fade from detectability"
  "Grillmair 2017"

record OrbitInference : Set where
  constructor orbit-inference
  field
    geometricTrack : String
    adoptedGalacticModel : String
    inferredUnknowns : String
    confirmationChannels : String
    sourceReference : String

open OrbitInference public

canonicalOrbitInference : OrbitInference
canonicalOrbitInference = orbit-inference
  "polynomial/sky track plus estimated distance"
  "adopted Galactic potential/model used for orbit integration"
  "radial velocity, proper motions, peri/apogalacticon, inclination and orbit pole"
  "radial velocity and proper motion measurements; Gaia-style astrometry"
  "Grillmair 2017 Table 1 and conclusions"

record GrillmairDepthBoundary : Set where
  constructor grillmair-depth-boundary
  field
    matchedFilterPeakIsConfirmedStream : Bool
    matchedFilterPeakIsConfirmedStreamIsFalse : matchedFilterPeakIsConfirmedStream ≡ false
    oneProjectionPreservesDetectability : Bool
    oneProjectionPreservesDetectabilityIsFalse : oneProjectionPreservesDetectability ≡ false
    fittedOrbitProvesProgenitorAssociation : Bool
    fittedOrbitProvesProgenitorAssociationIsFalse : fittedOrbitProvesProgenitorAssociation ≡ false
    properMotionOrRadialVelocityCanConfirmCandidate : Bool
    properMotionOrRadialVelocityCanConfirmCandidateIsTrue : properMotionOrRadialVelocityCanConfirmCandidate ≡ true

canonicalGrillmairDepthBoundary : GrillmairDepthBoundary
canonicalGrillmairDepthBoundary = grillmair-depth-boundary false refl false refl false refl true refl

data GrillmairReverseTarget : Set where
  acquireCMDTemplate
  acquireForegroundEstimate
  acquireDistanceModulus
  acquireProjectionChoice
  acquireReddeningModel
  acquireTrackFit
  acquireGalacticPotential
  acquireRadialVelocity
  acquireProperMotion
  acquireProgenitorKinematics
  : GrillmairReverseTarget
