module DASHI.ComputerScience.RSA260C3OrbitReducerHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.ComputerScience.RSA260InferredCandidateReducerHyperfabricExact as PairPrior
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources
import DASHI.ComputerScience.RSA260369DNA27CodecNDimTetrationCrossPollinationExact as Triadic
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster3B

------------------------------------------------------------------------
-- C3 STRUCTURED ORBIT REDUCER HYPERFABRIC
--
-- Extends inferred candidate discovery beyond size-two refinement classes.
-- Stable classes of size three generate candidate cyclic actions in both
-- orientations.  Candidate identity still does not imply automorphism:
-- operator-derived co-requirement closure and final MP = PM remain mandatory.
------------------------------------------------------------------------

monster3BRepresentationPrimary : Source.AttributedSource
monster3BRepresentationPrimary =
  Source.mkDOISource
    "R. W. Barraclough; R. A. Wilson"
    "The Character Table of a Maximal Subgroup of the Monster"
    "LMS Journal of Computation and Mathematics 10, 161-175"
    "2007"
    "10.1112/S1461157000001352"
    "https://doi.org/10.1112/S1461157000001352"
    Source.academicArticleSource
    "primary representation-theory source coordinate for the existing Monster 3B phase lane; used here only as a model for structured C3 action search, not as an RSA theorem"
    Source.publicAttribution

record C3SourceCoordinates : Set where
  constructor c3-source-coordinates
  field
    representationSource : Source.AttributedSource
    cyclicGroupQID : Sources.IdentifierApplicability
    c3OrbitOEIS : Sources.IdentifierApplicability
    qidCreatesActionValidity : Bool
    oeisCreatesActionValidity : Bool
open C3SourceCoordinates public

currentC3SourceCoordinates : C3SourceCoordinates
currentC3SourceCoordinates = c3-source-coordinates
  monster3BRepresentationPrimary
  Sources.identifierUnresolved
  Sources.identifierNotApplicable
  false false

record C3OrbitRuntimeSource : Set where
  constructor c3-orbit-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
open C3OrbitRuntimeSource public

currentC3OrbitRuntimeSource : C3OrbitRuntimeSource
currentC3OrbitRuntimeSource = c3-orbit-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_c3_orbit_reducer_hyperfabric_256_oracle.c"
  "d31f9cc5ea4cd61d3244a443607c98c2c5c24761"
  "6d44671d177d5b0af331d4a9f9cd5724815f8069"
  "gcc (Debian 14.2.0-19) 14.2.0"

record C3OrbitReducerExecutionReceipt : Set where
  constructor c3-orbit-reducer-execution-receipt
  field
    carrierCoordinates : Nat
    activeC3Coordinates : Nat
    explicitResidualTailCoordinates : Nat
    stableRefinementClassCount : Nat
    inferredC3CandidateCount : Nat
    nonC3ResidualClassCount : Nat
    refinementRounds : Nat
    individuallyCommutingC3Candidates : Nat
    inferredCoRequirementEdges : Nat
    inferredRequirementComponents : Nat
    smallestRequirementComponent : Nat
    largestRequirementComponent : Nat
    inferredConsumerConflictEdges : Nat
    admissibleClosedBatches : Nat
    selectedClosedComponents : Nat
    selectedC3Orbits : Nat
    quotientCoordinates : Nat
    forwardC3OrientationCommutes : Bool
    inverseC3OrientationCommutes : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
open C3OrbitReducerExecutionReceipt public

currentC3OrbitReducerExecutionReceipt : C3OrbitReducerExecutionReceipt
currentC3OrbitReducerExecutionReceipt = c3-orbit-reducer-execution-receipt
  256
  252
  4
  85
  84
  1
  14
  0
  77
  7
  9
  15
  5
  36
  3
  42
  172
  true
  true
  true
  false

------------------------------------------------------------------------
-- Bidi / cross-pollination boundaries.
------------------------------------------------------------------------

record StructuredOrbitPromotionBoundary : Set where
  constructor structured-orbit-promotion-boundary
  field
    pairOnlyCandidateDiscoveryRemoved : Bool
    sizeThreeClassesGenerateCyclicCandidates : Bool
    bothC3OrientationsChecked : Bool
    fourCoordinateTailRetainedWithoutCoercion : Bool
    coRequirementClosureStillRequired : Bool
    consumerConflictSelectionStillRequired : Bool
    globalMPEqualsPMStillRequired : Bool
    c3CardinalityImpliesMonsterRepresentation : Bool
    monster3BSourceImpliesRSAAction : Bool
open StructuredOrbitPromotionBoundary public

canonicalStructuredOrbitPromotionBoundary : StructuredOrbitPromotionBoundary
canonicalStructuredOrbitPromotionBoundary = structured-orbit-promotion-boundary
  true true true true true true true false false

pairPriorBoundary : PairPrior.CandidateInferencePromotionBoundary
pairPriorBoundary = PairPrior.canonicalCandidateInferencePromotionBoundary

snowballBoundary : Sources.SnowballAttributionBoundary
snowballBoundary = Sources.canonicalSnowballAttributionBoundary

triadicManifestBoundary : Triadic.ArtifactManifestBoundary
triadicManifestBoundary = Triadic.currentArtifactManifestBoundary

monsterPhaseBoundary : Monster3B.PhaseTransportBoundary
monsterPhaseBoundary = Monster3B.canonicalPhaseTransportBoundary

------------------------------------------------------------------------
-- Next structured-action residuals.
------------------------------------------------------------------------

data StructuredOrbitResidual : Set where
  inferActionOrderInsteadOfMatchingOnlyClassSize : StructuredOrbitResidual
  inferOrientationFromOperatorInsteadOfTryingBoth : StructuredOrbitResidual
  generaliseToCyclicAndDihedralGenerators : StructuredOrbitResidual
  inferProductionObserver : StructuredOrbitResidual
  inferProductionLift : StructuredOrbitResidual
  runOnProductionMatrix : StructuredOrbitResidual

firstStructuredOrbitResidual : StructuredOrbitResidual
firstStructuredOrbitResidual = inferActionOrderInsteadOfMatchingOnlyClassSize

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SizeThreeClassImpliesC3Automorphism : Set where
data TernaryCarrierImpliesZ3Operator : Set where
data MonsterC3ImpliesRSAC3 : Set where
data DOIImpliesStructuredReducerValidity : Set where
data FourCoordinateTailMayBeDiscarded : Set where

sizeThreeClassDoesNotCreateC3Automorphism : SizeThreeClassImpliesC3Automorphism → ⊥
sizeThreeClassDoesNotCreateC3Automorphism ()

ternaryCarrierDoesNotRetypeOperator : TernaryCarrierImpliesZ3Operator → ⊥
ternaryCarrierDoesNotRetypeOperator ()

monsterC3DoesNotCreateRSAC3 : MonsterC3ImpliesRSAC3 → ⊥
monsterC3DoesNotCreateRSAC3 ()

doiDoesNotCreateStructuredReducerValidity : DOIImpliesStructuredReducerValidity → ⊥
doiDoesNotCreateStructuredReducerValidity ()

tailCannotBeDiscardedByCardinalityPreference : FourCoordinateTailMayBeDiscarded → ⊥
tailCannotBeDiscardedByCardinalityPreference ()
