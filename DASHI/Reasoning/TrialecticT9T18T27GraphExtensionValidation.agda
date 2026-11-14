module DASHI.Reasoning.TrialecticT9T18T27GraphExtensionValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

boundary : Tower.TrialecticT9T18T27GraphExtensionBoundary
boundary = Tower.canonicalTrialecticT9T18T27GraphExtensionBoundary

t9ChunkPaid : Tower.t9ChunkReusesThreeT3Cells boundary ≡ true
t9ChunkPaid = refl

t18RechartPaid : Tower.t18RechartsExistingStructuredBoundary boundary ≡ true
t18RechartPaid = refl

t27AmbientPaid : Tower.t27AmbientIsThreeT9Faces boundary ≡ true
t27AmbientPaid = refl

graphCompletionPaid : Tower.t18GraphCompletesToT27GivenPolicy boundary ≡ true
graphCompletionPaid = refl

graphRoundTripPaid : Tower.completedT27ProjectsExactlyToT18 boundary ≡ true
graphRoundTripPaid = refl

completedT27HasOnlyT18FreeData : Tower.completedT27HasT18FreeData boundary ≡ true
completedT27HasOnlyT18FreeData = refl

noPolicyNoCanonicalThirdFace : Tower.t18AloneDeterminesCanonicalT27 boundary ≡ false
noPolicyNoCanonicalThirdFace = refl

ambientT27NotSameInformationAsCompletedGraph :
  Tower.ambientT27IdentifiedWithCompletedGraphByCardinality boundary ≡ false
ambientT27NotSameInformationAsCompletedGraph = refl

siblingCompletionNotSilentlyImported :
  Tower.siblingDomainCompletionAutomaticallyImported boundary ≡ false
siblingCompletionNotSilentlyImported = refl

canonicalStructuredCoordinates : Cell.StructuredBoundaryCoordinates
canonicalStructuredCoordinates =
  Cell.compatibleBoundaryToCoordinates Cell.canonicalCompatibleThreeCellBoundary

structuredT18RoundTrip :
  Tower.t18ToStructuredBoundaryCoordinates
    (Tower.structuredBoundaryCoordinatesToT18 canonicalStructuredCoordinates)
  ≡ canonicalStructuredCoordinates
structuredT18RoundTrip = refl

firstFacePolicy : Tower.T18Coordinates → Tower.T9Coordinates
firstFacePolicy = Tower.firstNine

canonicalCompletedT27 : Tower.T27Coordinates
canonicalCompletedT27 =
  Tower.completeT27 firstFacePolicy
    (Tower.structuredBoundaryCoordinatesToT18 canonicalStructuredCoordinates)

canonicalCompletedT27SatisfiesGraph :
  Tower.GraphLaw firstFacePolicy canonicalCompletedT27
canonicalCompletedT27SatisfiesGraph = Tower.completeT27SatisfiesGraph

canonicalCompletedProjectsBackToT18 :
  Tower.projectT18 canonicalCompletedT27
  ≡ Tower.structuredBoundaryCoordinatesToT18 canonicalStructuredCoordinates
canonicalCompletedProjectsBackToT18 =
  Tower.projectCompleteT27 firstFacePolicy
    (Tower.structuredBoundaryCoordinatesToT18 canonicalStructuredCoordinates)
