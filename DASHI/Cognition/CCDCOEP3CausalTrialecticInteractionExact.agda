module DASHI.Cognition.CCDCOEP3CausalTrialecticInteractionExact where

------------------------------------------------------------------------
-- CCDCOE P3: TWO-AXIS NON-ADDITIVITY, TRIALECTIC HISTORY AND CAUSAL
-- IDENTIFICATION. Finite witness mathematics; NO empirical attribution.
--
-- This module reuses existing repository-wide NonFactorability, S3 and
-- DiscriminatorSynthesis owners. In particular, the six permutations are
-- NOT a new S3 group, and additive arithmetic is never claimed false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)

import Base369
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Cognition.CCDCOEP3TypedIntersectionalAxisExact as Axis
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Trialectic
import DASHI.Reasoning.TrialecticThreeStrandBraidHistoryExact as Braid

------------------------------------------------------------------------
-- INTERSECTIONAL OWNERSHIP: heterogeneous typed axes, NOT a scalar trick.
--
-- Reuse CCDCOEP3TypedIntersectionalAxisExact, which directly consumes the
-- original IntersectionalBinaryInteractionBridgeExact,
-- BinaryInteractionNonseparabilityExact, IntersectionalConstraintGeometryExact,
-- and IntersectionalNonFactorability owners. Neither an equal point count
-- nor a reweighted aggregate identifies race- and sex-axis positions.
------------------------------------------------------------------------

typedRaceSexAxesDistinct :
  Axis.raceAxis ≡ Axis.sexAxis → ⊥
typedRaceSexAxesDistinct = Axis.axisTagsDiffer

typedInteractionHasNoEndpointAdditiveReconstruction :
  Interaction.NonseparableAdditiveInteraction Axis.typedJointSurface
typedInteractionHasNoEndpointAdditiveReconstruction =
  Axis.typedJointNotAdditivelySeparable

sameTypedCoordinatesDoNotDetermineSituatedRecognition :
  NF.FactorsThrough Axis.coordinatesOnly Axis.recognition → ⊥
sameTypedCoordinatesDoNotDetermineSituatedRecognition =
  Axis.jointPositionsStillDoNotRecoverContextualOutcome

------------------------------------------------------------------------
-- The SIX S3 reorientations are owned by existing ternary group modules.
-- Reorientation != arbitrary rearrangement of a historical intervention.
------------------------------------------------------------------------

canonicalSixReorientations : List Perm.TriPermutation
canonicalSixReorientations =
  Perm.permIdentity ∷
  Perm.permRotate ∷
  Perm.permRotate2 ∷
  Perm.permSwapLowMid ∷
  Perm.permSwapLowHigh ∷
  Perm.permSwapMidHigh ∷
  []

sixReorientationsReversible :
  (p : Perm.TriPermutation) →
  (x : Base369.TriTruth) →
  Perm.applyPermutation (Perm.inversePermutation p)
    (Perm.applyPermutation p x) ≡ x
sixReorientationsReversible = Perm.inverseLeftAt

orderOfS3OperationsMatters :
  S3._∙_ Perm.permRotate Perm.permSwapLowMid
  ≡ S3._∙_ Perm.permSwapLowMid Perm.permRotate → ⊥
orderOfS3OperationsMatters = S3.nonCommutativeWitness

sameAttachedFaceDoesNotSpecifyHistoricalRoute :
  Descent.FactorsThrough Braid.faceOf Braid.routeOf → ⊥
sameAttachedFaceDoesNotSpecifyHistoricalRoute =
  Braid.braidRouteDoesNotFactorThroughAttachedFace

sameThreeEdgesDoNotDetermineTriadicFace :
  NF.FactorsThrough
    Trialectic.boundaryObserver Trialectic.faceConsumer → ⊥
sameThreeEdgesDoNotDetermineTriadicFace =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      Trialectic.sameEdgesReciprocal
      Trialectic.sameEdgesCoercive
      refl
      (λ ()))

------------------------------------------------------------------------
-- Exact finite observationally equivalent causal-world counterexample.
-- Direct:  X := U; Y := X.
-- Common:  X := U; Y := U.
-- Observing the natural X=U history produces the same complete two-point
-- distribution. Intervening to set X=1 at U=0 distinguishes the worlds.
------------------------------------------------------------------------

data Bit : Set where
  zeroBit oneBit : Bit

data CausalWorld : Set where
  directEffect commonCause : CausalWorld

observedExposure : Bit → Bit
observedExposure background = background

responseToExposure : CausalWorld → Bit → Bit → Bit
responseToExposure directEffect _ exposure = exposure
responseToExposure commonCause background _ = background

naturalOutcome : CausalWorld → Bit → Bit
naturalOutcome world background =
  responseToExposure world background (observedExposure background)

record ObservedPair : Set where
  constructor observedPair
  field
    atZero atOne : Bit

observedPairFor : CausalWorld → ObservedPair
observedPairFor world =
  observedPair (naturalOutcome world zeroBit)
               (naturalOutcome world oneBit)

observedDistributionsIdentical :
  observedPairFor directEffect ≡ observedPairFor commonCause
observedDistributionsIdentical = refl

-- Explicit intervention do(X=1), holding the background U=0 fixed.
interventionalProbe : CausalWorld → Bit
interventionalProbe world =
  responseToExposure world zeroBit oneBit

interventionalResultsDiffer :
  interventionalProbe directEffect ≡
  interventionalProbe commonCause → ⊥
interventionalResultsDiffer ()

observationalAssociationDoesNotIdentifyCausation :
  NF.FactorsThrough observedPairFor interventionalProbe → ⊥
observationalAssociationDoesNotIdentifyCausation =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      directEffect commonCause
      observedDistributionsIdentical
      interventionalResultsDiffer)

-- Use actual pre-existing costed experiment/discriminator owner.
counterfactualDistinguishingProbe :
  Discriminator.ExperimentBundle CausalWorld
counterfactualDistinguishingProbe =
  Discriminator.experimentBundle
    Bit
    interventionalProbe
    1
    "Synthetic do(X=1) at fixed U=0, separating two finite SCMs"
    "Exact finite definition; not a permitted or executed real-world study"

counterfactualProbeSeparates :
  Discriminator.BundleSeparates
    counterfactualDistinguishingProbe
    directEffect commonCause
counterfactualProbeSeparates =
  Discriminator.bundleSeparates interventionalResultsDiffer

counterfactualLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension observedPairFor
counterfactualLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      directEffect commonCause observedDistributionsIdentical)
    counterfactualDistinguishingProbe
    counterfactualProbeSeparates

------------------------------------------------------------------------
-- Even when an effect is identified, purpose is a DIFFERENT consumer.
-- Two possible originating purposes share the same effect observation.
------------------------------------------------------------------------

data PurposeWorld : Set where
  voluntaryInfluence : PurposeWorld
  hostileInterference : PurposeWorld

data Purpose : Set where
  nonHostilePurpose : Purpose
  hostilePurpose : Purpose

observedEffect : PurposeWorld → Bit
observedEffect _ = oneBit

worldPurpose : PurposeWorld → Purpose
worldPurpose voluntaryInfluence = nonHostilePurpose
worldPurpose hostileInterference = hostilePurpose

purposeDiffers :
  worldPurpose voluntaryInfluence ≡
  worldPurpose hostileInterference → ⊥
purposeDiffers ()

effectCannotIdentifyHostilePurpose :
  NF.FactorsThrough observedEffect worldPurpose → ⊥
effectCannotIdentifyHostilePurpose =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      voluntaryInfluence hostileInterference refl purposeDiffers)

------------------------------------------------------------------------
-- A socially coherent presentation is not automatically evidence-responsive.
-- Hold the declared public agreement fixed while revisability changes.
------------------------------------------------------------------------

data Agreement : Set where
  sharedNarrative : Agreement

data Revisability : Set where
  contestable : Revisability
  selfSealed : Revisability

data EpistemicWorld : Set where
  coherentAndContestable : EpistemicWorld
  coherentButSelfSealed : EpistemicWorld

publicCoherence : EpistemicWorld → Agreement
publicCoherence _ = sharedNarrative

evidenceRevision : EpistemicWorld → Revisability
evidenceRevision coherentAndContestable = contestable
evidenceRevision coherentButSelfSealed = selfSealed

revisabilityDiffers :
  evidenceRevision coherentAndContestable ≡
  evidenceRevision coherentButSelfSealed → ⊥
revisabilityDiffers ()

narrativeCoherenceDoesNotDetermineRevisability :
  NF.FactorsThrough publicCoherence evidenceRevision → ⊥
narrativeCoherenceDoesNotDetermineRevisability =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      coherentAndContestable coherentButSelfSealed
      refl revisabilityDiffers)

-- If a legitimate observer can measure revision responses rather than
-- only their public narrative label, it separates this finite collision.
-- A real study must independently validate response scoring and consent.
revisabilityDistinguishingProbe :
  Discriminator.ExperimentBundle EpistemicWorld
revisabilityDistinguishingProbe =
  Discriminator.experimentBundle
    Revisability
    evidenceRevision
    1
    "Finite evidence-response probe rather than narrative-agreement label"
    "Toy observation only; no human data or validated predictor"

revisionProbeSeparates :
  Discriminator.BundleSeparates
    revisabilityDistinguishingProbe
    coherentAndContestable coherentButSelfSealed
revisionProbeSeparates =
  Discriminator.bundleSeparates revisabilityDiffers

revisionLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension publicCoherence
revisionLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      coherentAndContestable coherentButSelfSealed refl)
    revisabilityDistinguishingProbe
    revisionProbeSeparates
