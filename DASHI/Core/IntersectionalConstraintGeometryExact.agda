module DASHI.Core.IntersectionalConstraintGeometryExact where

------------------------------------------------------------------------
-- PRIMARY CONCEPTUAL SOURCES
--
-- Kimberle Crenshaw,
-- "Demarginalizing the Intersection of Race and Sex: A Black Feminist
-- Critique of Antidiscrimination Doctrine, Feminist Theory and Antiracist
-- Politics", University of Chicago Legal Forum 1989(1), Article 8.
-- Stable original journal record; no DOI is asserted here.
--
-- Kimberle Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1241--1299 (1991).
-- DOI: 10.2307/1229039.
--
-- SOURCE SCOPE
--
-- The 1989 paper is the direct conceptual source for the warning that an
-- intersectional experience is not adequately reconstructed by summing
-- independently modelled single-axis experiences.  The 1991 paper supplies the
-- structural/political/representational intersectionality context.
--
-- CROSS-POLLINATION
--
-- Reuse DASHI.Core.IntersectionalNonFactorability rather than define another
-- factorisation calculus.  The supplied 2026-08-27 discussion asks for a
-- ceteris-paribus geometry in which a second non-redundant power relation can
-- further restrict an already constrained position, with genuinely nonlinear
-- interaction allowed.
--
-- IMPORTANT BOUNDARY
--
-- The constructors below name *constraint regimes*, not intrinsic properties
-- or universal empirical rankings of demographic identities.  Any application
-- to concrete populations requires separate evidence that the stated
-- constraints are active, comparable, held-fixed, and non-redundant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Two held-fixed schematic regimes.
------------------------------------------------------------------------

data ConstraintRegime : Set where
  heteronormativeOnly : ConstraintRegime
  heteronormativePlusPatriarchal : ConstraintRegime

-- The comparison deliberately holds the declared sexuality-axis observation
-- fixed.  It therefore cannot by itself see the additional gendered relation.
data SexualityAxisObservation : Set where
  nonHeteronormativePosition : SexualityAxisObservation

sexualityAxis : ConstraintRegime → SexualityAxisObservation
sexualityAxis heteronormativeOnly = nonHeteronormativePosition
sexualityAxis heteronormativePlusPatriarchal = nonHeteronormativePosition

sameSexualityAxisObservation :
  sexualityAxis heteronormativeOnly
  ≡ sexualityAxis heteronormativePlusPatriarchal
sameSexualityAxisObservation = refl

------------------------------------------------------------------------
-- Joint relational state.
------------------------------------------------------------------------

data JointConstraintState : Set where
  oneActiveRelation : JointConstraintState
  twoActiveNonredundantRelations : JointConstraintState

jointConstraint : ConstraintRegime → JointConstraintState
jointConstraint heteronormativeOnly = oneActiveRelation
jointConstraint heteronormativePlusPatriarchal =
  twoActiveNonredundantRelations

jointConstraintDiffers :
  jointConstraint heteronormativeOnly
  ≡ jointConstraint heteronormativePlusPatriarchal → ⊥
jointConstraintDiffers ()

canonicalJointConstraintNonFactorability :
  INF.NonFactorabilityWitness sexualityAxis jointConstraint
canonicalJointConstraintNonFactorability =
  INF.nonFactorabilityWitness
    heteronormativeOnly
    heteronormativePlusPatriarchal
    refl
    jointConstraintDiffers

sexualityAxisCannotRecoverJointConstraint :
  INF.FactorsThrough sexualityAxis jointConstraint → ⊥
sexualityAxisCannotRecoverJointConstraint =
  INF.witnessRulesOutEveryFlatFactorisation
    canonicalJointConstraintNonFactorability

rechartedSexualityAxisCannotRecoverJointConstraint :
  ∀ {Chart : Set} →
  (rechart : SexualityAxisObservation → Chart) →
  INF.FactorsThrough (λ state → rechart (sexualityAxis state)) jointConstraint →
  ⊥
rechartedSexualityAxisCannotRecoverJointConstraint rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart canonicalJointConstraintNonFactorability

------------------------------------------------------------------------
-- Observer-refinement statement.
------------------------------------------------------------------------

sexualityPlusJointStrictlyRefinesSexuality :
  Observer.StrictRefinement
    sexualityAxis
    (Observer.pairObserver sexualityAxis jointConstraint)
sexualityPlusJointStrictlyRefinesSexuality =
  Observer.strictPairRefinement
    sexualityAxis
    jointConstraint
    heteronormativeOnly
    heteronormativePlusPatriarchal
    refl
    jointConstraintDiffers

------------------------------------------------------------------------
-- A small declared depth coordinate remains available as one schematic view,
-- but it is NOT the primary semantics of intersectionality.
------------------------------------------------------------------------

constraintDepth : ConstraintRegime → Nat
constraintDepth heteronormativeOnly = 1
constraintDepth heteronormativePlusPatriarchal = 2

singleAxisConstraintDepthIsOne :
  constraintDepth heteronormativeOnly ≡ 1
singleAxisConstraintDepthIsOne = refl

jointConstraintDepthIsTwo :
  constraintDepth heteronormativePlusPatriarchal ≡ 2
jointConstraintDepthIsTwo = refl

jointConstraintAddsOneDepthStep :
  constraintDepth heteronormativePlusPatriarchal
  ≡ suc (constraintDepth heteronormativeOnly)
jointConstraintAddsOneDepthStep = refl

------------------------------------------------------------------------
-- Operational affordance witness.
------------------------------------------------------------------------

data Affordance : Set where
  publicRecognition : Affordance
  privateRelation : Affordance

available : ConstraintRegime → Affordance → Bool
available heteronormativeOnly publicRecognition = true
available heteronormativeOnly privateRelation = true
available heteronormativePlusPatriarchal publicRecognition = false
available heteronormativePlusPatriarchal privateRelation = true

publicRecognitionDiffers :
  available heteronormativeOnly publicRecognition
  ≡ available heteronormativePlusPatriarchal publicRecognition → ⊥
publicRecognitionDiffers ()

privateRelationHeldFixed :
  available heteronormativeOnly privateRelation
  ≡ available heteronormativePlusPatriarchal privateRelation
privateRelationHeldFixed = refl

------------------------------------------------------------------------
-- Nonlinear interaction witness.
--
-- Each marginal relation alone leaves `publicRecognition` open in this finite
-- specimen, while their joint configuration closes it.  Therefore the joint
-- affordance is not reconstructed by simply conjoining independently evaluated
-- marginal affordances.  This is a finite theorem shape for interaction, not an
-- empirical law about any demographic group.
------------------------------------------------------------------------

data AxisConfiguration : Set where
  neitherAxis heteronormativeAxis patriarchalAxis jointAxes : AxisConfiguration

heteronormativeMarginal : AxisConfiguration → Bool
heteronormativeMarginal neitherAxis = false
heteronormativeMarginal heteronormativeAxis = true
heteronormativeMarginal patriarchalAxis = false
heteronormativeMarginal jointAxes = true

patriarchalMarginal : AxisConfiguration → Bool
patriarchalMarginal neitherAxis = false
patriarchalMarginal heteronormativeAxis = false
patriarchalMarginal patriarchalAxis = true
patriarchalMarginal jointAxes = true

_and_ : Bool → Bool → Bool
true and true = true
true and false = false
false and true = false
false and false = false

-- Marginal-only model: each individual axis, considered in isolation, leaves
-- the selected affordance open; conjunction therefore predicts it remains open.
marginalPublicRecognition : AxisConfiguration → Bool
marginalPublicRecognition neitherAxis = true
marginalPublicRecognition heteronormativeAxis = true
marginalPublicRecognition patriarchalAxis = true
marginalPublicRecognition jointAxes =
  marginalPublicRecognition heteronormativeAxis
  and marginalPublicRecognition patriarchalAxis

-- Actual finite joint-response specimen with an interaction term.
interactionPublicRecognition : AxisConfiguration → Bool
interactionPublicRecognition neitherAxis = true
interactionPublicRecognition heteronormativeAxis = true
interactionPublicRecognition patriarchalAxis = true
interactionPublicRecognition jointAxes = false

marginalModelPredictsJointOpen :
  marginalPublicRecognition jointAxes ≡ true
marginalModelPredictsJointOpen = refl

interactionModelMakesJointClosed :
  interactionPublicRecognition jointAxes ≡ false
interactionModelMakesJointClosed = refl

jointInteractionIsNotRecoveredByMarginalConjunction :
  marginalPublicRecognition jointAxes
  ≡ interactionPublicRecognition jointAxes → ⊥
jointInteractionIsNotRecoveredByMarginalConjunction ()

-- The two models agree on every single-axis configuration, isolating the
-- difference to the declared interaction itself.
heteronormativeSingleAxisHeldFixed :
  marginalPublicRecognition heteronormativeAxis
  ≡ interactionPublicRecognition heteronormativeAxis
heteronormativeSingleAxisHeldFixed = refl

patriarchalSingleAxisHeldFixed :
  marginalPublicRecognition patriarchalAxis
  ≡ interactionPublicRecognition patriarchalAxis
patriarchalSingleAxisHeldFixed = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record IntersectionalConstraintGeometryBoundary : Set where
  constructor intersectional-constraint-geometry-boundary
  field
    identityHasIntrinsicConstraintNumber : Bool
    identityHasIntrinsicConstraintNumberIsFalse :
      identityHasIntrinsicConstraintNumber ≡ false
    specimenIsUniversalPopulationOrdering : Bool
    specimenIsUniversalPopulationOrderingIsFalse :
      specimenIsUniversalPopulationOrdering ≡ false
    separateAxesAutomaticallyDetermineJointOutcome : Bool
    separateAxesAutomaticallyDetermineJointOutcomeIsFalse :
      separateAxesAutomaticallyDetermineJointOutcome ≡ false
    rechartingCollapsedAxisRecoversJointRelation : Bool
    rechartingCollapsedAxisRecoversJointRelationIsFalse :
      rechartingCollapsedAxisRecoversJointRelation ≡ false
    scalarDepthIsPrimaryIntersectionalSemantics : Bool
    scalarDepthIsPrimaryIntersectionalSemanticsIsFalse :
      scalarDepthIsPrimaryIntersectionalSemantics ≡ false
    jointAffordanceMustEqualMarginalConjunction : Bool
    jointAffordanceMustEqualMarginalConjunctionIsFalse :
      jointAffordanceMustEqualMarginalConjunction ≡ false

canonicalIntersectionalConstraintGeometryBoundary :
  IntersectionalConstraintGeometryBoundary
canonicalIntersectionalConstraintGeometryBoundary =
  intersectional-constraint-geometry-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
