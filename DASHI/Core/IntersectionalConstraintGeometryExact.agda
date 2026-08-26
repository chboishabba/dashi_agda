module DASHI.Core.IntersectionalConstraintGeometryExact where

------------------------------------------------------------------------
-- PRIMARY CONCEPTUAL SOURCE
--
-- Kimberle Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1241--1299 (1991).
-- DOI: 10.2307/1229039.
--
-- CROSS-POLLINATION
--
-- Reuse DASHI.Core.IntersectionalNonFactorability rather than define another
-- factorisation calculus.  The supplied 2026-08-27 discussion asks for a
-- ceteris-paribus geometry in which a second non-redundant power relation can
-- further restrict an already constrained position.  This file provides a
-- finite schematic witness of that theorem shape.
--
-- IMPORTANT BOUNDARY
--
-- The constructors below name *constraint regimes*, not intrinsic properties
-- or universal empirical rankings of demographic identities.  The theorem is:
--
--   same declared single-axis projection
--   + an additional non-redundant constraint in the joint regime
--   -> different action-relevant outcome / one additional depth step.
--
-- Any application to concrete populations requires its own evidence that the
-- stated constraints are active, comparable, held-fixed, and non-redundant.
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

-- Even arbitrary recharting of the single sexuality-axis label cannot repair
-- the missing joint relation.
rechartedSexualityAxisCannotRecoverJointConstraint :
  ∀ {Chart : Set} →
  (rechart : SexualityAxisObservation → Chart) →
  INF.FactorsThrough (λ state → rechart (sexualityAxis state)) jointConstraint →
  ⊥
rechartedSexualityAxisCannotRecoverJointConstraint rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart canonicalJointConstraintNonFactorability

------------------------------------------------------------------------
-- Observer-refinement statement: adding the joint relation strictly refines
-- the held-fixed marginal observer.
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
-- Explicit finite depth metric for the *declared schematic model only*.
-- The exact result is a successor relation rather than a universal scalar law.
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
-- A tiny affordance witness makes "more constrained" operational rather than
-- merely numeric: an action remains available under the one-relation regime
-- and is blocked under the declared two-relation regime.
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

canonicalIntersectionalConstraintGeometryBoundary :
  IntersectionalConstraintGeometryBoundary
canonicalIntersectionalConstraintGeometryBoundary =
  intersectional-constraint-geometry-boundary
    false refl
    false refl
    false refl
    false refl
