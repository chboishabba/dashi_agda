{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SubstitutedBackgroundFixedPointStabilityRound365Exact where

------------------------------------------------------------------------
-- ROUND365 / FIXED-POINT PERTURBATION COMPILER BENEATH R364 H_subScale
--
-- R364 showed that the marked-walk H_scale route is not mandatory.  Its
-- direct source-native route needs only:
--
--   H_local    : local D²E Lipschitz along the substituted background;
--   H_subScale : substituted-background displacement <= source scale.
--
-- CMP116 (1.13)--(1.21) constructs the substituted background by contractive
-- analytic equations.  This module isolates the generic theorem needed to
-- make H_subScale compiler-owned once the literal CMP116 map is attached:
--
--   same-map contraction
--   + cross-parameter map defect
--   + ordinary fixed-point absorption
--   -> fixed-point displacement bound.
--
-- The carrier is intentionally abstract.  It does NOT identify the older
-- finite-background critical map with the CMP116 substituted-background map.
-- It also does not manufacture the contraction rate, the cross-domain defect,
-- or the ordered-scalar absorption law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record SubstitutedBackgroundFixedPointPerturbationData : Set₁ where
  field
    Parameter State Bound : Set

    map : Parameter → State → State
    fixedPoint : Parameter → State
    fixed : ∀ parameter →
      map parameter (fixedPoint parameter) ≡ fixedPoint parameter

    distance : State → State → Bound
    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    addMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (add a c) (add b d)

    contractionRate stabilityFactor : Bound

    -- Metric triangle inequality in the only shape used below.
    triangle : ∀ x y z →
      LessEqual (distance x z)
        (add (distance x y) (distance y z))

    -- Same CMP116 substitution map, two candidate backgrounds.
    sameMapContraction : ∀ parameter x y →
      LessEqual
        (distance (map parameter x) (map parameter y))
        (scale contractionRate (distance x y))

    -- Same candidate background, two source/domain parameters.
    mapDefect : Parameter → Parameter → Bound
    crossParameterMapDefect : ∀ left right x →
      LessEqual
        (distance (map left x) (map right x))
        (mapDefect left right)

    -- Standard ordered-scalar contraction absorption.  In a concrete normed
    -- real carrier this is the usual q<1 rearrangement, equivalently division
    -- by 1-q.  It is kept separate from YM source content.
    absorbContraction : ∀ {x defect} →
      LessEqual x
        (add (scale contractionRate x) defect) →
      LessEqual x (scale stabilityFactor defect)

open SubstitutedBackgroundFixedPointPerturbationData public

fixedPointDifferenceBeforeAbsorption :
  (dataSet : SubstitutedBackgroundFixedPointPerturbationData) →
  (left right : Parameter dataSet) →
  LessEqual dataSet
    (distance dataSet
      (fixedPoint dataSet left)
      (fixedPoint dataSet right))
    (add dataSet
      (scale dataSet
        (contractionRate dataSet)
        (distance dataSet
          (fixedPoint dataSet left)
          (fixedPoint dataSet right)))
      (mapDefect dataSet left right))
fixedPointDifferenceBeforeAbsorption dataSet left right
  rewrite sym (fixed dataSet left)
        | sym (fixed dataSet right) =
  lessEqualTransitive dataSet
    (triangle dataSet
      (map dataSet left (fixedPoint dataSet left))
      (map dataSet left (fixedPoint dataSet right))
      (map dataSet right (fixedPoint dataSet right)))
    (addMonotone dataSet
      (sameMapContraction dataSet left
        (fixedPoint dataSet left)
        (fixedPoint dataSet right))
      (crossParameterMapDefect dataSet left right
        (fixedPoint dataSet right)))

fixedPointPerturbationStable :
  (dataSet : SubstitutedBackgroundFixedPointPerturbationData) →
  (left right : Parameter dataSet) →
  LessEqual dataSet
    (distance dataSet
      (fixedPoint dataSet left)
      (fixedPoint dataSet right))
    (scale dataSet
      (stabilityFactor dataSet)
      (mapDefect dataSet left right))
fixedPointPerturbationStable dataSet left right =
  absorbContraction dataSet
    (fixedPointDifferenceBeforeAbsorption dataSet left right)

------------------------------------------------------------------------
-- Pareto / same-object boundary.
------------------------------------------------------------------------

record CMP116Round365AttachmentBoundary : Set where
  constructor cmp116-round365-boundary
  field
    literalCMP116MapAttachmentStillRequired : Bool
    literalCMP116MapAttachmentStillRequiredIsTrue :
      literalCMP116MapAttachmentStillRequired ≡ true

    literalCMP116ContractionStillRequired : Bool
    literalCMP116ContractionStillRequiredIsTrue :
      literalCMP116ContractionStillRequired ≡ true

    literalCrossDomainMapDefectStillRequired : Bool
    literalCrossDomainMapDefectStillRequiredIsTrue :
      literalCrossDomainMapDefectStillRequired ≡ true

    fixedPointPerturbationAlgebraCompilerOwned : Bool
    fixedPointPerturbationAlgebraCompilerOwnedIsTrue :
      fixedPointPerturbationAlgebraCompilerOwned ≡ true

    r364SubstitutionScaleMayBeCompilerOutput : Bool
    r364SubstitutionScaleMayBeCompilerOutputIsTrue :
      r364SubstitutionScaleMayBeCompilerOutput ≡ true

canonicalCMP116Round365AttachmentBoundary : CMP116Round365AttachmentBoundary
canonicalCMP116Round365AttachmentBoundary =
  cmp116-round365-boundary
    true refl
    true refl
    true refl
    true refl
    true refl

fixedPointPerturbationCompilerLevel : ProofLevel
fixedPointPerturbationCompilerLevel = machineChecked

literalCMP116FixedPointMapAttachmentLevel : ProofLevel
literalCMP116FixedPointMapAttachmentLevel = conditional

literalCMP116FixedPointContractionLevel : ProofLevel
literalCMP116FixedPointContractionLevel = conditional

literalCMP116CrossParameterDefectLevel : ProofLevel
literalCMP116CrossParameterDefectLevel = conditional

r364HSubScalePrimitiveRequirement : Bool
r364HSubScalePrimitiveRequirement = false

r364HSubScalePrimitiveRequirementIsFalse :
  r364HSubScalePrimitiveRequirement ≡ false
r364HSubScalePrimitiveRequirementIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
