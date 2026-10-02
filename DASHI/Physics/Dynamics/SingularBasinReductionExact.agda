{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.SingularBasinReductionExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Closure.Basin as Basin

------------------------------------------------------------------------
-- Generic reduction semantics for attractor basins.
--
-- A dimensional reduction is not assumed to preserve basin membership.
-- This module isolates preservation, reflection, exactness, and two distinct
-- obstruction witnesses:
--
--   1. a full-state basin member whose reduced image is excluded; and
--   2. two full states with the same reduced image but different full-basin
--      membership, proving that full basin membership does not factor through
--      the selected projection at all.
------------------------------------------------------------------------

record LogicalEquivalence (A B : Set) : Set where
  constructor logicalEquivalence
  field
    forward : A → B
    backward : B → A

open LogicalEquivalence public

record BasinReduction (Full Reduced : Set) : Set₁ where
  field
    project : Full → Reduced
    fullBasin : Basin.Basin Full
    reducedBasin : Basin.Basin Reduced

open BasinReduction public

FullMember :
  ∀ {Full Reduced : Set} →
  BasinReduction Full Reduced →
  Full →
  Set
FullMember R x =
  Basin.Basin.InBasin (fullBasin R) x

ReducedMember :
  ∀ {Full Reduced : Set} →
  BasinReduction Full Reduced →
  Reduced →
  Set
ReducedMember R y =
  Basin.Basin.InBasin (reducedBasin R) y

BasinPreserving :
  ∀ {Full Reduced : Set} →
  BasinReduction Full Reduced →
  Set
BasinPreserving R =
  ∀ x →
  FullMember R x →
  ReducedMember R (project R x)

BasinReflecting :
  ∀ {Full Reduced : Set} →
  BasinReduction Full Reduced →
  Set
BasinReflecting R =
  ∀ x →
  ReducedMember R (project R x) →
  FullMember R x

BasinExact :
  ∀ {Full Reduced : Set} →
  BasinReduction Full Reduced →
  Set
BasinExact R =
  BasinPreserving R × BasinReflecting R

record BasinReductionFailure
  {Full Reduced : Set}
  (R : BasinReduction Full Reduced) : Set where
  field
    witness : Full
    fullMember : FullMember R witness
    reducedExcluded :
      ¬ ReducedMember R (project R witness)

open BasinReductionFailure public

failure-refutes-preservation :
  ∀ {Full Reduced : Set}
    {R : BasinReduction Full Reduced} →
  BasinReductionFailure R →
  ¬ BasinPreserving R
failure-refutes-preservation failure preservation =
  reducedExcluded failure
    (preservation
      (witness failure)
      (fullMember failure))

failure-refutes-exactness :
  ∀ {Full Reduced : Set}
    {R : BasinReduction Full Reduced} →
  BasinReductionFailure R →
  ¬ BasinExact R
failure-refutes-exactness failure exact =
  failure-refutes-preservation failure (fst exact)

------------------------------------------------------------------------
-- Stronger information-loss obstruction.
--
-- If two full states collapse to the same reduced state while differing in a
-- selected predicate, then no predicate on the reduced state can exactly
-- recover that selected full-state predicate.
------------------------------------------------------------------------

record PredicateFactorisation
  {Full Reduced : Set}
  (project : Full → Reduced)
  (Predicate : Full → Set) : Set₁ where
  field
    reducedPredicate : Reduced → Set
    exactAt :
      ∀ x →
      LogicalEquivalence
        (Predicate x)
        (reducedPredicate (project x))

open PredicateFactorisation public

record ProjectionPredicateCollision
  {Full Reduced : Set}
  (project : Full → Reduced)
  (Predicate : Full → Set) : Set where
  field
    left : Full
    right : Full
    sameProjection : project left ≡ project right
    leftHas : Predicate left
    rightLacks : ¬ Predicate right

open ProjectionPredicateCollision public

collision-refutes-factorisation :
  ∀ {Full Reduced : Set}
    {project : Full → Reduced}
    {Predicate : Full → Set} →
  ProjectionPredicateCollision project Predicate →
  ¬ PredicateFactorisation project Predicate
collision-refutes-factorisation collision factorisation
  with sameProjection collision
... | refl =
  rightLacks collision
    (backward
      (exactAt factorisation (right collision))
      (forward
        (exactAt factorisation (left collision))
        (leftHas collision)))

record BasinProjectionCollision
  {Full Reduced : Set}
  (R : BasinReduction Full Reduced) : Set where
  field
    inside : Full
    outside : Full
    sameReducedState :
      project R inside ≡ project R outside
    insideFullBasin :
      FullMember R inside
    outsideFullBasin :
      ¬ FullMember R outside

open BasinProjectionCollision public

basin-collision-refutes-full-membership-factorisation :
  ∀ {Full Reduced : Set}
    {R : BasinReduction Full Reduced} →
  BasinProjectionCollision R →
  ¬ PredicateFactorisation (project R) (FullMember R)
basin-collision-refutes-full-membership-factorisation collision =
  collision-refutes-factorisation
    record
      { left = inside collision
      ; right = outside collision
      ; sameProjection = sameReducedState collision
      ; leftHas = insideFullBasin collision
      ; rightLacks = outsideFullBasin collision
      }

------------------------------------------------------------------------
-- Local-state correspondence and global-basin preservation are orthogonal.
--
-- This is the reusable theorem boundary needed by singular-funnel examples:
-- even if a reduction carries selected fixed/stable states correctly, that fact
-- alone does not construct BasinPreserving.
------------------------------------------------------------------------

record LocalAttractorCorrespondence
  {Full Reduced : Set}
  (R : BasinReduction Full Reduced) : Set₁ where
  field
    FullAttractor : Set
    ReducedAttractor : Set
    fullPoint : FullAttractor → Full
    reducedPoint : ReducedAttractor → Reduced
    mapAttractor : FullAttractor → ReducedAttractor
    selectedPointsAgree :
      ∀ a →
      project R (fullPoint a) ≡
        reducedPoint (mapAttractor a)

open LocalAttractorCorrespondence public

record LocalCorrespondenceWithGlobalFailure
  {Full Reduced : Set}
  (R : BasinReduction Full Reduced) : Set₁ where
  field
    local : LocalAttractorCorrespondence R
    globalFailure : BasinReductionFailure R

open LocalCorrespondenceWithGlobalFailure public
