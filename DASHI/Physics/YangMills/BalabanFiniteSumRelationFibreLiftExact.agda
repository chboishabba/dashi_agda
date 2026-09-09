module DASHI.Physics.YangMills.BalabanFiniteSumRelationFibreLiftExact where

------------------------------------------------------------------------
-- FINITE-SUM RELATION OBSERVER
--
-- Reuse the already-proved finite rational monotonicity theorem as a genuine
-- relation-preserving fibre observer.  This is the inequality analogue of the
-- global-norm equality lifts used by the variance decomposition.
--
-- No new inequality is proved here.  The existing recursive finite-sum proof
-- is registered once as the preservation receipt required by Core's generic
-- FibreRelationLift, after which consumers may lift pointwise <= facts without
-- reopening the list/fibre representation.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational using (ℚ; _≤_)

import DASHI.Core.AtomicGlobalFibreLiftExact as FibreLift
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
open import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact using
  (sumRationalMonotone)

sumObserver : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumObserver values field = sumRational values field

sumObserverPreservesPointwiseOrder :
  ∀ {A : Set} (values : List A) {left right : A → ℚ} →
  (∀ value → left value ≤ right value) →
  sumObserver values left ≤ sumObserver values right
sumObserverPreservesPointwiseOrder values pointwise =
  sumRationalMonotone values _ _ pointwise

sumOrderFibreLift :
  ∀ {A : Set} (values : List A) →
  FibreLift.FibreRelationLift _≤_ _≤_ (sumObserver values)
sumOrderFibreLift values =
  FibreLift.fibre-relation-lift
    (sumObserverPreservesPointwiseOrder values)

sumRationalMonotoneViaFibre :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotoneViaFibre values left right pointwise =
  FibreLift.atomicRelationFamilyToGlobal
    (sumOrderFibreLift values)
    pointwise

------------------------------------------------------------------------
-- Boundary: the relation lift is a reusable observer receipt, not an axiom
-- that every aggregate preserves every relation.
------------------------------------------------------------------------

relationLiftIsSpecificToRationalOrder :
  ∀ {A : Set} (values : List A) →
  FibreLift.FibreRelationLift _≤_ _≤_ (sumObserver values)
relationLiftIsSpecificToRationalOrder = sumOrderFibreLift
