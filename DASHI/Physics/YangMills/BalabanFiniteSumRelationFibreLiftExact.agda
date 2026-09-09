module DASHI.Physics.YangMills.BalabanFiniteSumRelationFibreLiftExact where

------------------------------------------------------------------------
-- FINITE-SUM RELATION OBSERVER
--
-- Register the lower finite-rational monotonicity theorem as a genuine
-- relation-preserving fibre observer.  This module sits below physical energy
-- consumers: it depends only on the scalar finite-sum order core, never on a
-- theorem that is itself supposed to consume the lift.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational using (ℚ; _≤_)

import DASHI.Core.AtomicGlobalFibreLiftExact as FibreLift
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
import DASHI.Physics.YangMills.BalabanFiniteRationalOrderCoreExact as OrderCore

sumObserver : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumObserver values field = sumRational values field

sumObserverPreservesPointwiseOrder :
  ∀ {A : Set} (values : List A) {left right : A → ℚ} →
  (∀ value → left value ≤ right value) →
  sumObserver values left ≤ sumObserver values right
sumObserverPreservesPointwiseOrder values {left} {right} pointwise =
  OrderCore.sumRationalMonotone values left right pointwise

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
