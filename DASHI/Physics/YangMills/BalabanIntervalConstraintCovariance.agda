module DASHI.Physics.YangMills.BalabanIntervalConstraintCovariance where

-- Covariance identity for the arbitrary interval Q_{k:k+n}.
--
-- This is the operator-level form needed by the cumulative block calculation:
-- recursively pushing the covariance through the shells k,...,k+n-1 equals a
-- single push through the composed interval constraint and its reverse-composed
-- adjoint.
--
-- The proof is finite induction and introduces no determinant or analytic
-- premise.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _≈_
  ; constrainedCovariance
  ; cong
  )
open import DASHI.Physics.YangMills.BalabanIntervalConstraintChain using
  ( intervalConstraint )

intervalAdjoint :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space (suc i) → Space i) →
  (k n : ℕ) →
  Space (n + k) → Space k
intervalAdjoint Space Q* k zero z = z
intervalAdjoint Space Q* k (suc n) z =
  intervalAdjoint Space Q* k n (Q* (n + k) z)

intervalPushedCovariance :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (k n : ℕ) →
  (Space k → Space k) →
  Space (n + k) → Space (n + k)
intervalPushedCovariance Space Q Q* k zero inverseStart = inverseStart
intervalPushedCovariance Space Q Q* k (suc n) inverseStart =
  constrainedCovariance
    (Q (n + k))
    (intervalPushedCovariance Space Q Q* k n inverseStart)
    (Q* (n + k))

directIntervalCovariance :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (k n : ℕ) →
  (Space k → Space k) →
  Space (n + k) → Space (n + k)
directIntervalCovariance Space Q Q* k n inverseStart z =
  intervalConstraint Space Q k n
    (inverseStart (intervalAdjoint Space Q* k n z))

intervalComposedConstrainedCovariance :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (k n : ℕ) →
  (inverseStart : Space k → Space k) →
  intervalPushedCovariance Space Q Q* k n inverseStart
    ≈ directIntervalCovariance Space Q Q* k n inverseStart
intervalComposedConstrainedCovariance Space Q Q* k zero inverseStart z = refl
intervalComposedConstrainedCovariance Space Q Q* k (suc n) inverseStart z =
  cong
    (Q (n + k))
    (intervalComposedConstrainedCovariance
      Space Q Q* k n inverseStart (Q* (n + k) z))

intervalNestedSchurComplementIdentity :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (k n : ℕ) →
  (inverseStart : Space k → Space k) →
  (inverseEnd :
    (Space (n + k) → Space (n + k)) →
    Space (n + k) → Space (n + k)) →
  (inverseCongruence :
    {F G : Space (n + k) → Space (n + k)} →
    F ≈ G →
    inverseEnd F ≈ inverseEnd G) →
  inverseEnd
    (intervalPushedCovariance Space Q Q* k n inverseStart)
  ≈ inverseEnd
      (directIntervalCovariance Space Q Q* k n inverseStart)
intervalNestedSchurComplementIdentity
  Space Q Q* k n inverseStart inverseEnd inverseCongruence =
  inverseCongruence
    (intervalComposedConstrainedCovariance
      Space Q Q* k n inverseStart)
