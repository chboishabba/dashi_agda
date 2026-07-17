module DASHI.Physics.YangMills.BalabanFiniteConstraintCovariance where

-- Covariance-level companion to `BalabanFiniteConstraintChain`.
--
-- For a finite family of adjacent averaging maps Qᵢ and adjoints Qᵢ*, this
-- module proves that recursively pushing a fine covariance through every shell
-- equals pushing it once through the simultaneously composed constraint and
-- its reverse-composed adjoint.  This is the exact source-neutral operator
-- identity needed before the Bałaban-specific block determinant calculation.
--
-- No invertibility, positivity, determinant law, or Yang--Mills estimate is
-- postulated here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _≈_
  ; constrainedCovariance
  ; cong
  )
open import DASHI.Physics.YangMills.BalabanFiniteConstraintChain using
  ( iteratedConstraint )

-- Reverse composition of the adjacent adjoints:
--
--   Q*_{0:n} = Q₀* Q₁* ... Q_{n-1}*.
iteratedAdjoint :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space (suc i) → Space i) →
  (n : ℕ) →
  Space n → Space zero
iteratedAdjoint Space Q* zero z = z
iteratedAdjoint Space Q* (suc n) z =
  iteratedAdjoint Space Q* n (Q* n z)

-- Sequential covariance transport.  At each shell this applies
--
--   C ↦ Qᵢ C Qᵢ*.
iteratedPushedCovariance :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (n : ℕ) →
  (Space zero → Space zero) →
  Space n → Space n
iteratedPushedCovariance Space Q Q* zero inverseFine = inverseFine
iteratedPushedCovariance Space Q Q* (suc n) inverseFine =
  constrainedCovariance
    (Q n)
    (iteratedPushedCovariance Space Q Q* n inverseFine)
    (Q* n)

-- Simultaneous transport through Q_{0:n} and its composed adjoint.
directComposedCovariance :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (n : ℕ) →
  (Space zero → Space zero) →
  Space n → Space n
directComposedCovariance Space Q Q* n inverseFine z =
  iteratedConstraint Space Q n
    (inverseFine (iteratedAdjoint Space Q* n z))

-- The cumulative covariance identity.  The proof is finite induction; the
-- successor step is only congruence under the next averaging map.
finiteComposedConstrainedCovariance :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (n : ℕ) →
  (inverseFine : Space zero → Space zero) →
  iteratedPushedCovariance Space Q Q* n inverseFine
    ≈ directComposedCovariance Space Q Q* n inverseFine
finiteComposedConstrainedCovariance Space Q Q* zero inverseFine z = refl
finiteComposedConstrainedCovariance Space Q Q* (suc n) inverseFine z =
  cong
    (Q n)
    (finiteComposedConstrainedCovariance
      Space Q Q* n inverseFine (Q* n z))

-- Any concrete inverse operation that respects pointwise operator equality
-- transports the cumulative covariance identity to the simultaneous nested
-- Schur operator.  This remains algebraic: the source-specific proof must
-- provide the actual inverse and its domain.
finiteNestedSchurComplementIdentity :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  (n : ℕ) →
  (inverseFine : Space zero → Space zero) →
  (inverseCoarse :
    (Space n → Space n) →
    Space n → Space n) →
  (inverseCongruence :
    {F G : Space n → Space n} →
    F ≈ G →
    inverseCoarse F ≈ inverseCoarse G) →
  inverseCoarse
    (iteratedPushedCovariance Space Q Q* n inverseFine)
  ≈ inverseCoarse
      (directComposedCovariance Space Q Q* n inverseFine)
finiteNestedSchurComplementIdentity
  Space Q Q* n inverseFine inverseCoarse inverseCongruence =
  inverseCongruence
    (finiteComposedConstrainedCovariance
      Space Q Q* n inverseFine)
