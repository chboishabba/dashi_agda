module DASHI.Physics.YangMills.BalabanFiniteConstraintChain where

-- Finite-chain extension of `BalabanNestedConstraintMinimum`.
--
-- Bałaban's cumulative constraint is not merely a two-stage composite.  For a
-- scale-indexed family
--
--   Qᵢ : Space i → Space (suc i)
--
-- this module constructs the literal composed map Q_{0:n}, records the full
-- sequence of intermediate constraint values, and proves that sequential and
-- simultaneous feasibility are equivalent for every finite n.  Consequently
-- the two formulations have exactly the same minimizers for any objective and
-- comparison relation.
--
-- This is source-neutral algebra only.  It does not assert the source-specific
-- determinant factorisation, penalty correction, or any Yang--Mills estimate.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _⇔_
  ; iff
  ; Minimises
  ; trans
  ; cong
  )

-- The simultaneous nested constraint Q_{0:n}.
iteratedConstraint :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space i → Space (suc i)) →
  (n : ℕ) →
  Space zero → Space n
iteratedConstraint Space Q zero x = x
iteratedConstraint Space Q (suc n) x =
  Q n (iteratedConstraint Space Q n x)

-- Sequential feasibility retains every intermediate coarse variable.  At the
-- final stage it states Qₙ y = z; recursively, y is itself reached by the
-- preceding sequence of constraints.
SequentialFeasibleN :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space i → Space (suc i)) →
  (n : ℕ) →
  Space n →
  Space zero →
  Set
SequentialFeasibleN Space Q zero z x = x ≡ z
SequentialFeasibleN Space Q (suc n) z x =
  Σ (Space n)
    (λ y →
      SequentialFeasibleN Space Q n y x
        × (Q n y ≡ z))

-- Direct feasibility retains only the single composed equation.
DirectFeasibleN :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space i → Space (suc i)) →
  (n : ℕ) →
  Space n →
  Space zero →
  Set
DirectFeasibleN Space Q n z x =
  iteratedConstraint Space Q n x ≡ z

-- A direct witness determines the canonical sequence of intermediate values.
directToSequentialN :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (n : ℕ) →
  (z : Space n) →
  (x : Space zero) →
  DirectFeasibleN Space Q n z x →
  SequentialFeasibleN Space Q n z x
directToSequentialN Space Q zero z x direct = direct
directToSequentialN Space Q (suc n) z x direct =
  iteratedConstraint Space Q n x ,
  ( directToSequentialN
      Space Q n (iteratedConstraint Space Q n x) x refl
  , direct
  )

-- Conversely, eliminating the remembered intermediate values gives the single
-- composed constraint equation.
sequentialToDirectN :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (n : ℕ) →
  (z : Space n) →
  (x : Space zero) →
  SequentialFeasibleN Space Q n z x →
  DirectFeasibleN Space Q n z x
sequentialToDirectN Space Q zero z x sequential = sequential
sequentialToDirectN Space Q (suc n) z x sequential =
  trans
    (cong
      (Q n)
      (sequentialToDirectN
        Space Q n (proj₁ sequential) x (proj₁ (proj₂ sequential))))
    (proj₂ (proj₂ sequential))

finiteSequentialFeasibleIffDirect :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (n : ℕ) →
  (z : Space n) →
  (x : Space zero) →
  SequentialFeasibleN Space Q n z x
    ⇔ DirectFeasibleN Space Q n z x
finiteSequentialFeasibleIffDirect Space Q n z x =
  iff
    (sequentialToDirectN Space Q n z x)
    (directToSequentialN Space Q n z x)

-- Since the feasible subsets of the fine space coincide, minimization against
-- either description is the same theorem, without requiring an order,
-- completeness, or an existence axiom.
sequentialMinimumToDirectN :
  {Value : Set} →
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (_≼_ : Value → Value → Set) →
  (objective : Space zero → Value) →
  (n : ℕ) →
  (z : Space n) →
  (x : Space zero) →
  Minimises _≼_ objective (SequentialFeasibleN Space Q n z) x →
  Minimises _≼_ objective (DirectFeasibleN Space Q n z) x
sequentialMinimumToDirectN Space Q _≼_ objective n z x minimum =
  sequentialToDirectN Space Q n z x (proj₁ minimum) ,
  λ y direct-y →
    proj₂ minimum y (directToSequentialN Space Q n z y direct-y)

directMinimumToSequentialN :
  {Value : Set} →
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (_≼_ : Value → Value → Set) →
  (objective : Space zero → Value) →
  (n : ℕ) →
  (z : Space n) →
  (x : Space zero) →
  Minimises _≼_ objective (DirectFeasibleN Space Q n z) x →
  Minimises _≼_ objective (SequentialFeasibleN Space Q n z) x
directMinimumToSequentialN Space Q _≼_ objective n z x minimum =
  directToSequentialN Space Q n z x (proj₁ minimum) ,
  λ y sequential-y →
    proj₂ minimum y (sequentialToDirectN Space Q n z y sequential-y)

finiteSequentialMinimumEqualsDirectMinimum :
  {Value : Set} →
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (_≼_ : Value → Value → Set) →
  (objective : Space zero → Value) →
  (n : ℕ) →
  (z : Space n) →
  (x : Space zero) →
  Minimises _≼_ objective (SequentialFeasibleN Space Q n z) x
    ⇔ Minimises _≼_ objective (DirectFeasibleN Space Q n z) x
finiteSequentialMinimumEqualsDirectMinimum
  Space Q _≼_ objective n z x =
  iff
    (sequentialMinimumToDirectN Space Q _≼_ objective n z x)
    (directMinimumToSequentialN Space Q _≼_ objective n z x)
