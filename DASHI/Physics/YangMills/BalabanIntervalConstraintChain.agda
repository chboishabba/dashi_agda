module DASHI.Physics.YangMills.BalabanIntervalConstraintChain where

-- Arbitrary-interval form of the finite Bałaban constraint chain.
--
-- The earlier finite-chain module starts at scale zero.  The cumulative RG
-- theorem needs Q_{k:m} for arbitrary k < m.  Writing the interval by a start
-- scale `k` and a length `n`, this module constructs
--
--   Q_{k:k+n} : Space k → Space (n + k)
--
-- and proves that remembering every intermediate field is equivalent to the
-- single simultaneous constraint.  Minimisers therefore agree on every
-- interval, not only prefixes from scale zero.
--
-- No determinant law, positivity estimate, or Yang--Mills authority record is
-- introduced.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _⇔_
  ; iff
  ; Minimises
  ; trans
  ; cong
  )

intervalConstraint :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space i → Space (suc i)) →
  (k n : ℕ) →
  Space k → Space (n + k)
intervalConstraint Space Q k zero x = x
intervalConstraint Space Q k (suc n) x =
  Q (n + k) (intervalConstraint Space Q k n x)

SequentialFeasibleInterval :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space i → Space (suc i)) →
  (k n : ℕ) →
  Space (n + k) →
  Space k →
  Set
SequentialFeasibleInterval Space Q k zero z x = x ≡ z
SequentialFeasibleInterval Space Q k (suc n) z x =
  Σ (Space (n + k))
    (λ y →
      SequentialFeasibleInterval Space Q k n y x
        × (Q (n + k) y ≡ z))

DirectFeasibleInterval :
  (Space : ℕ → Set) →
  ((i : ℕ) → Space i → Space (suc i)) →
  (k n : ℕ) →
  Space (n + k) →
  Space k →
  Set
DirectFeasibleInterval Space Q k n z x =
  intervalConstraint Space Q k n x ≡ z

directToSequentialInterval :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (k n : ℕ) →
  (z : Space (n + k)) →
  (x : Space k) →
  DirectFeasibleInterval Space Q k n z x →
  SequentialFeasibleInterval Space Q k n z x
directToSequentialInterval Space Q k zero z x direct = direct
directToSequentialInterval Space Q k (suc n) z x direct =
  intervalConstraint Space Q k n x ,
  ( directToSequentialInterval
      Space Q k n (intervalConstraint Space Q k n x) x refl
  , direct
  )

sequentialToDirectInterval :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (k n : ℕ) →
  (z : Space (n + k)) →
  (x : Space k) →
  SequentialFeasibleInterval Space Q k n z x →
  DirectFeasibleInterval Space Q k n z x
sequentialToDirectInterval Space Q k zero z x sequential = sequential
sequentialToDirectInterval Space Q k (suc n) z x sequential =
  trans
    (cong
      (Q (n + k))
      (sequentialToDirectInterval
        Space Q k n (proj₁ sequential) x (proj₁ (proj₂ sequential))))
    (proj₂ (proj₂ sequential))

intervalSequentialFeasibleIffDirect :
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (k n : ℕ) →
  (z : Space (n + k)) →
  (x : Space k) →
  SequentialFeasibleInterval Space Q k n z x
    ⇔ DirectFeasibleInterval Space Q k n z x
intervalSequentialFeasibleIffDirect Space Q k n z x =
  iff
    (sequentialToDirectInterval Space Q k n z x)
    (directToSequentialInterval Space Q k n z x)

sequentialMinimumToDirectInterval :
  {Value : Set} →
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (_≼_ : Value → Value → Set) →
  (objective : Space k → Value) →
  (k n : ℕ) →
  (z : Space (n + k)) →
  (x : Space k) →
  Minimises _≼_ objective
    (SequentialFeasibleInterval Space Q k n z) x →
  Minimises _≼_ objective
    (DirectFeasibleInterval Space Q k n z) x
sequentialMinimumToDirectInterval Space Q _≼_ objective k n z x minimum =
  sequentialToDirectInterval Space Q k n z x (proj₁ minimum) ,
  λ y direct-y →
    proj₂ minimum y
      (directToSequentialInterval Space Q k n z y direct-y)

directMinimumToSequentialInterval :
  {Value : Set} →
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (_≼_ : Value → Value → Set) →
  (objective : Space k → Value) →
  (k n : ℕ) →
  (z : Space (n + k)) →
  (x : Space k) →
  Minimises _≼_ objective
    (DirectFeasibleInterval Space Q k n z) x →
  Minimises _≼_ objective
    (SequentialFeasibleInterval Space Q k n z) x
directMinimumToSequentialInterval Space Q _≼_ objective k n z x minimum =
  directToSequentialInterval Space Q k n z x (proj₁ minimum) ,
  λ y sequential-y →
    proj₂ minimum y
      (sequentialToDirectInterval Space Q k n z y sequential-y)

intervalSequentialMinimumEqualsDirectMinimum :
  {Value : Set} →
  (Space : ℕ → Set) →
  (Q : (i : ℕ) → Space i → Space (suc i)) →
  (_≼_ : Value → Value → Set) →
  (objective : Space k → Value) →
  (k n : ℕ) →
  (z : Space (n + k)) →
  (x : Space k) →
  Minimises _≼_ objective
    (SequentialFeasibleInterval Space Q k n z) x
    ⇔ Minimises _≼_ objective
        (DirectFeasibleInterval Space Q k n z) x
intervalSequentialMinimumEqualsDirectMinimum
  Space Q _≼_ objective k n z x =
  iff
    (sequentialMinimumToDirectInterval
      Space Q _≼_ objective k n z x)
    (directMinimumToSequentialInterval
      Space Q _≼_ objective k n z x)
