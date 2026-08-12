module DASHI.Crypto.ResidualConstraintDecompositionExact where

------------------------------------------------------------------------
-- RESIDUAL CONSTRAINT DECOMPOSITION
--
-- Exact finite/type-theoretic core for the verification -> search gap.
-- Local testability is separated from independent global solvability by an
-- explicit reconciliation relation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

open _↔_ public

record TwoLocalResidualSystem : Set₁ where
  constructor twoLocalResidualSystem
  field
    Hidden Local₀ Local₁ : Set
    ρ₀ : Hidden → Local₀
    ρ₁ : Hidden → Local₁
    LocalPlausible₀ : Local₀ → Set
    LocalPlausible₁ : Local₁ → Set
    Reconcile : Local₀ → Local₁ → Set
    GlobalPlausible : Hidden → Set
    globalPlausibleIffLocal : ∀ hidden →
      GlobalPlausible hidden ↔
      (LocalPlausible₀ (ρ₀ hidden) ×
       (LocalPlausible₁ (ρ₁ hidden) ×
        Reconcile (ρ₀ hidden) (ρ₁ hidden)))

open TwoLocalResidualSystem public

globalImpliesEachLocal :
  ∀ {system : TwoLocalResidualSystem} {hidden} →
  GlobalPlausible system hidden →
  LocalPlausible₀ system (ρ₀ system hidden) ×
  LocalPlausible₁ system (ρ₁ system hidden)
globalImpliesEachLocal {system} {hidden} global with
  forward (globalPlausibleIffLocal system hidden) global
... | local₀ , (local₁ , reconcile) = local₀ , local₁

------------------------------------------------------------------------
-- Concrete counterexample: each Bool coordinate is locally admissible, but
-- reconciliation requires equality.  Hence arbitrary products of local
-- solutions need not be globally admissible.
------------------------------------------------------------------------

data EqualBits : Bool → Bool → Set where
  equal-false : EqualBits false false
  equal-true  : EqualBits true true

record BitPair : Set where
  constructor bitPair
  field left right : Bool

open BitPair public

Always : Bool → Set
Always bit = bit ≡ bit

GlobalEqual : BitPair → Set
GlobalEqual pair = EqualBits (left pair) (right pair)

bitPairResidualSystem : TwoLocalResidualSystem
bitPairResidualSystem = twoLocalResidualSystem
  BitPair Bool Bool left right Always Always EqualBits GlobalEqual localGlobal
  where
  localGlobal : ∀ pair →
    GlobalEqual pair ↔
    (Always (left pair) × (Always (right pair) × EqualBits (left pair) (right pair)))
  localGlobal (bitPair false false) = iff
    (λ eq → refl , (refl , eq))
    (λ { (p₀ , (p₁ , eq)) → eq })
  localGlobal (bitPair false true) = iff
    (λ ())
    (λ { (p₀ , (p₁ , ())) })
  localGlobal (bitPair true false) = iff
    (λ ())
    (λ { (p₀ , (p₁ , ())) })
  localGlobal (bitPair true true) = iff
    (λ eq → refl , (refl , eq))
    (λ { (p₀ , (p₁ , eq)) → eq })

localTestabilityDoesNotGiveIndependentSolvability :
  Always false × Always true
localTestabilityDoesNotGiveIndependentSolvability = refl , refl

crossLocalPairCannotReconcile : EqualBits false true → ⊥
crossLocalPairCannotReconcile ()

-- The mathematical boundary used downstream: a local-coordinate transform is
-- useful for search only if the reconciliation seam is itself tractable.
record ReconciliationBottleneck (Local₀ Local₁ : Set) : Set₁ where
  constructor reconciliationBottleneck
  field
    Reconcile : Local₀ → Local₁ → Set
    CandidatePair : Set
    pairCoordinates : CandidatePair → Local₀ × Local₁
