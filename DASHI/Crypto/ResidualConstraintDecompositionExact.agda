module DASHI.Crypto.ResidualConstraintDecompositionExact where

------------------------------------------------------------------------
-- RESIDUAL CONSTRAINT DECOMPOSITION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record _↔_ (A B : Set) : Set where
  constructor iff
  field forward : A → B
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
       (LocalPlausible₁ (ρ₁ hidden) × Reconcile (ρ₀ hidden) (ρ₁ hidden)))
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
-- Numeric score layer: local scores can be exact while a coupling penalty
-- remains.  This is the score analogue of local predicates + reconciliation.
------------------------------------------------------------------------

record AdditiveResidualScore : Set₁ where
  constructor additiveResidualScore
  field
    Hidden Local₀ Local₁ : Set
    ρ₀ : Hidden → Local₀
    ρ₁ : Hidden → Local₁
    localScore₀ : Local₀ → Nat
    localScore₁ : Local₁ → Nat
    couplingScore : Local₀ → Local₁ → Nat
    globalScore : Hidden → Nat
    scoreDecomposition : ∀ hidden →
      globalScore hidden ≡
      localScore₀ (ρ₀ hidden) +
      (localScore₁ (ρ₁ hidden) + couplingScore (ρ₀ hidden) (ρ₁ hidden))
open AdditiveResidualScore public

globalScoreIsLocalPlusCoupling :
  ∀ (score : AdditiveResidualScore) hidden →
  globalScore score hidden ≡
  localScore₀ score (ρ₀ score hidden) +
  (localScore₁ score (ρ₁ score hidden) +
   couplingScore score (ρ₀ score hidden) (ρ₁ score hidden))
globalScoreIsLocalPlusCoupling score = scoreDecomposition score

------------------------------------------------------------------------
-- Concrete counterexample: every Bool coordinate is locally admissible and has
-- local score zero, but equality reconciliation rejects crossed coordinates.
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
  localGlobal (bitPair false false) = iff (λ eq → refl , (refl , eq)) (λ { (p₀ , (p₁ , eq)) → eq })
  localGlobal (bitPair false true) = iff (λ ()) (λ { (p₀ , (p₁ , ())) })
  localGlobal (bitPair true false) = iff (λ ()) (λ { (p₀ , (p₁ , ())) })
  localGlobal (bitPair true true) = iff (λ eq → refl , (refl , eq)) (λ { (p₀ , (p₁ , eq)) → eq })

localTestabilityDoesNotGiveIndependentSolvability : Always false × Always true
localTestabilityDoesNotGiveIndependentSolvability = refl , refl

crossLocalPairCannotReconcile : EqualBits false true → ⊥
crossLocalPairCannotReconcile ()

zeroScore : Bool → Nat
zeroScore b = 0

mismatchScore : Bool → Bool → Nat
mismatchScore false false = 0
mismatchScore false true = 1
mismatchScore true false = 1
mismatchScore true true = 0

pairMismatchScore : BitPair → Nat
pairMismatchScore pair = mismatchScore (left pair) (right pair)

bitPairAdditiveScore : AdditiveResidualScore
bitPairAdditiveScore = additiveResidualScore
  BitPair Bool Bool left right zeroScore zeroScore mismatchScore pairMismatchScore proof
  where
  proof : ∀ pair →
    pairMismatchScore pair ≡
    zeroScore (left pair) + (zeroScore (right pair) + mismatchScore (left pair) (right pair))
  proof (bitPair false false) = refl
  proof (bitPair false true) = refl
  proof (bitPair true false) = refl
  proof (bitPair true true) = refl

record ReconciliationBottleneck (Local₀ Local₁ : Set) : Set₁ where
  constructor reconciliationBottleneck
  field
    Reconcile : Local₀ → Local₁ → Set
    CandidatePair : Set
    pairCoordinates : CandidatePair → Local₀ × Local₁
