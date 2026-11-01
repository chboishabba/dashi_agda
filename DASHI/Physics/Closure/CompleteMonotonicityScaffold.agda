module DASHI.Physics.Closure.CompleteMonotonicityScaffold where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_)

postulate
  ℝ : Set
  ℝ≥0 : Set
  ℝ>0 : Set
  
  _≥_ : ℝ → ℝ → Set
  _*_ : ℝ → ℝ → ℝ
  
  Differentiable : Nat → (ℝ≥0 → ℝ) → Set
  deriv : (n : Nat) → (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ)
  
  negOnePow : Nat → ℝ
  
  PositiveBorelMeasure : Set → Set
  ∫ : {A : Set} → (A → ℝ) → PositiveBorelMeasure A → ℝ
  exp : ℝ → ℝ
  support : {A : Set} → PositiveBorelMeasure A → (A → Set)
  
  SelfAdjointOperator : Set
  twoPointFn : SelfAdjointOperator → (ℝ≥0 → ℝ)
  spectralMeasure : SelfAdjointOperator → PositiveBorelMeasure ℝ≥0
  lowestEigenvalue : SelfAdjointOperator → ℝ
  
  subset : {A : Set} → (A → Set) → (A → Set) → Set
  halfOpenInterval : ℝ → (ℝ≥0 → Set)
  
  realOf : ℝ>0 → ℝ
  realOf≥0 : ℝ≥0 → ℝ

-- Layer 1: The Bernstein witness
record CompletelyMonotoneTwoPoint
    (G : ℝ≥0 → ℝ) : Set where
  field
    infinitely-differentiable : ∀ n → Differentiable n G
    alternating-sign : ∀ n (t : ℝ≥0) → ((negOnePow n) * (deriv n G t)) ≥ (deriv 0 G t)

-- Layer 2: Spectral representation (Bernstein-Widder)
record SpectralRepresentation
    (G : ℝ≥0 → ℝ) (μ : PositiveBorelMeasure ℝ≥0) : Set where
  field
    laplace-form : ∀ (t : ℝ≥0) → G t ≡ ∫ (λ λ′ → exp ((realOf≥0 λ′) * (realOf≥0 t))) μ
    gap-bound    : Σ ℝ>0 (λ m → subset (support μ) (halfOpenInterval (realOf m)))

-- Layer 3: Hamiltonian gap receipt
record SpectralGapFromCM
    (H : SelfAdjointOperator) (m : ℝ>0) : Set where
  field
    cm-witness   : CompletelyMonotoneTwoPoint (twoPointFn H)
    spectral-rep : SpectralRepresentation (twoPointFn H) (spectralMeasure H)
    gap-transport : lowestEigenvalue H ≥ realOf m
