
module DASHI.Physics.ThreeBodyPredictability where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import UFTC_Lattice using
  ( ConeInterior
  ; ConeInteriorPreserved
  ; InInterior
  ; Boundary
  )

open import CounterexampleHarness using (Counterexample)
open import Contraction using (Contractive≢; StrictContraction)
open import MDL.Core using (Lyapunov; CodeLength)

------------------------------------------------------------------------
-- Repo-native theorem surfaces for a three-body predictability program.

postulate
  ℝ : Set

record Vec3 : Set where
  field
    x y z : ℝ

record Body : Set where
  field
    pos  : Vec3
    vel  : Vec3
    mass : ℝ

record ThreeBodyState : Set where
  field
    b₁ b₂ b₃ : Body
    t        : ℝ

record Delta3Body : Set where
  field
    Δr₁₂ Δr₁₃ Δr₂₃ : ℝ
    Δv₁ Δv₂ Δv₃    : Vec3

postulate
  Step    : ThreeBodyState → ThreeBodyState
  DeltaOf : ThreeBodyState → Delta3Body

postulate
  ΔCone : ConeInterior {Delta3Body}

data Regime : Set where
  NearPeriodic   : Regime
  Resonant       : Regime
  CloseEncounter : Regime
  Escape         : Regime

postulate
  classify : ThreeBodyState → Regime

postulate
  CarrierQ : Set
  TΔ3      : Delta3Body → CarrierQ
  Q̂core   : CarrierQ → CodeLength

EnergyΔ3 : Delta3Body → CodeLength
EnergyΔ3 δ = Q̂core (TΔ3 δ)

data DeltaPath : Set where
  []Δ  : DeltaPath
  _∷Δ_ : Delta3Body → DeltaPath → DeltaPath

Action3 : DeltaPath → CodeLength
Action3 []Δ       = zero
Action3 (δ ∷Δ Δs) = EnergyΔ3 δ + Action3 Δs

postulate
  StepΔ : Delta3Body → Delta3Body

ThreeBodyLyapunov : Set₁
ThreeBodyLyapunov = Lyapunov StepΔ

postulate
  iterate : Nat → ThreeBodyState → ThreeBodyState

record LocalPredictiveHorizon (s : ThreeBodyState) : Set₁ where
  field
    horizon : Nat
    stable-prefix :
      ∀ n →
      InInterior ΔCone (DeltaOf (iterate n s))

postulate
  _≢R_ : Regime → Regime → Set

record ChaosBoundary (s : ThreeBodyState) : Set₁ where
  field
    on-boundary :
      Boundary ΔCone (DeltaOf s)

    regime-fracture :
      Σ Regime (λ r₁ →
      Σ Regime (λ r₂ →
        r₁ ≢R r₂))

record PredictabilityTheorem : Set₁ where
  field
    interior-contractive-gives-horizon :
      ∀ s →
      InInterior ΔCone (DeltaOf s) →
      Σ (StrictContraction UState StepState) (λ _ →
      Σ ThreeBodyLyapunov (λ _ →
        LocalPredictiveHorizon s))

    boundary-gives-counterexample :
      ∀ s →
      Boundary ΔCone (DeltaOf s) →
      Counterexample (λ st → InInterior ΔCone (DeltaOf st))

  where
    postulate
      UState    : _
      StepState : _ → _

record BoundaryBranchingTheorem : Set₁ where
  field
    branch-at-boundary :
      ∀ s →
      Boundary ΔCone (DeltaOf s) →
      Σ ThreeBodyState (λ s₁ →
      Σ ThreeBodyState (λ s₂ →
        classify s₁ ≢R classify s₂))

record InteriorCoherenceTheorem : Set₁ where
  field
    interior-regime-persistence :
      ∀ s →
      InInterior ΔCone (DeltaOf s) →
      Σ (Contractive≢ UState StepState) (λ _ →
      Σ Regime (λ r →
        ∀ n → classify (iterate n s) ≡ r))

  where
    postulate
      UState    : _
      StepState : _ → _

record RegimeWeights : Set where
  field
    wPeriodic   : CodeLength
    wResonant   : CodeLength
    wEncounter  : CodeLength
    wEscape     : CodeLength

postulate
  weightsAt : ThreeBodyState → Nat → RegimeWeights
  _≈W_      : RegimeWeights → RegimeWeights → Set

record RegimeWeightConvergenceTheorem : Set₁ where
  field
    converges-on-stable-prefix :
      ∀ s →
      LocalPredictiveHorizon s →
      Σ RegimeWeights (λ w∞ →
        ∀ n → weightsAt s n ≈W w∞)

postulate
  EnergyΔ3-compatible-with-quadratic-bridge : Set
