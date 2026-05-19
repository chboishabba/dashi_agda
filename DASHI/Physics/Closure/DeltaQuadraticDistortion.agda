module DASHI.Physics.Closure.DeltaQuadraticDistortion where

open import Agda.Primitive using (Level; lsuc; Setω)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_; _∸_; z≤n)
import Data.Nat.Properties as NatP

import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Arithmetic.ArithmeticIntegerEmbeddingBridge as AIEB

absDiff : Nat → Nat → Nat
absDiff m n = (m ∸ n) + (n ∸ m)

absDiff-refl≤0 : ∀ n → absDiff n n ≤ 0
absDiff-refl≤0 n rewrite NatP.n∸n≡0 n = z≤n

record DeltaQuadraticDistortion
  {ℓS : Level}
  (State : Set ℓS) :
  Set (lsuc ℓS) where
  field
    pressureΔ : State → Nat
    energyQ : State → Nat
    epsilon : State → Nat
    distortionBound :
      ∀ s → absDiff (energyQ s) (pressureΔ s) ≤ epsilon s

record DeltaQuadraticOrder
  {ℓS : Level}
  (State : Set ℓS) :
  Set (lsuc ℓS) where
  field
    pressureΔ : State → Nat
    energyQ : State → Nat
    control : Nat → Nat
    monotone-up-to :
      ∀ s → pressureΔ s ≤ control (energyQ s)

record ControlledDeltaQuadraticTransform
  {ℓS : Level}
  (State : Set ℓS) :
  Set (lsuc ℓS) where
  field
    distortion : DeltaQuadraticDistortion State
    order : DeltaQuadraticOrder State

record DominanceTransport
  {ℓS : Level}
  (State : Set ℓS)
  (transform : ControlledDeltaQuadraticTransform State) :
  Set (lsuc ℓS) where
  open ControlledDeltaQuadraticTransform transform
  open DeltaQuadraticDistortion distortion
    renaming
      ( pressureΔ to pressure
      ; energyQ to energy
      ; epsilon to errorBound
      )

  field
    mainΔ : State → Nat
    errorΔ : State → Nat
    mainQ : State → Nat
    errorQ : State → Nat
    deltaDominance :
      ∀ s → errorΔ s ≤ mainΔ s
    transportedDominance :
      ∀ s → errorQ s ≤ mainQ s
    mainControlled :
      ∀ s → absDiff (mainQ s) (mainΔ s) ≤ errorBound s
    errorControlled :
      ∀ s → absDiff (errorQ s) (errorΔ s) ≤ errorBound s

zeroErrorDominanceTransport :
  {ℓS : Level} {State : Set ℓS} →
  (transform : ControlledDeltaQuadraticTransform State) →
  DominanceTransport State transform
zeroErrorDominanceTransport {State = State} transform =
  let
    open ControlledDeltaQuadraticTransform transform
    open DeltaQuadraticDistortion distortion
      renaming
        ( pressureΔ to pressure
        ; energyQ to energy
        ; epsilon to errorBound
        )
  in
  record
    { mainΔ = pressure
    ; errorΔ = λ _ → 0
    ; mainQ = energy
    ; errorQ = λ _ → 0
    ; deltaDominance = λ _ → z≤n
    ; transportedDominance = λ _ → z≤n
    ; mainControlled = λ s → distortionBound s
    ; errorControlled =
        λ _ → NatP.≤-trans (absDiff-refl≤0 0) z≤n
    }

record DeltaQuadraticDistortionForCompatibility
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    compatibility :
      DQ.CancellationPressureCompatibility theorem dim≡15

    energyNat :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState
        (DQ.CancellationPressureCompatibility.pressureBridge compatibility) →
      Nat

    epsilonNat :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState
        (DQ.CancellationPressureCompatibility.pressureBridge compatibility) →
      Nat

    energyNatMatchesQuadratic : Set₁

    distortionBound :
      ∀ s →
      absDiff
        (energyNat s)
        (AIEB.scalarCancellationPressure
          (DQ.CancellationPressureCompatibility.pressureBridge compatibility)
          s)
      ≤
      epsilonNat s

  State : Set
  State =
    AIEB.IntegerEmbeddingPressureBridge.IntegerState
      (DQ.CancellationPressureCompatibility.pressureBridge compatibility)

  pressureNat : State → Nat
  pressureNat s =
    AIEB.scalarCancellationPressure
      (DQ.CancellationPressureCompatibility.pressureBridge compatibility)
      s

  distortionSurface : DeltaQuadraticDistortion State
  distortionSurface = record
    { pressureΔ = pressureNat
    ; energyQ = energyNat
    ; epsilon = epsilonNat
    ; distortionBound = distortionBound
    }

record DeltaQuadraticOrderForCompatibility
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    distortionForCompatibility :
      DeltaQuadraticDistortionForCompatibility theorem dim≡15
    control : Nat → Nat
    monotone-up-to :
      ∀ s →
      DeltaQuadraticDistortionForCompatibility.pressureNat
        distortionForCompatibility
        s
      ≤
      control
        (DeltaQuadraticDistortionForCompatibility.energyNat
          distortionForCompatibility
          s)

  State : Set
  State =
    DeltaQuadraticDistortionForCompatibility.State
      distortionForCompatibility

  orderSurface : DeltaQuadraticOrder State
  orderSurface = record
    { pressureΔ =
        DeltaQuadraticDistortionForCompatibility.pressureNat
          distortionForCompatibility
    ; energyQ =
        DeltaQuadraticDistortionForCompatibility.energyNat
          distortionForCompatibility
    ; control = control
    ; monotone-up-to = monotone-up-to
    }

  controlledTransform :
    ControlledDeltaQuadraticTransform State
  controlledTransform = record
    { distortion =
        DeltaQuadraticDistortionForCompatibility.distortionSurface
          distortionForCompatibility
    ; order = orderSurface
    }

exactNatDistortion :
  ∀ {ℓS}
  {State : Set ℓS}
  (score : State → Nat) →
  DeltaQuadraticDistortion State
exactNatDistortion score = record
  { pressureΔ = score
  ; energyQ = score
  ; epsilon = λ _ → 0
  ; distortionBound = λ s → absDiff-refl≤0 (score s)
  }
