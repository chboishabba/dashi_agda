module DASHI.Physics.Closure.CanonicalDynamicsLawTheorem where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; _≤_; _∸_; z≤n; s≤s)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI

ShiftConvergenceRateTarget : Set
ShiftConvergenceRateTarget =
  (s : PGFSI.ShiftFlowState) →
  Σ Nat
    (λ n →
      P0.iterate n PGFSI.shiftFlowEvolve s
        ≡
      SPTI.shiftHeldExitPoint
      ×
      n ≤ PGFSI.shiftFlowPotential s)

shiftConvergenceDescent :
  (s : PGFSI.ShiftFlowState) →
  PGFSI.shiftFlowPotential (PGFSI.shiftFlowEvolve s)
    <
  PGFSI.shiftFlowPotential s
  ⊎
  PGFSI.shiftFlowEvolve s ≡ s
shiftConvergenceDescent SPTI.shiftStartPoint =
  inj₁ (s≤s (s≤s z≤n))
shiftConvergenceDescent SPTI.shiftNextPoint =
  inj₁ (s≤s z≤n)
shiftConvergenceDescent SPTI.shiftHeldExitPoint =
  inj₂ refl

shiftConvergenceRateTarget : ShiftConvergenceRateTarget
shiftConvergenceRateTarget SPTI.shiftStartPoint =
  suc (suc zero) , (refl , s≤s (s≤s z≤n))
shiftConvergenceRateTarget SPTI.shiftNextPoint =
  suc zero , (refl , s≤s z≤n)
shiftConvergenceRateTarget SPTI.shiftHeldExitPoint =
  zero , (refl , z≤n)

canonicalShiftConvergenceBound :
  P0.ConvergenceBound {PGFSI.ShiftFlowState}
canonicalShiftConvergenceBound =
  record
    { K = PGFSI.shiftFlowEvolve
    ; mdl = PGFSI.shiftFlowPotential
    ; descent = shiftConvergenceDescent
    ; fixedPoint = SPTI.shiftHeldExitPoint
    ; converges = shiftConvergenceRateTarget
    }

record PointedMetricHorizonConvergenceTarget
  (S : Set)
  : Set₁ where
  field
    K : S → S
    fixedPoint : S
    distanceToFixedPoint : S → Nat
    horizon : S → Nat

    fixedPointStable :
      K fixedPoint ≡ fixedPoint

    horizonLands :
      ∀ x →
      P0.iterate (horizon x) K x ≡ fixedPoint

    rateToFixedPoint :
      ∀ t x →
      distanceToFixedPoint (P0.iterate t K x)
        ≤
      distanceToFixedPoint x ∸ t

shiftFlowDistanceToFixedPoint :
  PGFSI.ShiftFlowState → Nat
shiftFlowDistanceToFixedPoint = PGFSI.shiftFlowPotential

shiftFlowHorizon :
  PGFSI.ShiftFlowState → Nat
shiftFlowHorizon SPTI.shiftStartPoint = suc (suc zero)
shiftFlowHorizon SPTI.shiftNextPoint = suc zero
shiftFlowHorizon SPTI.shiftHeldExitPoint = zero

shiftFlowHorizonLands :
  (s : PGFSI.ShiftFlowState) →
  P0.iterate (shiftFlowHorizon s) PGFSI.shiftFlowEvolve s
    ≡
  SPTI.shiftHeldExitPoint
shiftFlowHorizonLands SPTI.shiftStartPoint = refl
shiftFlowHorizonLands SPTI.shiftNextPoint = refl
shiftFlowHorizonLands SPTI.shiftHeldExitPoint = refl

shiftFlowP0IteratesFrom2Held :
  (n : Nat) →
  (s : PGFSI.ShiftFlowState) →
  P0.iterate (suc (suc n)) PGFSI.shiftFlowEvolve s
    ≡
  SPTI.shiftHeldExitPoint
shiftFlowP0IteratesFrom2Held zero s =
  PGFSI.shiftFlowEvolutionCoherenceWitness s
shiftFlowP0IteratesFrom2Held (suc n) s
  rewrite shiftFlowP0IteratesFrom2Held n (PGFSI.shiftFlowEvolve s)
  = refl

shiftFlowPointedMetricRate :
  ∀ t s →
  shiftFlowDistanceToFixedPoint
    (P0.iterate t PGFSI.shiftFlowEvolve s)
    ≤
  shiftFlowDistanceToFixedPoint s ∸ t
shiftFlowPointedMetricRate zero SPTI.shiftStartPoint =
  s≤s (s≤s z≤n)
shiftFlowPointedMetricRate zero SPTI.shiftNextPoint =
  s≤s z≤n
shiftFlowPointedMetricRate zero SPTI.shiftHeldExitPoint =
  z≤n
shiftFlowPointedMetricRate (suc zero) SPTI.shiftStartPoint =
  s≤s z≤n
shiftFlowPointedMetricRate (suc zero) SPTI.shiftNextPoint =
  z≤n
shiftFlowPointedMetricRate (suc zero) SPTI.shiftHeldExitPoint =
  z≤n
shiftFlowPointedMetricRate (suc (suc n)) s
  rewrite shiftFlowP0IteratesFrom2Held n s
  = z≤n

canonicalShiftPointedMetricConvergenceTarget :
  PointedMetricHorizonConvergenceTarget PGFSI.ShiftFlowState
canonicalShiftPointedMetricConvergenceTarget =
  record
    { K = PGFSI.shiftFlowEvolve
    ; fixedPoint = SPTI.shiftHeldExitPoint
    ; distanceToFixedPoint = shiftFlowDistanceToFixedPoint
    ; horizon = shiftFlowHorizon
    ; fixedPointStable = PGFSI.shiftFlowHeldStableWitness
    ; horizonLands = shiftFlowHorizonLands
    ; rateToFixedPoint = shiftFlowPointedMetricRate
    }

record RealizationIndexedPointedMetricConvergenceTarget : Set₁ where
  field
    Realization : Set
    State : Set

    firstRealization : Realization
    secondRealization : Realization
    realizationsNontrivial :
      firstRealization P0.≢ secondRealization

    realizationOf : State → Realization
    underlyingState : State → PGFSI.ShiftFlowState
    liftState : Realization → PGFSI.ShiftFlowState → State

    K : State → State
    fixedPointAt : Realization → State
    distanceToFixedPoint : State → Nat
    horizon : State → Nat

    lift-realization :
      ∀ r s → realizationOf (liftState r s) ≡ r

    lift-underlying :
      ∀ r s → underlyingState (liftState r s) ≡ s

    evolutionPreservesRealization :
      ∀ x → realizationOf (K x) ≡ realizationOf x

    evolutionCoherentWithShiftFlow :
      ∀ x →
      underlyingState (K x) ≡
      PGFSI.shiftFlowEvolve (underlyingState x)

    metricInvariant :
      ∀ x →
      distanceToFixedPoint x ≡
      shiftFlowDistanceToFixedPoint (underlyingState x)

    horizonInvariant :
      ∀ x → horizon x ≡ shiftFlowHorizon (underlyingState x)

    fixedPointStableAt :
      ∀ r → K (fixedPointAt r) ≡ fixedPointAt r

    horizonLandsAt :
      ∀ x →
      P0.iterate (horizon x) K x ≡ fixedPointAt (realizationOf x)

    rateToFixedPointAt :
      ∀ t x →
      distanceToFixedPoint (P0.iterate t K x)
        ≤
      distanceToFixedPoint x ∸ t

RealizedShiftFlowState : Set
RealizedShiftFlowState =
  Nat × PGFSI.ShiftFlowState

realizedShiftFlowEvolve :
  RealizedShiftFlowState → RealizedShiftFlowState
realizedShiftFlowEvolve (r , s) =
  r , PGFSI.shiftFlowEvolve s

realizedShiftFlowDistanceToFixedPoint :
  RealizedShiftFlowState → Nat
realizedShiftFlowDistanceToFixedPoint (_ , s) =
  shiftFlowDistanceToFixedPoint s

realizedShiftFlowHorizon :
  RealizedShiftFlowState → Nat
realizedShiftFlowHorizon (_ , s) =
  shiftFlowHorizon s

realizedShiftFlowFixedPointAt :
  Nat → RealizedShiftFlowState
realizedShiftFlowFixedPointAt r =
  r , SPTI.shiftHeldExitPoint

zero≢one : zero P0.≢ suc zero
zero≢one ()

realizedShiftFlowHorizonLands :
  ∀ x →
  P0.iterate (realizedShiftFlowHorizon x) realizedShiftFlowEvolve x
    ≡
  realizedShiftFlowFixedPointAt
    (Data.Product.proj₁ x)
realizedShiftFlowHorizonLands (r , SPTI.shiftStartPoint) = refl
realizedShiftFlowHorizonLands (r , SPTI.shiftNextPoint) = refl
realizedShiftFlowHorizonLands (r , SPTI.shiftHeldExitPoint) = refl

realizedShiftFlowP0IteratesFrom2Held :
  (n : Nat) →
  (x : RealizedShiftFlowState) →
  P0.iterate (suc (suc n)) realizedShiftFlowEvolve x
    ≡
  realizedShiftFlowFixedPointAt
    (Data.Product.proj₁ x)
realizedShiftFlowP0IteratesFrom2Held zero (r , s)
  rewrite PGFSI.shiftFlowEvolutionCoherenceWitness s
  = refl
realizedShiftFlowP0IteratesFrom2Held (suc n) x
  rewrite realizedShiftFlowP0IteratesFrom2Held n (realizedShiftFlowEvolve x)
  = refl

realizedShiftFlowPointedMetricRate :
  ∀ t x →
  realizedShiftFlowDistanceToFixedPoint
    (P0.iterate t realizedShiftFlowEvolve x)
    ≤
  realizedShiftFlowDistanceToFixedPoint x ∸ t
realizedShiftFlowPointedMetricRate zero (r , SPTI.shiftStartPoint) =
  s≤s (s≤s z≤n)
realizedShiftFlowPointedMetricRate zero (r , SPTI.shiftNextPoint) =
  s≤s z≤n
realizedShiftFlowPointedMetricRate zero (r , SPTI.shiftHeldExitPoint) =
  z≤n
realizedShiftFlowPointedMetricRate (suc zero) (r , SPTI.shiftStartPoint) =
  s≤s z≤n
realizedShiftFlowPointedMetricRate (suc zero) (r , SPTI.shiftNextPoint) =
  z≤n
realizedShiftFlowPointedMetricRate (suc zero) (r , SPTI.shiftHeldExitPoint) =
  z≤n
realizedShiftFlowPointedMetricRate (suc (suc n)) x
  rewrite realizedShiftFlowP0IteratesFrom2Held n x
  = z≤n

canonicalShiftRealizationMetricConvergenceFamily :
  RealizationIndexedPointedMetricConvergenceTarget
canonicalShiftRealizationMetricConvergenceFamily =
  record
    { Realization = Nat
    ; State = RealizedShiftFlowState
    ; firstRealization = zero
    ; secondRealization = suc zero
    ; realizationsNontrivial = zero≢one
    ; realizationOf = Data.Product.proj₁
    ; underlyingState = Data.Product.proj₂
    ; liftState = λ r s → r , s
    ; K = realizedShiftFlowEvolve
    ; fixedPointAt = realizedShiftFlowFixedPointAt
    ; distanceToFixedPoint = realizedShiftFlowDistanceToFixedPoint
    ; horizon = realizedShiftFlowHorizon
    ; lift-realization = λ _ _ → refl
    ; lift-underlying = λ _ _ → refl
    ; evolutionPreservesRealization = λ _ → refl
    ; evolutionCoherentWithShiftFlow = λ _ → refl
    ; metricInvariant = λ _ → refl
    ; horizonInvariant = λ _ → refl
    ; fixedPointStableAt = λ _ → refl
    ; horizonLandsAt = realizedShiftFlowHorizonLands
    ; rateToFixedPointAt = realizedShiftFlowPointedMetricRate
    }

record CanonicalDynamicsLawTheorem : Setω where
  field
    canonicalConsumer :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    canonicalDynamics : DC.DynamicalClosure
    canonicalDynamicsStatus : DCS.DynamicalClosureStatus
    canonicalDynamicsWitness : DCW.DynamicalClosureWitness
    propagationLaw :
      DCS.DynamicalClosureStatus.propagation canonicalDynamicsStatus
      ≡ DCS.fiberBackedPropagation
    causalAdmissibilityLaw :
      DCS.DynamicalClosureStatus.causalAdmissibility canonicalDynamicsStatus
      ≡ DCS.seamBackedCausalAdmissibility
    conservedQuantityLaw :
      DCS.DynamicalClosureStatus.monotoneQuantity canonicalDynamicsStatus
      ≡ DCS.mdlLyapunovAndFejer
    continuumLimitLaw :
      DCS.DynamicalClosureStatus.effectiveGeometry canonicalDynamicsStatus
      ≡ DCS.quadraticPolarizationAndOrthogonality
    realizationIndependentProofShape : DCW.DynamicalClosureWitness
    boundedConvergenceRate :
      P0.ConvergenceBound {PGFSI.ShiftFlowState}
    concreteConvergenceRateTarget :
      ShiftConvergenceRateTarget
    pointedMetricConvergenceTarget :
      PointedMetricHorizonConvergenceTarget PGFSI.ShiftFlowState
    realizationMetricConvergenceFamily :
      RealizationIndexedPointedMetricConvergenceTarget

canonicalDynamicsLawTheorem : CanonicalDynamicsLawTheorem
canonicalDynamicsLawTheorem =
  record
    { canonicalConsumer =
        CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    ; canonicalDynamics =
        CSDC.SpinDiracConsumerFromMinimal.dynamics
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; canonicalDynamicsStatus =
        CSDC.SpinDiracConsumerFromMinimal.dynamicsStatus
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; canonicalDynamicsWitness =
        CSDC.SpinDiracConsumerFromMinimal.dynamicsWitness
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; propagationLaw = refl
    ; causalAdmissibilityLaw = refl
    ; conservedQuantityLaw = refl
    ; continuumLimitLaw = refl
    ; realizationIndependentProofShape =
        CSDC.SpinDiracConsumerFromMinimal.dynamicsWitness
          (CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift)
    ; boundedConvergenceRate = canonicalShiftConvergenceBound
    ; concreteConvergenceRateTarget = shiftConvergenceRateTarget
    ; pointedMetricConvergenceTarget =
        canonicalShiftPointedMetricConvergenceTarget
    ; realizationMetricConvergenceFamily =
        canonicalShiftRealizationMetricConvergenceFamily
    }
