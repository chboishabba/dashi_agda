module DASHI.Physics.NavierStokes.DissipationNullComputationalCarrier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Harmonic/nullspace complexity boundary.
--
-- A dissipative operator can vanish on a carrier whose flow still supports a
-- nontrivial reachability/computation predicate.  This separates regularity and
-- dissipation estimates from computational predictability.

record Both (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

open Both public

record DissipationNullComputationalCarrier : Set₁ where
  field
    State : Set
    zeroState : State
    laplacian : State → State
    flow : State → State

    Harmonic : State → Set
    PerformsComputation : State → Set

    harmonicKillsLaplacian :
      ∀ x →
      Harmonic x →
      laplacian x ≡ zeroState

    computationalHarmonicWitness :
      Σ State
        (λ x → Both (Harmonic x) (PerformsComputation x))

open DissipationNullComputationalCarrier public

record ViscosityAction
  (C : DissipationNullComputationalCarrier) : Set₁ where
  field
    Viscosity : Set
    scale : Viscosity → State C → State C
    scaleZero :
      ∀ ν →
      scale ν (zeroState C) ≡ zeroState C

open ViscosityAction public

viscosityVanishesOnHarmonicCarrier :
  ∀ (C : DissipationNullComputationalCarrier) →
  (V : ViscosityAction C) →
  ∀ ν x →
  Harmonic C x →
  scale V ν (laplacian C x) ≡ zeroState C
viscosityVanishesOnHarmonicCarrier C V ν x harmonic
  rewrite harmonicKillsLaplacian C x harmonic =
  scaleZero V ν

------------------------------------------------------------------------
-- Source-specific cosymplectic/Hodge boundary.  This records exactly what the
-- cited steady-state construction does and does not promote.

record CosymplecticStationaryUniversalityBoundary : Set₁ where
  field
    Manifold Metric OneForm VectorField : Set

    hodgeAdmissibleMetric : Metric
    harmonicOneForm : OneForm
    stationaryField : VectorField

    nowhereVanishing : OneForm → Set
    harmonic : OneForm → Set
    turingCompleteFlow : VectorField → Set

    harmonicOneFormIsNowhereVanishing :
      nowhereVanishing harmonicOneForm
    harmonicOneFormIsHarmonic :
      harmonic harmonicOneForm
    stationaryFlowIsTuringComplete :
      turingCompleteFlow stationaryField

    viscosityIndependentSteadyState : Bool
    genericEuclideanUniversalityPromoted : Bool
    periodicThreeTorusUniversalityPromoted : Bool
    timeDependentUniversalityPromoted : Bool
    finiteTimeBlowupImplied : Bool

    viscosityIndependentSteadyStateIsTrue :
      viscosityIndependentSteadyState ≡ true
    genericEuclideanUniversalityPromotedIsFalse :
      genericEuclideanUniversalityPromoted ≡ false
    periodicThreeTorusUniversalityPromotedIsFalse :
      periodicThreeTorusUniversalityPromoted ≡ false
    timeDependentUniversalityPromotedIsFalse :
      timeDependentUniversalityPromoted ≡ false
    finiteTimeBlowupImpliedIsFalse :
      finiteTimeBlowupImplied ≡ false

open CosymplecticStationaryUniversalityBoundary public
