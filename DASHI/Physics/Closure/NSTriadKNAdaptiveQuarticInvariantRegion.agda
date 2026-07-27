module DASHI.Physics.Closure.NSTriadKNAdaptiveQuarticInvariantRegion where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Jean-Pierre Aubin.
-- Title: "Viability Theory".
-- Venue/year: Modern Birkhauser Classics, Birkhauser, 2009.
-- DOI: 10.1007/978-0-8176-4910-4.
-- Uses: Chapters 4, 8 and 12 on viability, invariance and Lyapunov functions.
-- Relationship: adapts inward-pointing invariance to finite Galerkin flow.
-- The concentrated/transition/diffuse cover and finite-chart-minimum route
-- are DASHI-original synthesis.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

data SpectralRegime : Set where
  zero concentrated transition diffuse : SpectralRegime

record AdaptiveQuarticInvariantRegion
    {c t s h r : Level} :
    Set (lsuc (c ⊔ t ⊔ s ⊔ h ⊔ r)) where
  field
    Cutoff : Set c
    Time : Set t
    State : Set s
    Chart : Set h
    Scalar : Set r

    initialTime : Time
    _≤T_ : Time → Time → Set t
    zeroScalar : Scalar
    _≤S_ _<S_ : Scalar → Scalar → Set r

    solution : Cutoff → Time → State
    zeroTangent : State
    velocityField : Cutoff → State → State
    selectChart : Cutoff → State → Chart
    regime : Cutoff → State → SpectralRegime

    IsZero NonZero : State → Set
    Concentrated Transition Diffuse : Cutoff → State → Set

    spectralRegimeExhaustive : ∀ N state →
      IsZero state
      ⊎ (Concentrated N state
      ⊎ (Transition N state ⊎ Diffuse N state))

    RegimeHolds : SpectralRegime → Cutoff → State → Set
    zeroRegimeMeaning : ∀ N state →
      RegimeHolds zero N state → IsZero state
    concentratedRegimeMeaning : ∀ N state →
      RegimeHolds concentrated N state → Concentrated N state
    transitionRegimeMeaning : ∀ N state →
      RegimeHolds transition N state → Transition N state
    diffuseRegimeMeaning : ∀ N state →
      RegimeHolds diffuse N state → Diffuse N state

    spectralRegimesMutuallyExclusive : ∀ first second N state →
      (first ≡ second → ⊥) →
      RegimeHolds first N state →
      RegimeHolds second N state →
      ⊥

    zeroStateIsEquilibrium : ∀ N state →
      IsZero state →
      velocityField N state ≡ zeroTangent

    ChartValid : Chart → Cutoff → State → Set
    concentratedStateHasValidChart : ∀ N state →
      Concentrated N state →
      ChartValid (selectChart N state) N state
    transitionStateHasValidChart : ∀ N state →
      Transition N state →
      ChartValid (selectChart N state) N state
    diffuseStateHasValidChart : ∀ N state →
      Diffuse N state →
      ChartValid (selectChart N state) N state
    selectedChartAlwaysValidForNonzeroState : ∀ N state →
      NonZero state →
      ChartValid (selectChart N state) N state

    Symmetry : Set h
    actState : Symmetry → State → State
    actChart : Symmetry → Chart → Chart
    chartSelectionEquivariant : ∀ symmetry N state →
      selectChart N (actState symmetry state)
      ≡ actChart symmetry (selectChart N state)
    ChartDecision : Cutoff → State → Chart → Set
    selectedChartSatisfiesDecision : ∀ N state →
      ChartDecision N state (selectChart N state)
    chartTieBreakingDeterministic : ∀ N state chart →
      ChartDecision N state chart →
      chart ≡ selectChart N state

    SolutionContinuouslyDifferentiable :
      Cutoff → (Time → State) → Set
    galerkinSolutionContinuouslyDifferentiable : ∀ N →
      SolutionContinuouslyDifferentiable N (solution N)

    lyapunovValue : Chart → Cutoff → State → Scalar
    upperDiniDerivative : Chart → Cutoff → State → Scalar
    LocallyLipschitz : (State → Scalar) → Set
    chartBarrierLocallyLipschitz : ∀ chart N →
      LocallyLipschitz (lyapunovValue chart N)

    Admissible : Cutoff → State → Set
    Boundary : Chart → Cutoff → State → Set
    Dangerous : Chart → Cutoff → State → Set

    jointDominationImpliesBoundaryDiniNegative : ∀ chart N state →
      ChartValid chart N state →
      Boundary chart N state →
      NonZero state →
      Dangerous chart N state →
      _<S_ (upperDiniDerivative chart N state) zeroScalar

    ChartValidOnInterval : Chart → Cutoff → Time → Time → Set
    chartValidUntilExitOrSwitch : ∀ chart N start finish →
      _≤T_ start finish →
      ChartValidOnInterval chart N start finish

    fixedChartNoFirstExit : ∀ chart N start finish →
      ChartValidOnInterval chart N start finish →
      Admissible N (solution N start) →
      Admissible N (solution N finish)

    SwitchAllowed : Chart → Chart → Cutoff → State → Set
    SwitchEvent : Set s
    oldSwitchChart newSwitchChart : SwitchEvent → Chart
    switchCutoff : SwitchEvent → Cutoff
    preSwitchState postSwitchState : SwitchEvent → State
    switchPreservesPhysicalState : ∀ event →
      preSwitchState event ≡ postSwitchState event
    switchingDoesNotIncreaseLyapunovValue : ∀ old new N state →
      SwitchAllowed old new N state →
      _≤S_
        (lyapunovValue new N state)
        (lyapunovValue old N state)

    FiniteChartFamily : Cutoff → Set
    selectedBarrier : Cutoff → State → Scalar
    selectedBarrierIsFiniteChartMinimum : ∀ N state →
      FiniteChartFamily N →
      selectedBarrier N state
      ≡ lyapunovValue (selectChart N state) N state
    selectedBarrierBelowEveryValidChart : ∀ N state chart →
      FiniteChartFamily N →
      ChartValid chart N state →
      _≤S_
        (selectedBarrier N state)
        (lyapunovValue chart N state)

    ActiveChart : Chart → Cutoff → State → Set
    activeChartsAllPointInward : ∀ chart N state →
      ActiveChart chart N state →
      Boundary chart N state →
      _≤S_ (upperDiniDerivative chart N state) zeroScalar

    selectedUpperDiniDerivative : Cutoff → State → Scalar
    minimumBarrierUpperDiniBound : ∀ N state chart →
      ActiveChart chart N state →
      _≤S_
        (selectedUpperDiniDerivative N state)
        (upperDiniDerivative chart N state)

    zenoSwitchingHarmlessForCommonBarrier : ∀ N state →
      _≤S_
        (selectedUpperDiniDerivative N state)
        zeroScalar

    InvariantAlong : Cutoff → (Time → State) → Set
    adaptiveBarrierNoFirstExit : ∀ N →
      Admissible N (solution N initialTime) →
      InvariantAlong N (solution N)

open AdaptiveQuarticInvariantRegion public

adaptiveAdmissibleUnionInvariant :
  ∀ {c t s h r}
    (R : AdaptiveQuarticInvariantRegion {c} {t} {s} {h} {r})
    (N : Cutoff R) →
  Admissible R N (solution R N (initialTime R)) →
  InvariantAlong R N (solution R N)
adaptiveAdmissibleUnionInvariant R N =
  adaptiveBarrierNoFirstExit R N

exhaustiveAdaptiveInvariance :
  ∀ {c t s h r}
    (R : AdaptiveQuarticInvariantRegion {c} {t} {s} {h} {r})
    (N : Cutoff R) →
  Admissible R N (solution R N (initialTime R)) →
  InvariantAlong R N (solution R N)
exhaustiveAdaptiveInvariance = adaptiveAdmissibleUnionInvariant

adaptiveInvariantRegionArchitectureImplemented : Bool
adaptiveInvariantRegionArchitectureImplemented = true

adaptiveInvariantRegionArchitectureImplementedIsTrue :
  adaptiveInvariantRegionArchitectureImplemented ≡ true
adaptiveInvariantRegionArchitectureImplementedIsTrue = refl

exhaustiveAdaptiveInvarianceClosed : Bool
exhaustiveAdaptiveInvarianceClosed = false

exhaustiveAdaptiveInvarianceClosedIsFalse :
  exhaustiveAdaptiveInvarianceClosed ≡ false
exhaustiveAdaptiveInvarianceClosedIsFalse = refl
