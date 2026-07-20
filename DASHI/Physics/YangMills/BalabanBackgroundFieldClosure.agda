module DASHI.Physics.YangMills.BalabanBackgroundFieldClosure where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- The semantic bridge after contraction.  Fixed-point uniqueness, criticality,
-- minimization, gauge-orbit uniqueness, and analytic dependence are separate.
------------------------------------------------------------------------

record FixedPointCriticalSemantics
    (State : Set)
    (criticalMap : State → State)
    (Critical : State → Set) : Set₁ where
  field
    fixedImpliesCritical : ∀ state → criticalMap state ≡ state → Critical state
    criticalImpliesFixed : ∀ state → Critical state → criticalMap state ≡ state

open FixedPointCriticalSemantics public

record CriticalMinimizerBridge
    (State : Set)
    (Critical Minimizer : State → Set) : Set₁ where
  field
    HessianCoerciveAtCritical : ∀ state → Critical state → Set
    hessianCoerciveAtCritical : ∀ state →
      (critical : Critical state) → HessianCoerciveAtCritical state critical
    criticalImpliesMinimizer : ∀ state →
      (critical : Critical state) →
      HessianCoerciveAtCritical state critical →
      Minimizer state

open CriticalMinimizerBridge public

record GaugeOrbitUniqueness
    (State Gauge : Set)
    (Critical : State → Set) : Set₁ where
  field
    gaugeAction : Gauge → State → State
    SameConstraintData : State → State → Set
    GaugeEquivalent : State → State → Set
    uniqueCriticalOrbit : ∀ left right →
      Critical left → Critical right → SameConstraintData left right →
      GaugeEquivalent left right

open GaugeOrbitUniqueness public

record AnalyticBackgroundDependence
    (Coarse State : Set) : Set₁ where
  field
    background : Coarse → State
    AnalyticAt : Coarse → Set
    UniformLocalityAt : Coarse → Set
    analytic : ∀ coarse → AnalyticAt coarse
    uniformLocality : ∀ coarse → UniformLocalityAt coarse

open AnalyticBackgroundDependence public

record BackgroundFieldClosure
    (Coarse State Gauge : Set)
    (criticalMap : State → State)
    (Critical Minimizer : State → Set) : Set₁ where
  field
    semantics : FixedPointCriticalSemantics State criticalMap Critical
    minimizerBridge : CriticalMinimizerBridge State Critical Minimizer
    orbitUniqueness : GaugeOrbitUniqueness State Gauge Critical
    analyticDependence : AnalyticBackgroundDependence Coarse State

open BackgroundFieldClosure public

assembleBackgroundFieldClosure :
  ∀ {Coarse State Gauge : Set}
    {criticalMap : State → State}
    {Critical Minimizer : State → Set} →
  FixedPointCriticalSemantics State criticalMap Critical →
  CriticalMinimizerBridge State Critical Minimizer →
  GaugeOrbitUniqueness State Gauge Critical →
  AnalyticBackgroundDependence Coarse State →
  BackgroundFieldClosure Coarse State Gauge criticalMap Critical Minimizer
assembleBackgroundFieldClosure semantics minimizer orbit analytic = record
  { semantics = semantics
  ; minimizerBridge = minimizer
  ; orbitUniqueness = orbit
  ; analyticDependence = analytic
  }
