module DASHI.Physics.YangMills.BalabanBackgroundFieldClosure where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Background-field closure, B1--B8.
--
-- This module makes the full analytic wall proof-relevant.  In particular it
-- does not identify a finite numerical experiment with a volume-, scale-,
-- background-, and patch-uniform theorem.  The analytic estimates are explicit
-- fields; all implications and the final assembly are machine checked.
------------------------------------------------------------------------

record TwoSidedInverse {State : Set}
    (operator inverse : State → State) : Set where
  field
    inverseLeft : ∀ state → inverse (operator state) ≡ state
    inverseRight : ∀ state → operator (inverse state) ≡ state

open TwoSidedInverse public

------------------------------------------------------------------------
-- B1--B2: constrained coercivity and the actual patch Green inverse.
------------------------------------------------------------------------

record UniformConstrainedHessianCoercivity
    (Index State Scalar Bound : Set) : Set₁ where
  field
    hessian : Index → State → State
    green : Index → State → State
    GaugeFixedTangent : Index → State → Set
    inner : State → State → Scalar
    normSq : State → Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Scalar → Set
    Positive : Bound → Set
    cH : Bound

    cHPositive : Positive cH
    uniformConstrainedHessianCoercive : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual (scale cH (normSq state))
        (inner state (hessian index state))

    constrainedHessianInvertible : ∀ index →
      TwoSidedInverse (hessian index) (green index)

    GaugeZeroModesRemoved : Index → Set
    BlockAverageModesRemoved : Index → Set
    ResidualGaugeModesRemoved : Index → Set
    BoundaryDegeneraciesRemoved : Index → Set
    gaugeZeroModesRemoved : ∀ index → GaugeZeroModesRemoved index
    blockAverageModesRemoved : ∀ index → BlockAverageModesRemoved index
    residualGaugeModesRemoved : ∀ index → ResidualGaugeModesRemoved index
    boundaryDegeneraciesRemoved : ∀ index → BoundaryDegeneraciesRemoved index

open UniformConstrainedHessianCoercivity public

------------------------------------------------------------------------
-- B3: weighted Green and derivative Green estimates.
------------------------------------------------------------------------

record UniformWeightedGreenEstimates
    (Index State Bound : Set) : Set₁ where
  field
    green : Index → State → State
    gradientGreen : Index → State → State
    secondGradientGreen : Index → State → State
    weightedNorm : Bound → State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    muG greenUpper gradientGreenUpper secondGradientGreenUpper : Bound

    uniformWeightedGreenBound : ∀ index source →
      LessEqual
        (weightedNorm muG (green index source))
        (multiply greenUpper (weightedNorm muG source))

    uniformWeightedGradientGreenBound : ∀ index source →
      LessEqual
        (weightedNorm muG (gradientGreen index source))
        (multiply gradientGreenUpper (weightedNorm muG source))

    uniformWeightedSecondGradientGreenBound : ∀ index source →
      LessEqual
        (weightedNorm muG (secondGradientGreen index source))
        (multiply secondGradientGreenUpper (weightedNorm muG source))

open UniformWeightedGreenEstimates public

------------------------------------------------------------------------
-- B4: patchwise random-walk/Neumann representation.
------------------------------------------------------------------------

record UniformPatchwiseRandomWalk
    (Index State Bound : Set) : Set₁ where
  field
    green localParametrix residual : Index → State → State
    residualPower : Index → Nat → State → State
    partialRandomWalk : Index → Nat → State → State
    randomWalkTail : Index → Nat → State → State
    weightedNorm : Bound → State → Bound
    multiply : Bound → Bound → Bound
    power : Bound → Nat → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set

    muG randomWalkRatio randomWalkUpper : Bound

    localParametrixErrorBound : ∀ index source →
      LessEqual
        (weightedNorm muG (residual index source))
        (multiply randomWalkRatio (weightedNorm muG source))

    randomWalkResidualStrict : StrictlyBelowOne randomWalkRatio

    neumannSeriesRepresentsGreen : ∀ index truncation source →
      green index source ≡
        partialRandomWalk index truncation source

    randomWalkTailUniform : ∀ index truncation source →
      LessEqual
        (weightedNorm muG (randomWalkTail index truncation source))
        (multiply
          (multiply randomWalkUpper (power randomWalkRatio truncation))
          (weightedNorm muG source))

    BulkPatchControl BoundaryPatchControl ScaleInterfaceControl
      CornerPatchControl NestedRestrictionControl : Index → Set
    bulkPatchControl : ∀ index → BulkPatchControl index
    boundaryPatchControl : ∀ index → BoundaryPatchControl index
    scaleInterfaceControl : ∀ index → ScaleInterfaceControl index
    cornerPatchControl : ∀ index → CornerPatchControl index
    nestedRestrictionControl : ∀ index → NestedRestrictionControl index

open UniformPatchwiseRandomWalk public

------------------------------------------------------------------------
-- B5: nonlinear remainder on one common critical ball.
------------------------------------------------------------------------

record UniformNonlinearRemainderEstimate
    (Index State Bound : Set) : Set₁ where
  field
    nonlinear : Index → State → State
    subtract : State → State → State
    norm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    InCriticalBall : Index → State → Set
    nonlinearUpper : Bound

    uniformNonlinearRemainderLipschitz : ∀ index left right →
      InCriticalBall index left →
      InCriticalBall index right →
      LessEqual
        (norm (subtract (nonlinear index left) (nonlinear index right)))
        (multiply nonlinearUpper (norm (subtract left right)))

    BCHHigherControl CommutatorControl ParallelTransportControl
      BackgroundDerivativeControl GaugeFixingControl BlockConstraintControl
      ChartChangeControl : Index → Set
    bchHigherControl : ∀ index → BCHHigherControl index
    commutatorControl : ∀ index → CommutatorControl index
    parallelTransportControl : ∀ index → ParallelTransportControl index
    backgroundDerivativeControl : ∀ index → BackgroundDerivativeControl index
    gaugeFixingControl : ∀ index → GaugeFixingControl index
    blockConstraintControl : ∀ index → BlockConstraintControl index
    chartChangeControl : ∀ index → ChartChangeControl index

open UniformNonlinearRemainderEstimate public

------------------------------------------------------------------------
-- B6--B7: self-map and strict common scalar budget.
------------------------------------------------------------------------

record CriticalBallBudget
    (Index State Bound : Set) : Set₁ where
  field
    criticalMap : Index → State → State
    InCriticalBall : Index → State → Set
    zero : State
    norm : State → Bound
    radius greenUpper nonlinearUpper rhoG : Bound
    multiply add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set

    criticalMapPreservesBall : ∀ index state →
      InCriticalBall index state →
      InCriticalBall index (criticalMap index state)

    criticalMapAtZeroBudget : ∀ index →
      LessEqual
        (add (norm (criticalMap index zero)) (multiply rhoG radius))
        radius

    greenTimesNonlinearBelowRho :
      LessEqual (multiply greenUpper nonlinearUpper) rhoG

    rhoGStrict : StrictlyBelowOne rhoG

open CriticalBallBudget public

------------------------------------------------------------------------
-- B8: fixed point, Euler--Lagrange, minimizer, gauge uniqueness, and
-- analytic dependence.  The original API is retained below.
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

------------------------------------------------------------------------
-- Complete indexed closure package.
------------------------------------------------------------------------

record BackgroundFieldAnalyticClosure
    (Index Coarse State Scalar Bound Gauge : Set)
    (criticalMap₀ : State → State)
    (Critical Minimizer : State → Set) : Set₁ where
  field
    coerciveHessian :
      UniformConstrainedHessianCoercivity Index State Scalar Bound
    weightedGreen : UniformWeightedGreenEstimates Index State Bound
    randomWalk : UniformPatchwiseRandomWalk Index State Bound
    nonlinearRemainder : UniformNonlinearRemainderEstimate Index State Bound
    ballBudget : CriticalBallBudget Index State Bound
    criticalSemantics :
      BackgroundFieldClosure Coarse State Gauge criticalMap₀ Critical Minimizer

open BackgroundFieldAnalyticClosure public

assembleBackgroundFieldAnalyticClosure :
  ∀ {Index Coarse State Scalar Bound Gauge : Set}
    {criticalMap₀ : State → State}
    {Critical Minimizer : State → Set} →
  UniformConstrainedHessianCoercivity Index State Scalar Bound →
  UniformWeightedGreenEstimates Index State Bound →
  UniformPatchwiseRandomWalk Index State Bound →
  UniformNonlinearRemainderEstimate Index State Bound →
  CriticalBallBudget Index State Bound →
  BackgroundFieldClosure Coarse State Gauge criticalMap₀ Critical Minimizer →
  BackgroundFieldAnalyticClosure
    Index Coarse State Scalar Bound Gauge criticalMap₀ Critical Minimizer
assembleBackgroundFieldAnalyticClosure coercive green random nonlinear ball semantic = record
  { coerciveHessian = coercive
  ; weightedGreen = green
  ; randomWalk = random
  ; nonlinearRemainder = nonlinear
  ; ballBudget = ball
  ; criticalSemantics = semantic
  }

backgroundFieldClosureAssemblyLevel : ProofLevel
backgroundFieldClosureAssemblyLevel = machineChecked

backgroundFieldCoercivityInputLevel : ProofLevel
backgroundFieldCoercivityInputLevel = conjectural

backgroundFieldWeightedGreenInputLevel : ProofLevel
backgroundFieldWeightedGreenInputLevel = conjectural

backgroundFieldRandomWalkInputLevel : ProofLevel
backgroundFieldRandomWalkInputLevel = conjectural

backgroundFieldNonlinearInputLevel : ProofLevel
backgroundFieldNonlinearInputLevel = conjectural

backgroundFieldSemanticInputLevel : ProofLevel
backgroundFieldSemanticInputLevel = conditional
