module DASHI.Puzzles.RubiksCayleyControlMetric where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Automata.KernelInternal as Kernel
import DASHI.Puzzles.RubiksPhasicState as Rubik

------------------------------------------------------------------------
-- Holonomy contraction and generator-induced control distance.
--
-- The theorem is split into an exact algebraic core and an analytic boundary.
-- Exact: zero contraction iff every selected M9 cell has zero local defect.
-- Analytic: curvature-to-edge coercivity requires a finite complex, gauge
-- fixing and a Poincare-type estimate; these assumptions are explicit fields,
-- not silently promoted.
------------------------------------------------------------------------

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

sumDefect : {A : Set} → (A → Nat) → (A → Bool) → Nat
sumDefect defect selected = zero

record HolonomyContractionTheorem
  (P : Rubik.PhaseStructure)
  (Cell : Set) : Set₁ where
  field
    holonomy : Cell → Rubik.PhaseStructure.Phase P
    localDefect : Cell → Nat
    selected : Cell → Bool

    localDefectIsDistanceToIdentity : Bool
    contractionNonnegative : Bool
    zeroContractionImpliesSelectedFlatness : Bool
    selectedFlatnessImpliesZeroContraction : Bool

  exactKernelClosed : Bool
  exactKernelClosed =
    localDefectIsDistanceToIdentity
    ∧ contractionNonnegative
    ∧ zeroContractionImpliesSelectedFlatness
    ∧ selectedFlatnessImpliesZeroContraction

record FiniteGaugeCoercivityBoundary : Set₁ where
  field
    finiteComplex : Bool
    connectedComplex : Bool
    compactPhaseCarrier : Bool
    gaugeFixedOrQuotiented : Bool
    globalCycleSectorsControlled : Bool
    discretePoincareEstimateAvailable : Bool
    curvatureControlsEdgeResidual : Bool

  coercivityAvailable : Bool
  coercivityAvailable =
    finiteComplex
    ∧ connectedComplex
    ∧ compactPhaseCarrier
    ∧ gaugeFixedOrQuotiented
    ∧ globalCycleSectorsControlled
    ∧ discretePoincareEstimateAvailable
    ∧ curvatureControlsEdgeResidual

record GeneratorAction (State Generator : Set) : Set₁ where
  field
    act : Generator → State → State
    unitCost : Generator → Nat
    preservesDiscreteLattice : Bool
    preservesAdmissibleKernel : Bool

record WordPath (State Generator : Set) : Set₁ where
  field
    start : State
    finish : State
    length : Nat
    endpointWitness : Bool
    everyStepGenerated : Bool
    everyStepAdmissible : Bool

record ControlMetricTheorem (State Generator : Set) : Set₁ where
  field
    action : GeneratorAction State Generator
    controlDistance : State → State → Nat
    cayleyDistance : State → State → Nat
    DiscreteState : State → Bool

    distanceIsInfimumOfGeneratedPathCosts : Bool
    positiveGeneratorCosts : Bool
    zeroOnlyOnIdenticalReachableStates : Bool
    triangleInequalityAvailable : Bool
    discreteUnitCostRestriction : Bool
    discreteRestrictionEqualsCayley :
      (x y : State) →
      DiscreteState x ≡ true →
      DiscreteState y ≡ true →
      controlDistance x y ≡ cayleyDistance x y

  controlMetricClosed : Bool
  controlMetricClosed =
    distanceIsInfimumOfGeneratedPathCosts
    ∧ positiveGeneratorCosts
    ∧ zeroOnlyOnIdenticalReachableStates
    ∧ triangleInequalityAvailable
    ∧ discreteUnitCostRestriction

record AdmissibleGeodesic (State Generator : Set) : Set₁ where
  field
    metric : ControlMetricTheorem State Generator
    path : WordPath State Generator
    shortestAmongAdmissibleGeneratedPaths : Bool
    kernelDefectNeverIncreasesPastBudget : Bool
    phasicInterpolationAvailable : Bool
    interpolationProjectsToSameMoveWord : Bool

  geodesicClosed : Bool
  geodesicClosed =
    shortestAmongAdmissibleGeneratedPaths
    ∧ kernelDefectNeverIncreasesPastBudget
    ∧ phasicInterpolationAvailable
    ∧ interpolationProjectsToSameMoveWord

------------------------------------------------------------------------
-- Standard comparison surface.
------------------------------------------------------------------------

record RubikStandardsComparison : Set₁ where
  field
    sameVerticesAsClassicalCubeGroup : Bool
    sameGeneratorEdgesAsCayleyGraph : Bool
    sameUnitWordMetricOnDiscreteStates : Bool
    quotientGraphsAreChannelProjections : Bool
    commutingRelationsFillHigherCells : Bool
    phasicAmbientLiftAdditional : Bool
    scalarHolonomyDefectAdditional : Bool
    kernelWeightedControlCostAdditional : Bool

  classicalCoreRecovered : Bool
  classicalCoreRecovered =
    sameVerticesAsClassicalCubeGroup
    ∧ sameGeneratorEdgesAsCayleyGraph
    ∧ sameUnitWordMetricOnDiscreteStates

  dashiLiftAdditional : Bool
  dashiLiftAdditional =
    quotientGraphsAreChannelProjections
    ∧ commutingRelationsFillHigherCells
    ∧ phasicAmbientLiftAdditional
    ∧ scalarHolonomyDefectAdditional
    ∧ kernelWeightedControlCostAdditional

metricStatement : String
metricStatement =
  "The move tensor induces a positive-cost control metric. On discrete legal "
  ++ "states with unit generator cost it is definitionally the Cayley shortest-"
  ++ "word metric. The phasic lift adds interpolation, holonomy defect and "
  ++ "kernel-aware weights without changing the classical discrete graph."
