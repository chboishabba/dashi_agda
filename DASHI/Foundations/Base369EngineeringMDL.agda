module DASHI.Foundations.Base369EngineeringMDL where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (_≤_)

open import DASHI.Foundations.Base369CirclePhase using
  ( Expr369
  ; atom3
  ; atom6
  ; atom9
  ; _⊕_
  ; _⊗_
  ; fortyFiveExpr
  )

------------------------------------------------------------------------
-- Multi-axis engineering cost carrier.
--
-- None of these axes is silently identified with description length.  A
-- consumer supplies weights and, where needed, an empirical calibration.

record EngineeringCost : Set where
  constructor engineeringCost
  field
    windingCount : Nat
    phaseSwitchingOperations : Nat
    circuitComponents : Nat
    switchingComplexity : Nat
    harmonicSynthesisOperations : Nat
    controlProgramLength : Nat

open EngineeringCost public

zeroEngineeringCost : EngineeringCost
zeroEngineeringCost = engineeringCost 0 0 0 0 0 0

combineEngineeringCost : EngineeringCost → EngineeringCost → EngineeringCost
combineEngineeringCost x y =
  engineeringCost
    (windingCount x + windingCount y)
    (phaseSwitchingOperations x + phaseSwitchingOperations y)
    (circuitComponents x + circuitComponents y)
    (switchingComplexity x + switchingComplexity y)
    (harmonicSynthesisOperations x + harmonicSynthesisOperations y)
    (controlProgramLength x + controlProgramLength y)

record EngineeringCostWeights : Set where
  constructor engineeringCostWeights
  field
    windingWeight : Nat
    phaseSwitchWeight : Nat
    circuitComponentWeight : Nat
    switchingComplexityWeight : Nat
    harmonicSynthesisWeight : Nat
    controlProgramWeight : Nat

open EngineeringCostWeights public

unitEngineeringCostWeights : EngineeringCostWeights
unitEngineeringCostWeights =
  engineeringCostWeights 1 1 1 1 1 1

weightedEngineeringCost :
  EngineeringCostWeights →
  EngineeringCost →
  Nat
weightedEngineeringCost weights cost =
  windingWeight weights * windingCount cost +
  phaseSwitchWeight weights * phaseSwitchingOperations cost +
  circuitComponentWeight weights * circuitComponents cost +
  switchingComplexityWeight weights * switchingComplexity cost +
  harmonicSynthesisWeight weights * harmonicSynthesisOperations cost +
  controlProgramWeight weights * controlProgramLength cost

------------------------------------------------------------------------
-- A parameterised interpretation of Expr369 into engineering costs.
--
-- This keeps the generated-expression algebra separate from a physical
-- implementation.  Different winding layouts, switching networks, harmonic
-- synthesis plans, and controllers can supply different models.

record CostModel369 : Set where
  constructor costModel369
  field
    atom3Cost : EngineeringCost
    atom6Cost : EngineeringCost
    atom9Cost : EngineeringCost
    additionOverhead : EngineeringCost
    multiplicationOverhead : EngineeringCost

open CostModel369 public

costExpr369 : CostModel369 → Expr369 → EngineeringCost
costExpr369 model atom3 = atom3Cost model
costExpr369 model atom6 = atom6Cost model
costExpr369 model atom9 = atom9Cost model
costExpr369 model (x ⊕ y) =
  combineEngineeringCost
    (combineEngineeringCost
      (costExpr369 model x)
      (costExpr369 model y))
    (additionOverhead model)
costExpr369 model (x ⊗ y) =
  combineEngineeringCost
    (combineEngineeringCost
      (costExpr369 model x)
      (costExpr369 model y))
    (multiplicationOverhead model)

------------------------------------------------------------------------
-- A syntax-only benchmark model.
--
-- Atoms each consume one component/token.  Addition records one phase-switch
-- instruction; multiplication records one harmonic-synthesis instruction.
-- This is a checked accounting convention, not a calibrated circuit law.

atomSyntaxCost : EngineeringCost
atomSyntaxCost = engineeringCost 0 0 1 0 0 1

additionSyntaxOverhead : EngineeringCost
additionSyntaxOverhead = engineeringCost 0 1 0 1 0 1

multiplicationSyntaxOverhead : EngineeringCost
multiplicationSyntaxOverhead = engineeringCost 0 0 0 1 1 1

syntacticCostModel369 : CostModel369
syntacticCostModel369 =
  costModel369
    atomSyntaxCost
    atomSyntaxCost
    atomSyntaxCost
    additionSyntaxOverhead
    multiplicationSyntaxOverhead

fortyFive-phase-switch-count :
  phaseSwitchingOperations
    (costExpr369 syntacticCostModel369 fortyFiveExpr)
  ≡ 1
fortyFive-phase-switch-count = refl

fortyFive-harmonic-synthesis-count :
  harmonicSynthesisOperations
    (costExpr369 syntacticCostModel369 fortyFiveExpr)
  ≡ 1
fortyFive-harmonic-synthesis-count = refl

fortyFive-circuit-component-count :
  circuitComponents
    (costExpr369 syntacticCostModel369 fortyFiveExpr)
  ≡ 3
fortyFive-circuit-component-count = refl

fortyFive-control-program-length :
  controlProgramLength
    (costExpr369 syntacticCostModel369 fortyFiveExpr)
  ≡ 5
fortyFive-control-program-length = refl

------------------------------------------------------------------------
-- Joint engineering/MDL realisation score.

record PhaseRealisation : Set where
  constructor phaseRealisation
  field
    phaseGridSectors : Nat
    targetPhaseIndex : Nat
    implementationCost : EngineeringCost
    modelDescriptionLength : Nat
    residualDescriptionLength : Nat

open PhaseRealisation public

engineeringMDLScore :
  EngineeringCostWeights →
  PhaseRealisation →
  Nat
engineeringMDLScore weights candidate =
  weightedEngineeringCost weights (implementationCost candidate) +
  modelDescriptionLength candidate +
  residualDescriptionLength candidate

record NoWorseThan
  (weights : EngineeringCostWeights)
  (x y : PhaseRealisation) : Set where
  constructor noWorseThan
  field
    scoreBound :
      engineeringMDLScore weights x ≤
      engineeringMDLScore weights y

open NoWorseThan public

data Every {A : Set} (P : A → Set) : List A → Set where
  every[] : Every P []
  every∷ :
    ∀ {x xs} →
    P x →
    Every P xs →
    Every P (x ∷ xs)

record SelectedPhaseRealisation
  (weights : EngineeringCostWeights)
  (alternatives : List PhaseRealisation) : Set where
  constructor selectedPhaseRealisation
  field
    selected : PhaseRealisation
    selectedIsNoWorseThanEveryAlternative :
      Every (λ alternative → NoWorseThan weights selected alternative)
            alternatives

------------------------------------------------------------------------
-- Calibration and authority boundary.

record EngineeringMDLBoundary : Set where
  constructor engineeringMDLBoundary
  field
    sixCostAxesRepresented : Bool
    expressionAccountingChecked : Bool
    physicalWeightsCalibrated : Bool
    physicalWeightsCalibratedIsFalse :
      physicalWeightsCalibrated ≡ false
    circuitOptimalityPromoted : Bool
    circuitOptimalityPromotedIsFalse :
      circuitOptimalityPromoted ≡ false
    boundary : String

base369EngineeringMDLBoundary : EngineeringMDLBoundary
base369EngineeringMDLBoundary =
  engineeringMDLBoundary
    true
    true
    false
    refl
    false
    refl
    "Windings, phase switches, circuit components, switching complexity, harmonic synthesis, and control-program length are typed as separate costs. Physical weights, loss models, and global circuit optimality require measured calibration and domain-specific proofs."
