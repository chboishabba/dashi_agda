module DASHI.Dynamics.TriadicResidualRechartDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.JChartSuccessorBoundary as Charts
import DASHI.Topology.TetrationalGateField as Gates

------------------------------------------------------------------------
-- Remainder classification drives refinement rather than being discarded.

data ResidualKind : Set where
  negligibleResidual harmonicResidual fineScaleResidual gluingFailureResidual : ResidualKind

data ResidualAction : Set where
  acceptCurrentModel openSpectralBlock deepenQuotient rechartModel : ResidualAction

residualAction : ResidualKind → ResidualAction
residualAction negligibleResidual = acceptCurrentModel
residualAction harmonicResidual = openSpectralBlock
residualAction fineScaleResidual = deepenQuotient
residualAction gluingFailureResidual = rechartModel

record ChartedResidualState : Set where
  constructor chartedResidualState
  field
    chart : Charts.ChartIndex
    residual : ResidualKind
    gateField : Gates.GateField
    history : List String

open ChartedResidualState public

stateAtStar : ChartedResidualState
stateAtStar =
  chartedResidualState
    (Charts.chart 10)
    gluingFailureResidual
    Gates.canonicalMixedGateField
    ("current chart no longer glues all local sections" ∷ [])

rechart : ChartedResidualState → ChartedResidualState
rechart s with residual s
... | negligibleResidual = s
... | harmonicResidual = s
... | fineScaleResidual = s
... | gluingFailureResidual =
  chartedResidualState
    (Charts.nextChart (chart s))
    negligibleResidual
    (gateField s)
    ("recharted after gluing failure" ∷ history s)

starRechartsToEleven : chart (rechart stateAtStar) ≡ Charts.chart 11
starRechartsToEleven = refl

------------------------------------------------------------------------
-- Generic conditioned update and proof obligations.

record ConditionedKernelDynamics : Set₁ where
  field
    State Context Noise Defect : Set
    forwardKernel : State → Context → Noise → State
    reverseKernel : State → Context → State
    defect : State → Context → Defect
    _≤defect_ : Defect → Defect → Set
    reverseNonincrease :
      ∀ state context →
      defect (reverseKernel state context) context ≤defect defect state context

record ProjectionResidualLane : Set₁ where
  field
    Hidden Observed Residual : Set
    project : Hidden → Observed
    lift : Observed → Hidden
    residual : Hidden → Residual
    reconstructionLaw : Set
    residualPreservesUnexplainedInformation : Set

record MDLRechartLane : Set₁ where
  field
    Model Residual Score : Set
    currentModel nextModel : Model
    currentResidual nextResidual : Residual
    score : Model → Residual → Score
    _<_ : Score → Score → Set
    complexityMargin : Score
    improvementPaysForNewChart : Set

record ResidualDynamicsBoundary : Set where
  constructor residualDynamicsBoundary
  field
    reverseKernelAlwaysFindsTruth : Bool
    reverseKernelAlwaysFindsTruthIsFalse : reverseKernelAlwaysFindsTruth ≡ false
    everyResidualIsNoise : Bool
    everyResidualIsNoiseIsFalse : everyResidualIsNoise ≡ false
    everyGluingFailureNeedsRechart : Bool
    everyGluingFailureNeedsRechartIsFalse : everyGluingFailureNeedsRechart ≡ false
    jPlusOneAvailableAsTypedSuccessor : Bool
    mdlImprovementRequiredForModelPromotion : Bool
    interpretation : String

canonicalResidualDynamicsBoundary : ResidualDynamicsBoundary
canonicalResidualDynamicsBoundary =
  residualDynamicsBoundary
    false refl
    false refl
    false refl
    true
    true
    "residuals may be negligible, spectral, fine-scale, or gluing failures; update, refinement, and recharting remain distinct proof-carrying actions"
