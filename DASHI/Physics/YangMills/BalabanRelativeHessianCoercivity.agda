module DASHI.Physics.YangMills.BalabanRelativeHessianCoercivity where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBackgroundFieldClosure as Background

------------------------------------------------------------------------
-- Highest-alpha B1 lane.
--
-- Instead of postulating coercivity of every background Hessian directly, this
-- module derives it from a uniformly coercive reference Hessian plus a relative
-- form bound for the background perturbation.  This is the standard stability
-- mechanism used in small-field background analysis.
------------------------------------------------------------------------

record RelativeHessianCoercivityData
    (Index State Bound : Set) : Set₁ where
  field
    referenceHessian : Index → State → State
    fullHessian : Index → State → State
    green : Index → State → State
    inner : State → State → Bound
    normSq : State → Bound
    scale add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    Positive : Bound → Set

    cReference perturbationSize cH : Bound
    cHPositive : Positive cH

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)
    addRightCancel : ∀ {left right common} →
      LessEqual (add left common) (add right common) → LessEqual left right

    GaugeFixedTangent : Index → State → Set

    referenceCoercive : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual (scale cReference (normSq state))
        (inner state (referenceHessian index state))

    perturbationPenalty : Index → State → Bound
    referenceBelowFullPlusPenalty : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual
        (inner state (referenceHessian index state))
        (add (inner state (fullHessian index state))
          (perturbationPenalty index state))

    perturbationRelativelyBounded : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual (perturbationPenalty index state)
        (scale perturbationSize (normSq state))

    coercivityBudget : ∀ state →
      LessEqual
        (add (scale cH (normSq state))
          (scale perturbationSize (normSq state)))
        (scale cReference (normSq state))

    constrainedHessianInvertible : ∀ index →
      Background.TwoSidedInverse (fullHessian index) (green index)

    GaugeZeroModesRemoved : Index → Set
    BlockAverageModesRemoved : Index → Set
    ResidualGaugeModesRemoved : Index → Set
    BoundaryDegeneraciesRemoved : Index → Set
    gaugeZeroModesRemoved : ∀ index → GaugeZeroModesRemoved index
    blockAverageModesRemoved : ∀ index → BlockAverageModesRemoved index
    residualGaugeModesRemoved : ∀ index → ResidualGaugeModesRemoved index
    boundaryDegeneraciesRemoved : ∀ index → BoundaryDegeneraciesRemoved index

open RelativeHessianCoercivityData public

relativePerturbationPreservesCoercivity :
  ∀ {Index State Bound : Set} →
  (dataSet : RelativeHessianCoercivityData Index State Bound) →
  ∀ index state →
  GaugeFixedTangent dataSet index state →
  LessEqual dataSet
    (scale dataSet (cH dataSet) (normSq dataSet state))
    (inner dataSet state (fullHessian dataSet index state))
relativePerturbationPreservesCoercivity dataSet index state tangent =
  addRightCancel dataSet
    (transitive dataSet
      (coercivityBudget dataSet state)
      (transitive dataSet
        (referenceCoercive dataSet index state tangent)
        (transitive dataSet
          (referenceBelowFullPlusPenalty dataSet index state tangent)
          (addMonotone dataSet
            (reflexive dataSet
              (inner dataSet state (fullHessian dataSet index state)))
            (perturbationRelativelyBounded dataSet index state tangent)))))

toUniformConstrainedHessianCoercivity :
  ∀ {Index State Bound : Set} →
  RelativeHessianCoercivityData Index State Bound →
  Background.UniformConstrainedHessianCoercivity
    Index State Bound Bound
toUniformConstrainedHessianCoercivity dataSet = record
  { hessian = fullHessian dataSet
  ; green = green dataSet
  ; GaugeFixedTangent = GaugeFixedTangent dataSet
  ; inner = inner dataSet
  ; normSq = normSq dataSet
  ; scale = scale dataSet
  ; LessEqual = LessEqual dataSet
  ; Positive = Positive dataSet
  ; cH = cH dataSet
  ; cHPositive = cHPositive dataSet
  ; uniformConstrainedHessianCoercive =
      relativePerturbationPreservesCoercivity dataSet
  ; constrainedHessianInvertible = constrainedHessianInvertible dataSet
  ; GaugeZeroModesRemoved = GaugeZeroModesRemoved dataSet
  ; BlockAverageModesRemoved = BlockAverageModesRemoved dataSet
  ; ResidualGaugeModesRemoved = ResidualGaugeModesRemoved dataSet
  ; BoundaryDegeneraciesRemoved = BoundaryDegeneraciesRemoved dataSet
  ; gaugeZeroModesRemoved = gaugeZeroModesRemoved dataSet
  ; blockAverageModesRemoved = blockAverageModesRemoved dataSet
  ; residualGaugeModesRemoved = residualGaugeModesRemoved dataSet
  ; boundaryDegeneraciesRemoved = boundaryDegeneraciesRemoved dataSet
  }

relativeHessianCoercivityBridgeLevel : ProofLevel
relativeHessianCoercivityBridgeLevel = machineChecked

referenceCoercivityAndPerturbationInputsLevel : ProofLevel
referenceCoercivityAndPerturbationInputsLevel = conditional
