module DASHI.Physics.YangMills.BalabanPatchTransferAnalyticReduction where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity using
  (PatchRegime; boundary; scaleInterface; corner; nestedRestriction)

------------------------------------------------------------------------
-- Coherent bulk-to-patch reduction for the finite-background analytic lane.
--
-- Every patch index carries both a bulk reference quantity and its transferred
-- patch quantity.  Thus the bulk theorem applies at the same index; the regime
-- equality is needed only to select the appropriate transfer comparison.
------------------------------------------------------------------------

record PatchTransferAnalyticInputs
    (Index State Bound : Set) : Set₁ where
  field
    regime : Index → PatchRegime

    LessEqual StrictLess : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    scale : Bound → Bound → Bound
    normSq inputNorm : Index → State → Bound

    bulkEnergy patchEnergy : Index → State → Bound
    bulkGreenNorm patchGreenNorm : Index → State → Bound
    bulkGradientGreenNorm patchGradientGreenNorm : Index → State → Bound
    bulkSecondGradientGreenNorm patchSecondGradientGreenNorm : Index → State → Bound
    bulkResidualNorm patchResidualNorm : Index → State → Bound

    cBulk cBoundary cInterface cCorner cNested : Bound
    CGBulk CGBoundary CGInterface CGCorner CGNested : Bound
    CGradBulk CGradBoundary CGradInterface CGradCorner CGradNested : Bound
    CSecondBulk CSecondBoundary CSecondInterface CSecondCorner CSecondNested : Bound
    qBulk qBoundary qInterface qCorner qNested qCommon one : Bound

    bulkCoercive : ∀ index state →
      LessEqual (scale cBulk (normSq index state)) (bulkEnergy index state)

    boundaryScaledConstantBelowBulk : ∀ index state →
      LessEqual (scale cBoundary (normSq index state))
                (scale cBulk (normSq index state))
    interfaceScaledConstantBelowBulk : ∀ index state →
      LessEqual (scale cInterface (normSq index state))
                (scale cBulk (normSq index state))
    cornerScaledConstantBelowBulk : ∀ index state →
      LessEqual (scale cCorner (normSq index state))
                (scale cBulk (normSq index state))
    nestedScaledConstantBelowBulk : ∀ index state →
      LessEqual (scale cNested (normSq index state))
                (scale cBulk (normSq index state))

    boundaryEnergyComparedToBulk : ∀ index state → regime index ≡ boundary →
      LessEqual (bulkEnergy index state) (patchEnergy index state)
    interfaceEnergyComparedToBulk : ∀ index state → regime index ≡ scaleInterface →
      LessEqual (bulkEnergy index state) (patchEnergy index state)
    cornerEnergyComparedToBulk : ∀ index state → regime index ≡ corner →
      LessEqual (bulkEnergy index state) (patchEnergy index state)
    nestedEnergyComparedToBulk : ∀ index state → regime index ≡ nestedRestriction →
      LessEqual (bulkEnergy index state) (patchEnergy index state)

    bulkWeightedGreenBound : ∀ index state →
      LessEqual (bulkGreenNorm index state)
                (scale CGBulk (inputNorm index state))
    bulkWeightedGradientGreenBound : ∀ index state →
      LessEqual (bulkGradientGreenNorm index state)
                (scale CGradBulk (inputNorm index state))
    bulkWeightedSecondGradientGreenBound : ∀ index state →
      LessEqual (bulkSecondGradientGreenNorm index state)
                (scale CSecondBulk (inputNorm index state))

    patchGreenControlledByBulk : ∀ index state →
      LessEqual (patchGreenNorm index state) (bulkGreenNorm index state)
    patchGradientGreenControlledByBulk : ∀ index state →
      LessEqual (patchGradientGreenNorm index state)
                (bulkGradientGreenNorm index state)
    patchSecondGradientGreenControlledByBulk : ∀ index state →
      LessEqual (patchSecondGradientGreenNorm index state)
                (bulkSecondGradientGreenNorm index state)

    bulkGreenConstantBelowBoundary : ∀ index state →
      LessEqual (scale CGBulk (inputNorm index state))
                (scale CGBoundary (inputNorm index state))
    bulkGreenConstantBelowInterface : ∀ index state →
      LessEqual (scale CGBulk (inputNorm index state))
                (scale CGInterface (inputNorm index state))
    bulkGreenConstantBelowCorner : ∀ index state →
      LessEqual (scale CGBulk (inputNorm index state))
                (scale CGCorner (inputNorm index state))
    bulkGreenConstantBelowNested : ∀ index state →
      LessEqual (scale CGBulk (inputNorm index state))
                (scale CGNested (inputNorm index state))

    bulkGradientConstantBelowBoundary : ∀ index state →
      LessEqual (scale CGradBulk (inputNorm index state))
                (scale CGradBoundary (inputNorm index state))
    bulkGradientConstantBelowInterface : ∀ index state →
      LessEqual (scale CGradBulk (inputNorm index state))
                (scale CGradInterface (inputNorm index state))
    bulkGradientConstantBelowCorner : ∀ index state →
      LessEqual (scale CGradBulk (inputNorm index state))
                (scale CGradCorner (inputNorm index state))
    bulkGradientConstantBelowNested : ∀ index state →
      LessEqual (scale CGradBulk (inputNorm index state))
                (scale CGradNested (inputNorm index state))

    bulkSecondConstantBelowBoundary : ∀ index state →
      LessEqual (scale CSecondBulk (inputNorm index state))
                (scale CSecondBoundary (inputNorm index state))
    bulkSecondConstantBelowInterface : ∀ index state →
      LessEqual (scale CSecondBulk (inputNorm index state))
                (scale CSecondInterface (inputNorm index state))
    bulkSecondConstantBelowCorner : ∀ index state →
      LessEqual (scale CSecondBulk (inputNorm index state))
                (scale CSecondCorner (inputNorm index state))
    bulkSecondConstantBelowNested : ∀ index state →
      LessEqual (scale CSecondBulk (inputNorm index state))
                (scale CSecondNested (inputNorm index state))

    bulkWeightedResidualBound : ∀ index state →
      LessEqual (bulkResidualNorm index state)
                (scale qBulk (inputNorm index state))
    patchResidualControlledByBulk : ∀ index state →
      LessEqual (patchResidualNorm index state) (bulkResidualNorm index state)

    bulkResidualConstantBelowBoundary : ∀ index state →
      LessEqual (scale qBulk (inputNorm index state))
                (scale qBoundary (inputNorm index state))
    bulkResidualConstantBelowInterface : ∀ index state →
      LessEqual (scale qBulk (inputNorm index state))
                (scale qInterface (inputNorm index state))
    bulkResidualConstantBelowCorner : ∀ index state →
      LessEqual (scale qBulk (inputNorm index state))
                (scale qCorner (inputNorm index state))
    bulkResidualConstantBelowNested : ∀ index state →
      LessEqual (scale qBulk (inputNorm index state))
                (scale qNested (inputNorm index state))

    qBulkBelowCommon : LessEqual qBulk qCommon
    qBoundaryBelowCommon : LessEqual qBoundary qCommon
    qInterfaceBelowCommon : LessEqual qInterface qCommon
    qCornerBelowCommon : LessEqual qCorner qCommon
    qNestedBelowCommon : LessEqual qNested qCommon
    qCommonStrict : StrictLess qCommon one

open PatchTransferAnalyticInputs public

private
  hodgeChain :
    ∀ {Index State Bound}
      (d : PatchTransferAnalyticInputs Index State Bound)
      {index state c} →
      LessEqual d (scale d c (normSq d index state))
                  (scale d (cBulk d) (normSq d index state)) →
      LessEqual d (bulkEnergy d index state) (patchEnergy d index state) →
      LessEqual d (scale d c (normSq d index state)) (patchEnergy d index state)
  hodgeChain d c≤bulk energy≤patch =
    transitive d c≤bulk (transitive d (bulkCoercive d _ _) energy≤patch)

  operatorChain :
    ∀ {Index State Bound}
      (d : PatchTransferAnalyticInputs Index State Bound)
      {left middle inputConstant outputConstant index state} →
      LessEqual d left middle →
      LessEqual d middle (scale d inputConstant (inputNorm d index state)) →
      LessEqual d (scale d inputConstant (inputNorm d index state))
                  (scale d outputConstant (inputNorm d index state)) →
      LessEqual d left (scale d outputConstant (inputNorm d index state))
  operatorChain d patch≤bulk bulkBound constantCompare =
    transitive d patch≤bulk (transitive d bulkBound constantCompare)

boundaryHodgeFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state → regime d index ≡ boundary →
  LessEqual d (scale d (cBoundary d) (normSq d index state))
              (patchEnergy d index state)
boundaryHodgeFromBulk d index state patch = hodgeChain d
  (boundaryScaledConstantBelowBulk d index state)
  (boundaryEnergyComparedToBulk d index state patch)

interfaceHodgeFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state → regime d index ≡ scaleInterface →
  LessEqual d (scale d (cInterface d) (normSq d index state))
              (patchEnergy d index state)
interfaceHodgeFromBulk d index state patch = hodgeChain d
  (interfaceScaledConstantBelowBulk d index state)
  (interfaceEnergyComparedToBulk d index state patch)

cornerHodgeFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state → regime d index ≡ corner →
  LessEqual d (scale d (cCorner d) (normSq d index state))
              (patchEnergy d index state)
cornerHodgeFromBulk d index state patch = hodgeChain d
  (cornerScaledConstantBelowBulk d index state)
  (cornerEnergyComparedToBulk d index state patch)

nestedHodgeFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state → regime d index ≡ nestedRestriction →
  LessEqual d (scale d (cNested d) (normSq d index state))
              (patchEnergy d index state)
nestedHodgeFromBulk d index state patch = hodgeChain d
  (nestedScaledConstantBelowBulk d index state)
  (nestedEnergyComparedToBulk d index state patch)

boundaryGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGreenNorm d index state)
              (scale d (CGBoundary d) (inputNorm d index state))
boundaryGreenFromBulk d index state = operatorChain d
  (patchGreenControlledByBulk d index state)
  (bulkWeightedGreenBound d index state)
  (bulkGreenConstantBelowBoundary d index state)

interfaceGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGreenNorm d index state)
              (scale d (CGInterface d) (inputNorm d index state))
interfaceGreenFromBulk d index state = operatorChain d
  (patchGreenControlledByBulk d index state)
  (bulkWeightedGreenBound d index state)
  (bulkGreenConstantBelowInterface d index state)

cornerGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGreenNorm d index state)
              (scale d (CGCorner d) (inputNorm d index state))
cornerGreenFromBulk d index state = operatorChain d
  (patchGreenControlledByBulk d index state)
  (bulkWeightedGreenBound d index state)
  (bulkGreenConstantBelowCorner d index state)

nestedGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGreenNorm d index state)
              (scale d (CGNested d) (inputNorm d index state))
nestedGreenFromBulk d index state = operatorChain d
  (patchGreenControlledByBulk d index state)
  (bulkWeightedGreenBound d index state)
  (bulkGreenConstantBelowNested d index state)

boundaryGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGradientGreenNorm d index state)
              (scale d (CGradBoundary d) (inputNorm d index state))
boundaryGradientGreenFromBulk d index state = operatorChain d
  (patchGradientGreenControlledByBulk d index state)
  (bulkWeightedGradientGreenBound d index state)
  (bulkGradientConstantBelowBoundary d index state)

interfaceGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGradientGreenNorm d index state)
              (scale d (CGradInterface d) (inputNorm d index state))
interfaceGradientGreenFromBulk d index state = operatorChain d
  (patchGradientGreenControlledByBulk d index state)
  (bulkWeightedGradientGreenBound d index state)
  (bulkGradientConstantBelowInterface d index state)

cornerGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGradientGreenNorm d index state)
              (scale d (CGradCorner d) (inputNorm d index state))
cornerGradientGreenFromBulk d index state = operatorChain d
  (patchGradientGreenControlledByBulk d index state)
  (bulkWeightedGradientGreenBound d index state)
  (bulkGradientConstantBelowCorner d index state)

nestedGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchGradientGreenNorm d index state)
              (scale d (CGradNested d) (inputNorm d index state))
nestedGradientGreenFromBulk d index state = operatorChain d
  (patchGradientGreenControlledByBulk d index state)
  (bulkWeightedGradientGreenBound d index state)
  (bulkGradientConstantBelowNested d index state)

boundarySecondGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchSecondGradientGreenNorm d index state)
              (scale d (CSecondBoundary d) (inputNorm d index state))
boundarySecondGradientGreenFromBulk d index state = operatorChain d
  (patchSecondGradientGreenControlledByBulk d index state)
  (bulkWeightedSecondGradientGreenBound d index state)
  (bulkSecondConstantBelowBoundary d index state)

interfaceSecondGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchSecondGradientGreenNorm d index state)
              (scale d (CSecondInterface d) (inputNorm d index state))
interfaceSecondGradientGreenFromBulk d index state = operatorChain d
  (patchSecondGradientGreenControlledByBulk d index state)
  (bulkWeightedSecondGradientGreenBound d index state)
  (bulkSecondConstantBelowInterface d index state)

cornerSecondGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchSecondGradientGreenNorm d index state)
              (scale d (CSecondCorner d) (inputNorm d index state))
cornerSecondGradientGreenFromBulk d index state = operatorChain d
  (patchSecondGradientGreenControlledByBulk d index state)
  (bulkWeightedSecondGradientGreenBound d index state)
  (bulkSecondConstantBelowCorner d index state)

nestedSecondGradientGreenFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchSecondGradientGreenNorm d index state)
              (scale d (CSecondNested d) (inputNorm d index state))
nestedSecondGradientGreenFromBulk d index state = operatorChain d
  (patchSecondGradientGreenControlledByBulk d index state)
  (bulkWeightedSecondGradientGreenBound d index state)
  (bulkSecondConstantBelowNested d index state)

boundaryResidualFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchResidualNorm d index state)
              (scale d (qBoundary d) (inputNorm d index state))
boundaryResidualFromBulk d index state = operatorChain d
  (patchResidualControlledByBulk d index state)
  (bulkWeightedResidualBound d index state)
  (bulkResidualConstantBelowBoundary d index state)

interfaceResidualFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchResidualNorm d index state)
              (scale d (qInterface d) (inputNorm d index state))
interfaceResidualFromBulk d index state = operatorChain d
  (patchResidualControlledByBulk d index state)
  (bulkWeightedResidualBound d index state)
  (bulkResidualConstantBelowInterface d index state)

cornerResidualFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchResidualNorm d index state)
              (scale d (qCorner d) (inputNorm d index state))
cornerResidualFromBulk d index state = operatorChain d
  (patchResidualControlledByBulk d index state)
  (bulkWeightedResidualBound d index state)
  (bulkResidualConstantBelowCorner d index state)

nestedResidualFromBulk :
  ∀ {Index State Bound} (d : PatchTransferAnalyticInputs Index State Bound)
    index state →
  LessEqual d (patchResidualNorm d index state)
              (scale d (qNested d) (inputNorm d index state))
nestedResidualFromBulk d index state = operatorChain d
  (patchResidualControlledByBulk d index state)
  (bulkWeightedResidualBound d index state)
  (bulkResidualConstantBelowNested d index state)

record PatchTransferAnalyticCertificate
    (Index State Bound : Set) : Set₁ where
  constructor assemblePatchTransferAnalyticReduction
  field
    analyticInputs : PatchTransferAnalyticInputs Index State Bound

open PatchTransferAnalyticCertificate public

patchTransferAnalyticReductionAssemblyLevel : ProofLevel
patchTransferAnalyticReductionAssemblyLevel = machineChecked

bulkAndTransferEstimateInputsLevel : ProofLevel
bulkAndTransferEstimateInputsLevel = conditional
