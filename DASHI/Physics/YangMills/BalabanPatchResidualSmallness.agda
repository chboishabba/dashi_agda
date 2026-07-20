module DASHI.Physics.YangMills.BalabanPatchResidualSmallness where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The weighted parametrix residual is split by patch geometry. A common q is
-- produced from bulk, boundary, interface, corner and nested contributions.
------------------------------------------------------------------------

record PatchResidualSmallnessData (Bound : Set) : Set₁ where
  field
    bulkUpper boundaryUpper interfaceUpper cornerUpper nestedUpper q one : Bound
    add : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    residualUpper : Bound
    residualUpperDefinition :
      residualUpper ≡
      add bulkUpper
        (add boundaryUpper (add interfaceUpper (add cornerUpper nestedUpper)))

    residualBelowQ : LessEqual residualUpper q
    qStrict : StrictlyBelow q one

open PatchResidualSmallnessData public

strictCommonResidual :
  ∀ {Bound : Set} →
  (dataSet : PatchResidualSmallnessData Bound) →
  LessEqual dataSet (residualUpper dataSet) (q dataSet)
strictCommonResidual dataSet = residualBelowQ dataSet

record PatchResidualWitness {Bound : Set}
    (dataSet : PatchResidualSmallnessData Bound) : Set₁ where
  field
    commonBound : LessEqual dataSet (residualUpper dataSet) (q dataSet)
    strictBelowOne : StrictlyBelow dataSet (q dataSet) (one dataSet)

assemblePatchResidualWitness :
  ∀ {Bound : Set} →
  (dataSet : PatchResidualSmallnessData Bound) →
  PatchResidualWitness dataSet
assemblePatchResidualWitness dataSet = record
  { commonBound = residualBelowQ dataSet
  ; strictBelowOne = qStrict dataSet
  }

patchResidualAssemblyLevel : ProofLevel
patchResidualAssemblyLevel = machineChecked

patchResidualEstimateInputsLevel : ProofLevel
patchResidualEstimateInputsLevel = conditional
