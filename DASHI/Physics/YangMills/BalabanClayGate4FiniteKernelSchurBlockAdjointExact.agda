module DASHI.Physics.YangMills.BalabanClayGate4FiniteKernelSchurBlockAdjointExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Methodological provenance.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik
-- 140 (1911), 1--28. No DOI recorded.
--
-- Tadeusz Bałaban, Michael O'Carroll, and Ricardo Schor,
-- "Block Renormalization Group for Euclidean Fermions",
-- Communications in Mathematical Physics 122 (1989), 233--247.
-- DOI: 10.1007/BF01257414.
--
-- Tadeusz Bałaban, John Imbrie, and Arthur Jaffe,
-- "Renormalization of the Higgs Model: Minimizers, Propagators and the
-- Stability of Mean Field Theory", Communications in Mathematical Physics 97
-- (1985), 299--329. DOI: 10.1007/BF01206191.
--
-- The literature supports uniform kernel bounds and exponential decay in related
-- constructive-RG carriers.  The theorem below isolates what is actually needed
-- for DASHI's physical Q-star estimate: finite row and column sums whose product
-- fits the selected squared-norm contraction budget.
------------------------------------------------------------------------

record FiniteKernelSchurData
    (Input Output Scalar : Set) : Set₁ where
  field
    Kernel : Set
    selectedKernel : Kernel

    rowBound columnBound operatorNormSquared : Scalar
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    finiteRowKernelSumBound : Set
    finiteColumnKernelSumBound : Set

    finiteSchurTest :
      LessEqual operatorNormSquared (multiply rowBound columnBound)

open FiniteKernelSchurData public

record DyadicBlockAdjointSchurBudget
    {Input Output Scalar}
    (dataSet : FiniteKernelSchurData Input Output Scalar) : Set₁ where
  field
    oneEighth : Scalar
    rowColumnProductBelowOneEighth :
      LessEqual dataSet
        (multiply dataSet (rowBound dataSet) (columnBound dataSet))
        oneEighth

open DyadicBlockAdjointSchurBudget public

finiteSchurImpliesOneEighthSquaredNorm :
  ∀ {Input Output Scalar}
    {dataSet : FiniteKernelSchurData Input Output Scalar} →
  (budget : DyadicBlockAdjointSchurBudget dataSet) →
  LessEqual dataSet
    (operatorNormSquared dataSet)
    (oneEighth budget)
finiteSchurImpliesOneEighthSquaredNorm {dataSet = dataSet} budget =
  transitive dataSet
    (finiteSchurTest dataSet)
    (rowColumnProductBelowOneEighth budget)

record PhysicalBlockAdjointKernelMeaning
    (Scale Input Output Scalar : Set) : Set₁ where
  field
    kernelData : Scale → FiniteKernelSchurData Input Output Scalar
    nextScale : Scale → Scale

    physicalBlockAdjointNormSquared : Scale → Scalar
    physicalNormMeaning : ∀ scale →
      physicalBlockAdjointNormSquared (nextScale scale)
      ≡ operatorNormSquared (kernelData scale)

    contractionBudget : ∀ scale →
      DyadicBlockAdjointSchurBudget (kernelData scale)

open PhysicalBlockAdjointKernelMeaning public

finiteKernelSchurReductionLevel : ProofLevel
finiteKernelSchurReductionLevel = machineChecked

oneEighthKernelBudgetAssemblyLevel : ProofLevel
oneEighthKernelBudgetAssemblyLevel = machineChecked

schurTestMethodProvenanceLevel : ProofLevel
schurTestMethodProvenanceLevel = standardImported

physicalBlockAdjointKernelIdentificationInputsLevel : ProofLevel
physicalBlockAdjointKernelIdentificationInputsLevel = conditional

physicalBlockAdjointRowColumnSumInputsLevel : ProofLevel
physicalBlockAdjointRowColumnSumInputsLevel = conditional
