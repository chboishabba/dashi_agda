module DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurBlockAdjointExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary methodological provenance.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik 140
-- (1911), 1--28. No DOI recorded.
--
-- The weighted Schur test permits nonconstant positive input and output test
-- functions.  In finite form, weighted row and column estimates with constants
-- alpha and beta imply ||T||^2 <= alpha beta.  This is the appropriate target
-- when lattice-volume weights, field normalization and RG rescaling cannot be
-- represented honestly by unweighted support cardinalities alone.
--
-- No particular scale weight is selected below.  A candidate such as an
-- L^{-gamma k} weight becomes useful only after it is identified with the
-- repository's physical Hilbert/polymer norm and both weighted kernel sums are
-- proved in that normalization.
------------------------------------------------------------------------

record FiniteWeightedSchurData
    (Input Output Scalar : Set) : Set₁ where
  field
    Kernel : Output → Input → Scalar

    inputWeight : Input → Scalar
    outputWeight : Output → Scalar

    weightedRowSum : Output → Scalar
    weightedColumnSum : Input → Scalar

    alpha beta operatorNormSquared : Scalar
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    InputWeightPositive : Input → Set
    OutputWeightPositive : Output → Set
    inputWeightPositive : ∀ input → InputWeightPositive input
    outputWeightPositive : ∀ output → OutputWeightPositive output

    WeightedRowSumMeaning : (Output → Scalar) → Set
    WeightedColumnSumMeaning : (Input → Scalar) → Set
    weightedRowSumMeaning : WeightedRowSumMeaning weightedRowSum
    weightedColumnSumMeaning : WeightedColumnSumMeaning weightedColumnSum

    weightedRowBound : ∀ output →
      LessEqual
        (weightedRowSum output)
        (multiply alpha (outputWeight output))

    weightedColumnBound : ∀ input →
      LessEqual
        (weightedColumnSum input)
        (multiply beta (inputWeight input))

    finiteWeightedSchurTest :
      LessEqual operatorNormSquared (multiply alpha beta)

open FiniteWeightedSchurData public

record RelativeWeightedSchurBudget
    {Input Output Scalar : Set}
    (dataSet : FiniteWeightedSchurData Input Output Scalar) : Set₁ where
  field
    oneEighth previousNormSquared : Scalar

    weightedProductBelowRelativeBudget :
      LessEqual dataSet
        (multiply dataSet (alpha dataSet) (beta dataSet))
        (multiply dataSet oneEighth previousNormSquared)

open RelativeWeightedSchurBudget public

finiteWeightedSchurImpliesRelativeOneEighth :
  ∀ {Input Output Scalar : Set}
    {dataSet : FiniteWeightedSchurData Input Output Scalar} →
  (budget : RelativeWeightedSchurBudget dataSet) →
  LessEqual dataSet
    (operatorNormSquared dataSet)
    (multiply dataSet
      (oneEighth budget)
      (previousNormSquared budget))
finiteWeightedSchurImpliesRelativeOneEighth {dataSet = dataSet} budget =
  transitive dataSet
    (finiteWeightedSchurTest dataSet)
    (weightedProductBelowRelativeBudget budget)

record PhysicalScaleWeightedSchurMeaning
    (Scale Input Output Scalar : Set) : Set₁ where
  field
    weightedData : Scale → FiniteWeightedSchurData Input Output Scalar

    PhysicalInputWeight : Scale → (Input → Scalar) → Set
    PhysicalOutputWeight : Scale → (Output → Scalar) → Set
    PhysicalWeightedKernel : Scale → (Output → Input → Scalar) → Set

    physicalInputWeight : ∀ scale →
      PhysicalInputWeight scale (inputWeight (weightedData scale))
    physicalOutputWeight : ∀ scale →
      PhysicalOutputWeight scale (outputWeight (weightedData scale))
    physicalWeightedKernel : ∀ scale →
      PhysicalWeightedKernel scale (Kernel (weightedData scale))

    relativeBudget : ∀ scale →
      RelativeWeightedSchurBudget (weightedData scale)

open PhysicalScaleWeightedSchurMeaning public

physicalWeightedSchurRelativeOneEighth :
  ∀ {Scale Input Output Scalar : Set}
    (meaning : PhysicalScaleWeightedSchurMeaning
      Scale Input Output Scalar)
    scale →
  LessEqual (weightedData meaning scale)
    (operatorNormSquared (weightedData meaning scale))
    (multiply (weightedData meaning scale)
      (oneEighth (relativeBudget meaning scale))
      (previousNormSquared (relativeBudget meaning scale)))
physicalWeightedSchurRelativeOneEighth meaning scale =
  finiteWeightedSchurImpliesRelativeOneEighth
    (relativeBudget meaning scale)

finiteWeightedSchurInterfaceLevel : ProofLevel
finiteWeightedSchurInterfaceLevel = machineChecked

weightedRelativeOneEighthAssemblyLevel : ProofLevel
weightedRelativeOneEighthAssemblyLevel = machineChecked

physicalScaleWeightedSchurAssemblyLevel : ProofLevel
physicalScaleWeightedSchurAssemblyLevel = machineChecked

weightedSchurMethodProvenanceLevel : ProofLevel
weightedSchurMethodProvenanceLevel = standardImported

physicalWeightedKernelSumMeaningInputsLevel : ProofLevel
physicalWeightedKernelSumMeaningInputsLevel = conditional

physicalScaleWeightChoiceInputsLevel : ProofLevel
physicalScaleWeightChoiceInputsLevel = conditional

physicalWeightedRowColumnBudgetInputsLevel : ProofLevel
physicalWeightedRowColumnBudgetInputsLevel = conditional
