module DASHI.Physics.YangMills.BalabanCompactHaarMassExactContributionApproximationExact where

------------------------------------------------------------------------
-- REAL HAAR TAGGED SUM -> RATIONAL/EXECUTABLE CELL CONTRIBUTIONS
--
-- The executable finite fold need not expose Haar masses separately.
-- A rational Gate4 activity may represent the WHOLE weighted cell contribution.
--
-- Per cell:
--
--   literal cell integral
--      ~ μ(C) f(x_C)                       oscillation
--      ~ executableContribution(C)         rationalization/representation
--
-- Hence no claim that μ(C) itself is rational is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-trans; +-mono-≤; absAddSubadditive; subAddCancelMiddle;
   *-distribˡ-+; *-comm; mulOneʳ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Tagged

record MassExactContributionApproximation
    (Cell : Set) : Set₁ where
  field
    cells : List Cell

    sourceCellIntegral : Cell → ℝ
    cellMass : Cell → ℝ
    sourceSample : Cell → ℝ

    executableContribution : Cell → ℝ

    oscillationModulus : ℝ
    contributionApproximationModulus : ℝ

    cellOscillationBound : ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (cellMass cell *ℝ sourceSample cell))
      ≤ℝ
      cellMass cell *ℝ oscillationModulus

    cellContributionApproximationBound : ∀ cell →
      absℝ
        ((cellMass cell *ℝ sourceSample cell)
          -ℝ executableContribution cell)
      ≤ℝ
      cellMass cell *ℝ contributionApproximationModulus

    massesSumOne :
      Sums.realSum cells cellMass ≡ 1ℝ

open MassExactContributionApproximation public

sourceIntegral :
  ∀ {Cell} →
  MassExactContributionApproximation Cell → ℝ
sourceIntegral dataSet =
  Sums.realSum
    (cells dataSet)
    (sourceCellIntegral dataSet)

executableSum :
  ∀ {Cell} →
  MassExactContributionApproximation Cell → ℝ
executableSum dataSet =
  Sums.realSum
    (cells dataSet)
    (executableContribution dataSet)

combinedModulus :
  ∀ {Cell} →
  MassExactContributionApproximation Cell → ℝ
combinedModulus dataSet =
  oscillationModulus dataSet
    +ℝ contributionApproximationModulus dataSet

cellTotalBound :
  ∀ {Cell}
    (dataSet : MassExactContributionApproximation Cell)
    cell →
  absℝ
    (sourceCellIntegral dataSet cell
      -ℝ executableContribution dataSet cell)
  ≤ℝ
  cellMass dataSet cell *ℝ combinedModulus dataSet
cellTotalBound dataSet cell =
  let
    source = sourceCellIntegral dataSet cell
    middle =
      cellMass dataSet cell *ℝ sourceSample dataSet cell
    target = executableContribution dataSet cell
  in
  subst
    (λ right → absℝ (source -ℝ target) ≤ℝ right)
    (sym
      (*-distribˡ-+
        (cellMass dataSet cell)
        (oscillationModulus dataSet)
        (contributionApproximationModulus dataSet)))
    (≤ℝ-trans
      (subst
        (λ difference →
          absℝ difference
          ≤ℝ
          absℝ (source -ℝ middle)
            +ℝ absℝ (middle -ℝ target))
        (sym (subAddCancelMiddle source middle target))
        (absAddSubadditive
          (source -ℝ middle)
          (middle -ℝ target)))
      (+-mono-≤
        (cellOscillationBound dataSet cell)
        (cellContributionApproximationBound dataSet cell)))

sumMassTimesCombinedModulus :
  ∀ {Cell}
    (dataSet : MassExactContributionApproximation Cell) →
  Sums.realSum
    (cells dataSet)
    (λ cell →
      cellMass dataSet cell *ℝ combinedModulus dataSet)
  ≡
  combinedModulus dataSet
sumMassTimesCombinedModulus dataSet =
  trans
    (Tagged.realSumScaleRight
      (cells dataSet)
      (cellMass dataSet)
      (combinedModulus dataSet))
    (trans
      (cong
        (λ totalMass →
          totalMass *ℝ combinedModulus dataSet)
        (massesSumOne dataSet))
      (trans
        (*-comm 1ℝ (combinedModulus dataSet))
        (mulOneʳ (combinedModulus dataSet))))

massExactContributionApproximationError :
  ∀ {Cell}
    (dataSet : MassExactContributionApproximation Cell) →
  absℝ
    (sourceIntegral dataSet -ℝ executableSum dataSet)
  ≤ℝ
  combinedModulus dataSet
massExactContributionApproximationError dataSet =
  ≤ℝ-trans
    (Error.absDifferenceOfRealSumsBelowPointwiseAbs
      (cells dataSet)
      (sourceCellIntegral dataSet)
      (executableContribution dataSet))
    (subst
      (λ upper →
        Sums.realSum
          (cells dataSet)
          (λ cell →
            absℝ
              (sourceCellIntegral dataSet cell
                -ℝ executableContribution dataSet cell))
        ≤ℝ upper)
      (sumMassTimesCombinedModulus dataSet)
      (Error.realSumMonotone
        (cells dataSet)
        (λ cell →
          absℝ
            (sourceCellIntegral dataSet cell
              -ℝ executableContribution dataSet cell))
        (λ cell →
          cellMass dataSet cell *ℝ combinedModulus dataSet)
        (cellTotalBound dataSet)))

massExactContributionApproximationCompilerLevel : ProofLevel
massExactContributionApproximationCompilerLevel = machineChecked

-- This is the corrected literal/executable seam:
-- Gate4 rational activity approximates a WEIGHTED source-cell contribution,
-- not the bare transcendental Eq.(1.71) density.
literalEquation171CellOscillationLevel : ProofLevel
literalEquation171CellOscillationLevel = conditional

literalGate4WeightedCellContributionApproximationLevel : ProofLevel
literalGate4WeightedCellContributionApproximationLevel = conditional
