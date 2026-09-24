module DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedApproximationExact where

------------------------------------------------------------------------
-- MASS-EXACT TAGGED HAAR QUADRATURE WITH APPROXIMATE EXECUTABLE VALUES
--
-- Literal source sample values live in ℝ.  Gate4 executable values may live in
-- a smaller/rational image.  Exact pointwise equality is neither required nor
-- generally possible.
--
-- On each cell:
--
--   source integral
--     ~ mass * literal source value       (oscillation error)
--     ~ mass * executable embedded value (value/rationalization error)
--
-- Exact Haar cell masses make measure discrepancy identically zero.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; +-mono-≤; absAddSubadditive;
   subAddCancelMiddle; *-distribˡ-+; *-comm; mulOneʳ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Exact

record MassExactTaggedApproximation
    (Cell : Set) : Set₁ where
  field
    cells : List Cell

    sourceCellIntegral : Cell → ℝ
    cellMass : Cell → ℝ

    sourceSample : Cell → ℝ
    executableSample : Cell → ℝ

    oscillationModulus : ℝ
    valueApproximationModulus : ℝ

    cellOscillationBound : ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (cellMass cell *ℝ sourceSample cell))
      ≤ℝ
      cellMass cell *ℝ oscillationModulus

    cellValueApproximationBound : ∀ cell →
      absℝ
        ((cellMass cell *ℝ sourceSample cell)
          -ℝ (cellMass cell *ℝ executableSample cell))
      ≤ℝ
      cellMass cell *ℝ valueApproximationModulus

    massesSumOne :
      Sums.realSum cells cellMass ≡ 1ℝ

open MassExactTaggedApproximation public

sourceIntegral :
  ∀ {Cell} →
  MassExactTaggedApproximation Cell → ℝ
sourceIntegral dataSet =
  Sums.realSum
    (cells dataSet)
    (sourceCellIntegral dataSet)

executableQuadrature :
  ∀ {Cell} →
  MassExactTaggedApproximation Cell → ℝ
executableQuadrature dataSet =
  Sums.realSum
    (cells dataSet)
    (λ cell →
      cellMass dataSet cell *ℝ executableSample dataSet cell)

combinedModulus :
  ∀ {Cell} →
  MassExactTaggedApproximation Cell → ℝ
combinedModulus dataSet =
  oscillationModulus dataSet
    +ℝ valueApproximationModulus dataSet

cellTotalApproximationBound :
  ∀ {Cell}
    (dataSet : MassExactTaggedApproximation Cell)
    cell →
  absℝ
    (sourceCellIntegral dataSet cell
      -ℝ
      (cellMass dataSet cell *ℝ executableSample dataSet cell))
  ≤ℝ
  cellMass dataSet cell *ℝ combinedModulus dataSet
cellTotalApproximationBound dataSet cell =
  let
    source = sourceCellIntegral dataSet cell
    middle =
      cellMass dataSet cell *ℝ sourceSample dataSet cell
    target =
      cellMass dataSet cell *ℝ executableSample dataSet cell
  in
  subst
    (λ right →
      absℝ (source -ℝ target) ≤ℝ right)
    (sym
      (*-distribˡ-+
        (cellMass dataSet cell)
        (oscillationModulus dataSet)
        (valueApproximationModulus dataSet)))
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
        (cellValueApproximationBound dataSet cell)))

sumMassTimesCombinedModulus :
  ∀ {Cell}
    (dataSet : MassExactTaggedApproximation Cell) →
  Sums.realSum
    (cells dataSet)
    (λ cell →
      cellMass dataSet cell *ℝ combinedModulus dataSet)
  ≡
  combinedModulus dataSet
sumMassTimesCombinedModulus dataSet =
  trans
    (Exact.realSumScaleRight
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

massExactTaggedApproximationError :
  ∀ {Cell}
    (dataSet : MassExactTaggedApproximation Cell) →
  absℝ
    (sourceIntegral dataSet
      -ℝ executableQuadrature dataSet)
  ≤ℝ
  combinedModulus dataSet
massExactTaggedApproximationError dataSet =
  ≤ℝ-trans
    (Error.absDifferenceOfRealSumsBelowPointwiseAbs
      (cells dataSet)
      (sourceCellIntegral dataSet)
      (λ cell →
        cellMass dataSet cell *ℝ executableSample dataSet cell))
    (subst
      (λ upper →
        Sums.realSum
          (cells dataSet)
          (λ cell →
            absℝ
              (sourceCellIntegral dataSet cell
                -ℝ
                (cellMass dataSet cell
                  *ℝ executableSample dataSet cell)))
        ≤ℝ upper)
      (sumMassTimesCombinedModulus dataSet)
      (Error.realSumMonotone
        (cells dataSet)
        (λ cell →
          absℝ
            (sourceCellIntegral dataSet cell
              -ℝ
              (cellMass dataSet cell
                *ℝ executableSample dataSet cell)))
        (λ cell →
          cellMass dataSet cell *ℝ combinedModulus dataSet)
        (cellTotalApproximationBound dataSet)))

massExactTaggedApproximationCompilerLevel : ProofLevel
massExactTaggedApproximationCompilerLevel = machineChecked

massExactMeasureDiscrepancyEliminatedLevel : ProofLevel
massExactMeasureDiscrepancyEliminatedLevel = machineChecked

-- Genuine analytic/source work:
-- (1) shrinking Haar cells control source oscillation;
-- (2) executable Gate4 rational values approximate the literal source density.
literalEquation171OscillationApproximationLevel : ProofLevel
literalEquation171OscillationApproximationLevel = conditional

literalGate4RationalValueApproximationLevel : ProofLevel
literalGate4RationalValueApproximationLevel = conditional
