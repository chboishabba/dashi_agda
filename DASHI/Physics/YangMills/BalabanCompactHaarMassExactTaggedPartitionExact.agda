module DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact where

------------------------------------------------------------------------
-- MASS-EXACT TAGGED PARTITIONS
--
-- Choose the quadrature weight of each cell to be its exact Haar mass.
-- Then the discrepancy contribution is identically zero and the global
-- quadrature error is bounded solely by the mass-weighted cell oscillation.
--
-- If every cell oscillation is bounded by one common modulus omega and the
-- cell masses sum to one, the total error is at most omega.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; +-mono-≤; absZero; subSelf;
   +-identityˡ; *-comm; *-distribʳ-+; mulOneʳ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error

realSumScaleRight :
  ∀ {A : Set}
    (values : List A)
    (weight : A → ℝ)
    common →
  Sums.realSum values (λ x → weight x *ℝ common)
  ≡
  Sums.realSum values weight *ℝ common
realSumScaleRight [] weight common =
  sym
    (DASHI.Foundations.RealAnalysisAxioms.mulZeroˡ common)
realSumScaleRight (x ∷ xs) weight common =
  trans
    (cong
      (λ tail → (weight x *ℝ common) +ℝ tail)
      (realSumScaleRight xs weight common))
    (sym
      (*-distribʳ-+
        (weight x)
        (Sums.realSum xs weight)
        common))

oneTimes :
  ∀ value →
  1ℝ *ℝ value ≡ value
oneTimes value =
  trans
    (*-comm 1ℝ value)
    (mulOneʳ value)

record MassExactTaggedPartition
    (Cell : Set) : Set₁ where
  field
    cells : List Cell

    sourceCellIntegral : Cell → ℝ
    cellMass : Cell → ℝ
    sampleValue : Cell → ℝ

    modulus : ℝ
    modulusNonnegative : 0ℝ ≤ℝ modulus

    cellOscillationBound : ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (cellMass cell *ℝ sampleValue cell))
      ≤ℝ
      cellMass cell *ℝ modulus

    massesSumOne :
      Sums.realSum cells cellMass ≡ 1ℝ

open MassExactTaggedPartition public

asFiniteQuadratureCellError :
  ∀ {Cell} →
  MassExactTaggedPartition Cell →
  Error.FiniteQuadratureCellError Cell
asFiniteQuadratureCellError dataSet = record
  { Error.FiniteQuadratureCellError.cells =
      cells dataSet
  ; Error.FiniteQuadratureCellError.sourceCellIntegral =
      sourceCellIntegral dataSet
  ; Error.FiniteQuadratureCellError.sourceCellMass =
      cellMass dataSet
  ; Error.FiniteQuadratureCellError.quadratureCellMass =
      cellMass dataSet
  ; Error.FiniteQuadratureCellError.sampleValue =
      sampleValue dataSet
  ; Error.FiniteQuadratureCellError.oscillationError =
      λ cell → cellMass dataSet cell *ℝ modulus dataSet
  ; Error.FiniteQuadratureCellError.discrepancyError =
      λ _ → 0ℝ
  ; Error.FiniteQuadratureCellError.oscillationBound =
      cellOscillationBound dataSet
  ; Error.FiniteQuadratureCellError.discrepancyBound =
      λ cell →
        subst
          (λ difference → absℝ difference ≤ℝ 0ℝ)
          (sym
            (subSelf
              (cellMass dataSet cell *ℝ sampleValue dataSet cell)))
          (subst
            (λ absolute → absolute ≤ℝ 0ℝ)
            (sym absZero)
            ≤ℝ-refl)
  }

taggedQuadratureSum :
  ∀ {Cell} →
  MassExactTaggedPartition Cell → ℝ
taggedQuadratureSum dataSet =
  Error.quadratureSum
    (asFiniteQuadratureCellError dataSet)

taggedSourceIntegral :
  ∀ {Cell} →
  MassExactTaggedPartition Cell → ℝ
taggedSourceIntegral dataSet =
  Error.sourceIntegral
    (asFiniteQuadratureCellError dataSet)

totalBudgetIsModulus :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell) →
  Error.totalErrorBudget
    (asFiniteQuadratureCellError dataSet)
  ≡ modulus dataSet
totalBudgetIsModulus dataSet =
  trans
    (Sums.realSumCong
      (cells dataSet)
      (λ cell →
        +-identityʳ
          (cellMass dataSet cell *ℝ modulus dataSet)))
    (trans
      (realSumScaleRight
        (cells dataSet)
        (cellMass dataSet)
        (modulus dataSet))
      (trans
        (cong
          (λ totalMass → totalMass *ℝ modulus dataSet)
          (massesSumOne dataSet))
        (oneTimes (modulus dataSet))))

massExactTaggedPartitionError :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell) →
  absℝ
    (taggedSourceIntegral dataSet
      -ℝ taggedQuadratureSum dataSet)
  ≤ℝ
  modulus dataSet
massExactTaggedPartitionError dataSet =
  subst
    (λ budget →
      absℝ
        (taggedSourceIntegral dataSet
          -ℝ taggedQuadratureSum dataSet)
      ≤ℝ budget)
    (totalBudgetIsModulus dataSet)
    (Error.finiteQuadratureErrorBound
      (asFiniteQuadratureCellError dataSet))

massExactTaggedPartitionCompilerLevel : ProofLevel
massExactTaggedPartitionCompilerLevel = machineChecked

massExactDiscrepancyZeroLevel : ProofLevel
massExactDiscrepancyZeroLevel = machineChecked

-- Remaining analytic content after choosing exact Haar cell masses:
-- construct the tagged partitions and prove the common cell oscillation modulus
-- tends to zero for the literal Eq.(1.71) density.
literalProductHaarMassExactPartitionLevel : ProofLevel
literalProductHaarMassExactPartitionLevel = conditional

literalEquation171TaggedCellOscillationLevel : ProofLevel
literalEquation171TaggedCellOscillationLevel = conditional
