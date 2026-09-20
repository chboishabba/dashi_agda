module DASHI.Physics.YangMills.BalabanMassExactTaggedPartitionQuadratureExact where

------------------------------------------------------------------------
-- MASS-EXACT TAGGED PARTITION QUADRATURE
--
-- If the quadrature weight of each cell is its literal source/Haar mass,
-- discrepancy vanishes exactly.  If each cell's tagged-value error is bounded
-- by mass(C) * modulus(mesh), and the cell masses sum to one, then
--
--   | integral f - taggedQuadrature f | <= modulus(mesh).
--
-- This is the reusable compact-probability Riemann-sum theorem needed by the
-- Eq.(1.71) route.  No Yang--Mills-specific input occurs in the proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; +-identityʳ; *-comm; *-distribʳ-+;
   mulOneʳ; mulZeroˡ; subSelf; absZero)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error

realSumRightScaleExact :
  ∀ {A : Set}
    (values : List A)
    (value : A → ℝ)
    (scale : ℝ) →
  Sums.realSum values (λ x → value x *ℝ scale)
  ≡
  Sums.realSum values value *ℝ scale
realSumRightScaleExact [] value scale =
  sym (mulZeroˡ scale)
realSumRightScaleExact (x ∷ xs) value scale =
  trans
    (cong
      (λ tail → value x *ℝ scale +ℝ tail)
      (realSumRightScaleExact xs value scale))
    (sym
      (*-distribʳ-+
        (value x)
        (Sums.realSum xs value)
        scale))

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

    massesSumOne :
      Sums.realSum cells cellMass ≡ 1ℝ

    cellOscillationBound :
      ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (cellMass cell *ℝ sampleValue cell))
      ≤ℝ
      cellMass cell *ℝ modulus

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
          (subSelf
            (cellMass dataSet cell *ℝ sampleValue dataSet cell))
          (subst
            (λ absolute → absolute ≤ℝ 0ℝ)
            (sym absZero)
            ≤ℝ-refl)
  }

massExactDiscrepancyIsZero :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell)
    cell →
  Error.discrepancyError
    (asFiniteQuadratureCellError dataSet) cell
  ≡ 0ℝ
massExactDiscrepancyIsZero dataSet cell = refl

totalErrorBudgetIsMassWeightedModulus :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell) →
  Error.totalErrorBudget
    (asFiniteQuadratureCellError dataSet)
  ≡
  Sums.realSum
    (cells dataSet)
    (λ cell → cellMass dataSet cell *ℝ modulus dataSet)
totalErrorBudgetIsMassWeightedModulus dataSet =
  Sums.realSumCong
    (cells dataSet)
    (λ cell → +-identityʳ
      (cellMass dataSet cell *ℝ modulus dataSet))

massWeightedModulusIsModulus :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell) →
  Sums.realSum
    (cells dataSet)
    (λ cell → cellMass dataSet cell *ℝ modulus dataSet)
  ≡
  modulus dataSet
massWeightedModulusIsModulus dataSet =
  trans
    (realSumRightScaleExact
      (cells dataSet)
      (cellMass dataSet)
      (modulus dataSet))
    (trans
      (cong
        (_*ℝ modulus dataSet)
        (massesSumOne dataSet))
      (oneTimes (modulus dataSet)))

massExactTotalErrorBudgetIsModulus :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell) →
  Error.totalErrorBudget
    (asFiniteQuadratureCellError dataSet)
  ≡
  modulus dataSet
massExactTotalErrorBudgetIsModulus dataSet =
  trans
    (totalErrorBudgetIsMassWeightedModulus dataSet)
    (massWeightedModulusIsModulus dataSet)

massExactTaggedPartitionError :
  ∀ {Cell}
    (dataSet : MassExactTaggedPartition Cell) →
  absℝ
    (Error.sourceIntegral
      (asFiniteQuadratureCellError dataSet)
      -ℝ
      Error.quadratureSum
        (asFiniteQuadratureCellError dataSet))
  ≤ℝ
  modulus dataSet
massExactTaggedPartitionError dataSet =
  subst
    (λ bound →
      absℝ
        (Error.sourceIntegral
          (asFiniteQuadratureCellError dataSet)
          -ℝ
          Error.quadratureSum
            (asFiniteQuadratureCellError dataSet))
      ≤ℝ bound)
    (massExactTotalErrorBudgetIsModulus dataSet)
    (Error.finiteQuadratureErrorBound
      (asFiniteQuadratureCellError dataSet))

massExactTaggedPartitionCompilerLevel : ProofLevel
massExactTaggedPartitionCompilerLevel = machineChecked

massExactTaggedPartitionDiscrepancyLevel : ProofLevel
massExactTaggedPartitionDiscrepancyLevel = machineChecked

massExactTaggedPartitionModulusCollapseLevel : ProofLevel
massExactTaggedPartitionModulusCollapseLevel = machineChecked
