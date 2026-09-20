module DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact where

------------------------------------------------------------------------
-- QUANTITATIVE FINITE QUADRATURE ERROR
--
-- For a finite partition, separate the error into:
--
--   (i) cell oscillation / representative error;
--  (ii) cell mass / discrepancy error.
--
-- The global estimate is proved by finite-sum induction from the ordered-real
-- triangle inequality.  This is the algebraic core behind the product-Haar
-- quadrature limit; no convergence theorem is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; +-mono-≤; absZero; absAddSubadditive;
   subAddDistributes; subAddCancelMiddle; +-identityˡ; +-identityʳ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums

realSumMonotone :
  ∀ {A : Set}
    (values : List A)
    (left right : A → ℝ) →
  (∀ x → left x ≤ℝ right x) →
  Sums.realSum values left ≤ℝ Sums.realSum values right
realSumMonotone [] left right pointwise =
  ≤ℝ-refl
realSumMonotone (x ∷ xs) left right pointwise =
  +-mono-≤
    (pointwise x)
    (realSumMonotone xs left right pointwise)

realSumSubExact :
  ∀ {A : Set}
    (values : List A)
    (left right : A → ℝ) →
  Sums.realSum values left -ℝ Sums.realSum values right
  ≡
  Sums.realSum values (λ x → left x -ℝ right x)
realSumSubExact [] left right =
  DASHI.Foundations.RealAnalysisAxioms.subSelf 0ℝ
realSumSubExact (x ∷ xs) left right =
  trans
    (subAddDistributes
      (left x) (Sums.realSum xs left)
      (right x) (Sums.realSum xs right))
    (cong
      (λ tail → (left x -ℝ right x) +ℝ tail)
      (realSumSubExact xs left right))

absRealSumBelowSumAbs :
  ∀ {A : Set}
    (values : List A)
    (value : A → ℝ) →
  absℝ (Sums.realSum values value)
  ≤ℝ
  Sums.realSum values (λ x → absℝ (value x))
absRealSumBelowSumAbs [] value =
  subst
    (λ left → left ≤ℝ 0ℝ)
    (sym absZero)
    ≤ℝ-refl
absRealSumBelowSumAbs (x ∷ xs) value =
  ≤ℝ-trans
    (absAddSubadditive
      (value x)
      (Sums.realSum xs value))
    (+-mono-≤
      ≤ℝ-refl
      (absRealSumBelowSumAbs xs value))

absDifferenceOfRealSumsBelowPointwiseAbs :
  ∀ {A : Set}
    (values : List A)
    (left right : A → ℝ) →
  absℝ
    (Sums.realSum values left -ℝ
     Sums.realSum values right)
  ≤ℝ
  Sums.realSum values
    (λ x → absℝ (left x -ℝ right x))
absDifferenceOfRealSumsBelowPointwiseAbs values left right =
  subst
    (λ difference →
      absℝ difference
      ≤ℝ
      Sums.realSum values
        (λ x → absℝ (left x -ℝ right x)))
    (sym (realSumSubExact values left right))
    (absRealSumBelowSumAbs values
      (λ x → left x -ℝ right x))

record FiniteQuadratureCellError
    (Cell : Set) : Set₁ where
  field
    cells : List Cell

    sourceCellIntegral : Cell → ℝ
    sourceCellMass : Cell → ℝ
    quadratureCellMass : Cell → ℝ
    sampleValue : Cell → ℝ

    oscillationError : Cell → ℝ
    discrepancyError : Cell → ℝ

    oscillationBound : ∀ cell →
      absℝ
        (sourceCellIntegral cell
          -ℝ (sourceCellMass cell *ℝ sampleValue cell))
      ≤ℝ oscillationError cell

    discrepancyBound : ∀ cell →
      absℝ
        ((sourceCellMass cell *ℝ sampleValue cell)
          -ℝ (quadratureCellMass cell *ℝ sampleValue cell))
      ≤ℝ discrepancyError cell

open FiniteQuadratureCellError public

quadratureCellValue :
  ∀ {Cell} →
  FiniteQuadratureCellError Cell → Cell → ℝ
quadratureCellValue dataSet cell =
  quadratureCellMass dataSet cell *ℝ sampleValue dataSet cell

cellTotalErrorBound :
  ∀ {Cell}
    (dataSet : FiniteQuadratureCellError Cell)
    cell →
  absℝ
    (sourceCellIntegral dataSet cell
      -ℝ quadratureCellValue dataSet cell)
  ≤ℝ
  oscillationError dataSet cell
    +ℝ discrepancyError dataSet cell
cellTotalErrorBound dataSet cell =
  let
    source = sourceCellIntegral dataSet cell
    middle = sourceCellMass dataSet cell *ℝ sampleValue dataSet cell
    target = quadratureCellValue dataSet cell
    split :
      source -ℝ target
      ≡ (source -ℝ middle) +ℝ (middle -ℝ target)
    split = subAddCancelMiddle source middle target
  in
  subst
    (λ difference →
      absℝ difference
      ≤ℝ oscillationError dataSet cell
        +ℝ discrepancyError dataSet cell)
    (sym split)
    (≤ℝ-trans
      (absAddSubadditive
        (source -ℝ middle)
        (middle -ℝ target))
      (+-mono-≤
        (oscillationBound dataSet cell)
        (discrepancyBound dataSet cell)))

sourceIntegral :
  ∀ {Cell} →
  FiniteQuadratureCellError Cell → ℝ
sourceIntegral dataSet =
  Sums.realSum
    (cells dataSet)
    (sourceCellIntegral dataSet)

quadratureSum :
  ∀ {Cell} →
  FiniteQuadratureCellError Cell → ℝ
quadratureSum dataSet =
  Sums.realSum
    (cells dataSet)
    (quadratureCellValue dataSet)

totalErrorBudget :
  ∀ {Cell} →
  FiniteQuadratureCellError Cell → ℝ
totalErrorBudget dataSet =
  Sums.realSum
    (cells dataSet)
    (λ cell →
      oscillationError dataSet cell
        +ℝ discrepancyError dataSet cell)

finiteQuadratureErrorBound :
  ∀ {Cell}
    (dataSet : FiniteQuadratureCellError Cell) →
  absℝ
    (sourceIntegral dataSet -ℝ quadratureSum dataSet)
  ≤ℝ
  totalErrorBudget dataSet
finiteQuadratureErrorBound dataSet =
  ≤ℝ-trans
    (absDifferenceOfRealSumsBelowPointwiseAbs
      (cells dataSet)
      (sourceCellIntegral dataSet)
      (quadratureCellValue dataSet))
    (realSumMonotone
      (cells dataSet)
      (λ cell →
        absℝ
          (sourceCellIntegral dataSet cell
            -ℝ quadratureCellValue dataSet cell))
      (λ cell →
        oscillationError dataSet cell
          +ℝ discrepancyError dataSet cell)
      (cellTotalErrorBound dataSet))

compactHaarFiniteQuadratureErrorLevel : ProofLevel
compactHaarFiniteQuadratureErrorLevel = machineChecked

-- Physics/geometry inputs remaining after the algebra:
-- construct product-SU(N) cells/nodes and prove their oscillation and mass
-- discrepancy budgets vanish uniformly for the Eq.(1.71) source densities.
literalProductHaarCellOscillationLevel : ProofLevel
literalProductHaarCellOscillationLevel = conditional

literalProductHaarMassDiscrepancyLevel : ProofLevel
literalProductHaarMassDiscrepancyLevel = conditional
