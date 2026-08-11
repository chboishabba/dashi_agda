module DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Prove the bilinear expansion that turns the two reconstructed multiplier
-- sources into a pair-indexed Boolean-cube Green contraction:
--
--   < sum_S s_S , K+ sum_T delta_T >
--     = sum_S sum_T <s_S,K+ delta_T>.
--
-- This is the exact bridge between the literal source/defect atom producers
-- and the correlated owner ledger.  It is finite-sum algebra, not an estimate;
-- no absolute value is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

sumVector : ∀ {Atom Index : Set} →
  List Atom → (Atom → Index → ℚ) → Index → ℚ
sumVector atoms vector index =
  Sums.sumRational atoms (λ atom → vector atom index)

finiteDotLeftPointwiseCong :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    {left transported right : Index → ℚ} →
  (∀ index → left index ≡ transported index) →
  Rect.finiteDot carrier left right
  ≡ Rect.finiteDot carrier transported right
finiteDotLeftPointwiseCong carrier {left} {transported} {right} pointwise =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ index → left index * right index)
    (λ index → transported index * right index)
    (λ index → cong (_* right index) (pointwise index))

finiteDotRightPointwiseCong :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    {left right transported : Index → ℚ} →
  (∀ index → right index ≡ transported index) →
  Rect.finiteDot carrier left right
  ≡ Rect.finiteDot carrier left transported
finiteDotRightPointwiseCong carrier {left} {right} {transported} pointwise =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ index → left index * right index)
    (λ index → left index * transported index)
    (λ index → cong (left index *_) (pointwise index))

applyRectangularSumVector :
  ∀ {Atom Row Column : Set}
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : Rect.RectangularMatrix Row Column)
    (atoms : List Atom)
    (vector : Atom → Column → ℚ)
    row →
  Rect.applyRectangular columnCarrier matrix
      (sumVector atoms vector) row
  ≡ sumVector atoms
      (λ atom → Rect.applyRectangular columnCarrier matrix (vector atom))
      row
applyRectangularSumVector columnCarrier matrix [] vector row =
  Rect.applyRectangularZero columnCarrier matrix row
applyRectangularSumVector columnCarrier matrix (atom ∷ atoms) vector row =
  trans
    (Rect.applyRectangularAdd
      columnCarrier matrix
      (vector atom) (sumVector atoms vector) row)
    (cong
      (Rect.applyRectangular columnCarrier matrix (vector atom) row +_)
      (applyRectangularSumVector
        columnCarrier matrix atoms vector row))

finiteDotSumLeft :
  ∀ {Atom Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (atoms : List Atom)
    (vector : Atom → Index → ℚ)
    right →
  Rect.finiteDot carrier (sumVector atoms vector) right
  ≡ Sums.sumRational atoms
      (λ atom → Rect.finiteDot carrier (vector atom) right)
finiteDotSumLeft carrier [] vector right =
  Rect.finiteDotZeroLeft carrier right
finiteDotSumLeft carrier (atom ∷ atoms) vector right =
  trans
    (Rect.finiteDotAddLeft
      carrier (vector atom) (sumVector atoms vector) right)
    (cong
      (Rect.finiteDot carrier (vector atom) right +_)
      (finiteDotSumLeft carrier atoms vector right))

finiteDotSumRight :
  ∀ {Atom Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left
    (atoms : List Atom)
    (vector : Atom → Index → ℚ) →
  Rect.finiteDot carrier left (sumVector atoms vector)
  ≡ Sums.sumRational atoms
      (λ atom → Rect.finiteDot carrier left (vector atom))
finiteDotSumRight carrier left [] vector =
  Rect.finiteDotZeroRight carrier left
finiteDotSumRight carrier left (atom ∷ atoms) vector =
  trans
    (Rect.finiteDotAddRight
      carrier left (vector atom) (sumVector atoms vector))
    (cong
      (Rect.finiteDot carrier left (vector atom) +_)
      (finiteDotSumRight carrier left atoms vector))

greenAtomPairContraction :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintAtomData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Cube.Subset4 → Cube.Subset4 → ℚ
greenAtomPairContraction {pseudoData = pseudoData} atomData
    sourceSubset defectSubset =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    (Atoms.sourceAtom atomData sourceSubset)
    (Pseudo.pseudoApply pseudoData
      (Atoms.defectAtom atomData defectSubset))

constraintAtomGreenExpansionExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (atomData : Atoms.SelectedConstraintAtomData
      {Multiplier} pseudoData firstVariationCovector rawExtractor) →
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    (Pseudo.constraintApply pseudoData firstVariationCovector)
    (Pseudo.pseudoApply pseudoData
      (Pseudo.constraintApply pseudoData rawExtractor))
  ≡ Sums.sumRational Cube.nonemptySubsets4
      (λ sourceSubset →
        Sums.sumRational Cube.nonemptySubsets4
          (greenAtomPairContraction atomData sourceSubset))
constraintAtomGreenExpansionExact
    {pseudoData = pseudoData}
    {firstVariationCovector = firstVariationCovector}
    {rawExtractor = rawExtractor}
    atomData =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    subsets = Cube.nonemptySubsets4
    sourceSum = sumVector subsets (Atoms.sourceAtom atomData)
    defectSum = sumVector subsets (Atoms.defectAtom atomData)

    sourceToSum : ∀ row →
      Pseudo.constraintApply pseudoData firstVariationCovector row
      ≡ sourceSum row
    sourceToSum row = sym (Atoms.sourceAtomsReconstruct atomData row)

    defectToSum : ∀ row →
      Pseudo.constraintApply pseudoData rawExtractor row
      ≡ defectSum row
    defectToSum row = sym (Atoms.defectAtomsReconstruct atomData row)

    pseudoDefectToSum : ∀ row →
      Pseudo.pseudoApply pseudoData
        (Pseudo.constraintApply pseudoData rawExtractor) row
      ≡ Pseudo.pseudoApply pseudoData defectSum row
    pseudoDefectToSum =
      Rect.applyRectangularVectorCong
        carrier
        (Pseudo.gramPseudoinverse pseudoData)
        defectToSum

    pseudoSumToAtomSum : ∀ row →
      Pseudo.pseudoApply pseudoData defectSum row
      ≡ sumVector subsets
          (λ defectSubset →
            Pseudo.pseudoApply pseudoData
              (Atoms.defectAtom atomData defectSubset))
          row
    pseudoSumToAtomSum =
      applyRectangularSumVector
        carrier
        (Pseudo.gramPseudoinverse pseudoData)
        subsets
        (Atoms.defectAtom atomData)
  in
  trans
    (finiteDotLeftPointwiseCong carrier sourceToSum)
    (trans
      (finiteDotRightPointwiseCong carrier pseudoDefectToSum)
      (trans
        (finiteDotRightPointwiseCong carrier pseudoSumToAtomSum)
        (trans
          (finiteDotSumRight carrier sourceSum subsets
            (λ defectSubset →
              Pseudo.pseudoApply pseudoData
                (Atoms.defectAtom atomData defectSubset)))
          (trans
            (Sums.sumRationalCong
              subsets
              (λ defectSubset →
                Rect.finiteDot carrier sourceSum
                  (Pseudo.pseudoApply pseudoData
                    (Atoms.defectAtom atomData defectSubset)))
              (λ defectSubset →
                Sums.sumRational subsets
                  (λ sourceSubset →
                    greenAtomPairContraction atomData
                      sourceSubset defectSubset))
              (λ defectSubset →
                finiteDotSumLeft carrier subsets
                  (Atoms.sourceAtom atomData)
                  (Pseudo.pseudoApply pseudoData
                    (Atoms.defectAtom atomData defectSubset))))
            (Fubini.sumSwap subsets subsets
              (λ defectSubset sourceSubset →
                greenAtomPairContraction atomData
                  sourceSubset defectSubset))))))

constraintAtomGreenBilinearExpansionLevel : ProofLevel
constraintAtomGreenBilinearExpansionLevel = machineChecked
