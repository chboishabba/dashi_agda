module DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur, classical matrix norm test (1911). No DOI applies to the
-- original result.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Extend the repository's square-root-free finite Schur test from square
-- matrices to the rectangular map actually carried by the nonlinear block
-- average:
--
--       A : Q^Column -> Q^Row.
--
-- If every absolute row mass is at most R and every absolute column mass is at
-- most C, then exact finite weighted Cauchy plus Fubini gives
--
--       ||A v||_2^2 <= R C ||v||_2^2.
--
-- No square root, spectral theorem, completeness, or dimension-count argument
-- is used.  This is the finite rational engine needed to turn CMP109
-- pointwise derivative-entry estimates into the nonlinear Gate-I L2 budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur

RectMatrix : Set → Set → Set
RectMatrix Row Column = Row → Column → ℚ

Vector : Set → Set
Vector Index = Index → ℚ

rectVectorNormSq :
  ∀ {Index : Set} → List Index → Vector Index → ℚ
rectVectorNormSq indices vector =
  Sums.sumRational indices
    (λ index → FiniteL2.square (vector index))

rectAbsoluteRowMass :
  ∀ {Row Column : Set} →
  List Column → RectMatrix Row Column → Row → ℚ
rectAbsoluteRowMass columns matrix row =
  Sums.sumRational columns (λ column → ∣ matrix row column ∣)

rectAbsoluteColumnMass :
  ∀ {Row Column : Set} →
  List Row → RectMatrix Row Column → Column → ℚ
rectAbsoluteColumnMass rows matrix column =
  Sums.sumRational rows (λ row → ∣ matrix row column ∣)

rectRowWeightedEnergy :
  ∀ {Row Column : Set} →
  List Column → RectMatrix Row Column → Vector Column → Row → ℚ
rectRowWeightedEnergy columns matrix vector row =
  Sums.sumRational columns
    (λ column →
      ∣ matrix row column ∣ * FiniteL2.square (vector column))

rectAbsoluteMajorantApply :
  ∀ {Row Column : Set} →
  List Column → RectMatrix Row Column → Vector Column → Row → ℚ
rectAbsoluteMajorantApply columns matrix vector row =
  Sums.sumRational columns
    (λ column → ∣ matrix row column ∣ * ∣ vector column ∣)

rectApply :
  ∀ {Row Column : Set} →
  List Column → RectMatrix Row Column → Vector Column → Row → ℚ
rectApply columns matrix vector row =
  Sums.sumRational columns (λ column → matrix row column * vector column)

rectApplyAbsoluteBound :
  ∀ {Row Column : Set}
    (columns : List Column)
    (matrix : RectMatrix Row Column)
    (vector : Vector Column)
    row →
  ∣ rectApply columns matrix vector row ∣
  ≤ rectAbsoluteMajorantApply columns matrix vector row
rectApplyAbsoluteBound columns matrix vector row =
  subst
    (λ upper → ∣ rectApply columns matrix vector row ∣ ≤ upper)
    (Schur.sumAbsoluteProductsExact columns (matrix row) vector)
    (Schur.sumAbsoluteTriangle columns
      (λ column → matrix row column * vector column))

rectAbsoluteMajorantNonnegative :
  ∀ {Row Column : Set}
    (columns : List Column)
    (matrix : RectMatrix Row Column)
    (vector : Vector Column)
    row →
  0ℚ ≤ rectAbsoluteMajorantApply columns matrix vector row
rectAbsoluteMajorantNonnegative columns matrix vector row =
  Schur.sumNonnegative columns _
    (λ column →
      Schur.productNonnegative
        ∣ matrix row column ∣ ∣ vector column ∣
        (ℚP.0≤∣p∣ (matrix row column))
        (ℚP.0≤∣p∣ (vector column)))

rectWeightedAbsoluteSquareSumExact :
  ∀ {Index : Set}
    (indices : List Index)
    (weight vector : Index → ℚ) →
  Schur.weightedSquareSum indices weight (λ index → ∣ vector index ∣)
  ≡ Sums.sumRational indices
      (λ index → weight index * FiniteL2.square (vector index))
rectWeightedAbsoluteSquareSumExact indices weight vector =
  Sums.sumRationalCong indices _ _
    (λ index →
      cong (weight index *_)
        (Schur.absoluteSquareExact (vector index)))

rectRowApplySquaredBound :
  ∀ {Row Column : Set}
    (columns : List Column)
    (matrix : RectMatrix Row Column)
    (vector : Vector Column)
    row →
  FiniteL2.square (rectApply columns matrix vector row)
  ≤ rectAbsoluteRowMass columns matrix row
      * rectRowWeightedEnergy columns matrix vector row
rectRowApplySquaredBound columns matrix vector row =
  let
    absoluteSquared :
      FiniteL2.square ∣ rectApply columns matrix vector row ∣
      ≤ FiniteL2.square
          (rectAbsoluteMajorantApply columns matrix vector row)
    absoluteSquared =
      Schur.squareMonotoneNonnegative
        ∣ rectApply columns matrix vector row ∣
        (rectAbsoluteMajorantApply columns matrix vector row)
        (ℚP.0≤∣p∣ (rectApply columns matrix vector row))
        (rectAbsoluteMajorantNonnegative columns matrix vector row)
        (rectApplyAbsoluteBound columns matrix vector row)

    weightedCauchy =
      Schur.finiteWeightedCauchySquared
        columns
        (λ column → ∣ matrix row column ∣)
        (λ column → ∣ vector column ∣)
        (λ column → ℚP.0≤∣p∣ (matrix row column))

    combined = ℚP.≤-trans absoluteSquared weightedCauchy
  in
  subst
    (λ lower →
      lower
      ≤ rectAbsoluteRowMass columns matrix row
          * rectRowWeightedEnergy columns matrix vector row)
    (Schur.absoluteSquareExact (rectApply columns matrix vector row))
    (subst
      (λ upper →
        FiniteL2.square ∣ rectApply columns matrix vector row ∣
        ≤ rectAbsoluteRowMass columns matrix row * upper)
      (rectWeightedAbsoluteSquareSumExact
        columns (λ column → ∣ matrix row column ∣) vector)
      combined)

rectRowWeightedEnergyNonnegative :
  ∀ {Row Column : Set}
    (columns : List Column)
    (matrix : RectMatrix Row Column)
    (vector : Vector Column)
    row →
  0ℚ ≤ rectRowWeightedEnergy columns matrix vector row
rectRowWeightedEnergyNonnegative columns matrix vector row =
  Schur.sumNonnegative columns _
    (λ column →
      Schur.productNonnegative
        ∣ matrix row column ∣
        (FiniteL2.square (vector column))
        (ℚP.0≤∣p∣ (matrix row column))
        (FiniteL2.squareNonnegative (vector column)))

sumRectRowsWeightedEnergyExact :
  ∀ {Row Column : Set}
    (rows : List Row)
    (columns : List Column)
    (matrix : RectMatrix Row Column)
    (vector : Vector Column) →
  Sums.sumRational rows
    (rectRowWeightedEnergy columns matrix vector)
  ≡ Sums.sumRational columns
      (λ column →
        FiniteL2.square (vector column)
          * rectAbsoluteColumnMass rows matrix column)
sumRectRowsWeightedEnergyExact rows columns matrix vector =
  trans
    (Fubini.sumSwap rows columns
      (λ row column →
        ∣ matrix row column ∣ * FiniteL2.square (vector column)))
    (Sums.sumRationalCong columns _ _
      (λ column →
        trans
          (Sums.sumRationalCong rows _ _
            (λ row → ℚP.*-comm
              ∣ matrix row column ∣
              (FiniteL2.square (vector column))))
          (Sums.sumRationalScale
            (FiniteL2.square (vector column)) rows
            (λ row → ∣ matrix row column ∣))))

finiteRectangularSchurSquared :
  ∀ {Row Column : Set}
    (rows : List Row)
    (columns : List Column)
    (matrix : RectMatrix Row Column)
    (vector : Vector Column)
    (rowBound columnBound : ℚ) →
  0ℚ ≤ rowBound →
  0ℚ ≤ columnBound →
  (∀ row → rectAbsoluteRowMass columns matrix row ≤ rowBound) →
  (∀ column → rectAbsoluteColumnMass rows matrix column ≤ columnBound) →
  rectVectorNormSq rows (rectApply columns matrix vector)
  ≤ (rowBound * columnBound) * rectVectorNormSq columns vector
finiteRectangularSchurSquared
    rows columns matrix vector rowBound columnBound
    rowBoundNonnegative columnBoundNonnegative
    rowsBounded columnsBounded =
  let
    rowPointwise : ∀ row →
      FiniteL2.square (rectApply columns matrix vector row)
      ≤ rowBound * rectRowWeightedEnergy columns matrix vector row
    rowPointwise row =
      ℚP.≤-trans
        (rectRowApplySquaredBound columns matrix vector row)
        (let
          instance
            energyNN : NonNegative
              (rectRowWeightedEnergy columns matrix vector row)
            energyNN = ℚ.nonNegative
              (rectRowWeightedEnergyNonnegative columns matrix vector row)
         in
         ℚP.*-monoʳ-≤-nonNeg
           (rectRowWeightedEnergy columns matrix vector row)
           (rowsBounded row))

    rowsSummed :
      rectVectorNormSq rows (rectApply columns matrix vector)
      ≤ rowBound
          * Sums.sumRational rows
              (rectRowWeightedEnergy columns matrix vector)
    rowsSummed =
      subst
        (λ upper →
          rectVectorNormSq rows (rectApply columns matrix vector) ≤ upper)
        (Sums.sumRationalScale rowBound rows
          (rectRowWeightedEnergy columns matrix vector))
        (Schur.sumPointwiseBelow rows _ _ rowPointwise)

    columnPointwise : ∀ column →
      FiniteL2.square (vector column)
        * rectAbsoluteColumnMass rows matrix column
      ≤ FiniteL2.square (vector column) * columnBound
    columnPointwise column =
      let
        instance
          squareNN : NonNegative (FiniteL2.square (vector column))
          squareNN = ℚ.nonNegative
            (FiniteL2.squareNonnegative (vector column))
      in
      ℚP.*-monoˡ-≤-nonNeg
        (FiniteL2.square (vector column))
        (columnsBounded column)

    columnsSummed :
      Sums.sumRational columns
        (λ column →
          FiniteL2.square (vector column)
            * rectAbsoluteColumnMass rows matrix column)
      ≤ columnBound * rectVectorNormSq columns vector
    columnsSummed =
      subst
        (λ upper →
          Sums.sumRational columns
            (λ column →
              FiniteL2.square (vector column)
                * rectAbsoluteColumnMass rows matrix column)
          ≤ upper)
        (trans
          (Sums.sumRationalCong columns _ _
            (λ column → ℚP.*-comm
              (FiniteL2.square (vector column)) columnBound))
          (Sums.sumRationalScale columnBound columns
            (λ column → FiniteL2.square (vector column))))
        (Schur.sumPointwiseBelow columns _ _ columnPointwise)

    energyBound :
      Sums.sumRational rows
        (rectRowWeightedEnergy columns matrix vector)
      ≤ columnBound * rectVectorNormSq columns vector
    energyBound =
      subst
        (λ lower → lower ≤ columnBound * rectVectorNormSq columns vector)
        (sym (sumRectRowsWeightedEnergyExact rows columns matrix vector))
        columnsSummed

    scaledEnergyBound :
      rowBound
        * Sums.sumRational rows
            (rectRowWeightedEnergy columns matrix vector)
      ≤ rowBound * (columnBound * rectVectorNormSq columns vector)
    scaledEnergyBound =
      let
        instance
          rowNN : NonNegative rowBound
          rowNN = ℚ.nonNegative rowBoundNonnegative
      in
      ℚP.*-monoˡ-≤-nonNeg rowBound energyBound
  in
  ℚP.≤-trans rowsSummed
    (subst
      (λ upper →
        rowBound
          * Sums.sumRational rows
              (rectRowWeightedEnergy columns matrix vector)
        ≤ upper)
      (sym
        (ℚP.*-assoc rowBound columnBound
          (rectVectorNormSq columns vector)))
      scaledEnergyBound)

finiteRectangularSchurSquaredLevel : ProofLevel
finiteRectangularSchurSquaredLevel = machineChecked
