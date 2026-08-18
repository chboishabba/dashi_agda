module DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteApplyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Rectangular companion to the existing finite weighted-kernel contraction.
-- For a finite Row x Column matrix A and vector v with |v_j| <= M,
--
--   |(A v)_i| <= M sum_j |A_ij|.
--
-- The theorem is only finite triangle inequality plus absolute-value
-- multiplicativity.  It is factored out because the selected KKT Schur cross
-- map applies the 768 x 3072 gauge-defect matrix to a twelve-coordinate family
-- of literal 0/1 average-adjoint vectors.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass

rectApply :
  ∀ {Row Column : Set} →
  List Column → Mass.RectMatrix Row Column → (Column → ℚ) → Row → ℚ
rectApply columns matrix vector row =
  Sums.sumRational columns (λ column → matrix row column * vector column)

rectApplyAbsoluteBound :
  ∀ {Row Column : Set}
    (columns : List Column)
    (matrix : Mass.RectMatrix Row Column)
    (vector : Column → ℚ)
    (majorant : ℚ) →
  0ℚ ≤ majorant →
  (∀ column → ∣ vector column ∣ ≤ majorant) →
  ∀ row →
  ∣ rectApply columns matrix vector row ∣
  ≤ majorant * Mass.absoluteRectRowMass columns matrix row
rectApplyAbsoluteBound [] matrix vector majorant majorantNN vectorBound row =
  ℚP.≤-refl
rectApplyAbsoluteBound (column ∷ columns) matrix vector majorant
    majorantNN vectorBound row =
  let
    instance
      majorantNonnegative : NonNegative majorant
      majorantNonnegative = ℚ.nonNegative majorantNN
      entryAbsNonnegative : NonNegative ∣ matrix row column ∣
      entryAbsNonnegative = ℚP.∣-∣-nonNeg (matrix row column)

    headBound :
      ∣ matrix row column * vector column ∣
      ≤ majorant * ∣ matrix row column ∣
    headBound =
      subst
        (λ lower → lower ≤ majorant * ∣ matrix row column ∣)
        (ℚP.∣p*q∣≡∣p∣*∣q∣ (matrix row column) (vector column))
        (subst
          (λ upper →
            ∣ matrix row column ∣ * ∣ vector column ∣ ≤ upper)
          (ℚP.*-comm majorant ∣ matrix row column ∣)
          (ℚP.*-monoˡ-≤-nonNeg
            ∣ matrix row column ∣ (vectorBound column)))

    tailBound :
      ∣ rectApply columns matrix vector row ∣
      ≤ majorant * Mass.absoluteRectRowMass columns matrix row
    tailBound = rectApplyAbsoluteBound
      columns matrix vector majorant majorantNN vectorBound row

    summed = ℚP.+-mono-≤ headBound tailBound
  in
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (matrix row column * vector column)
      (rectApply columns matrix vector row))
    (subst
      (λ upper →
        majorant * ∣ matrix row column ∣
          + majorant * Mass.absoluteRectRowMass columns matrix row
        ≤ upper)
      (sym
        (ℚRing.solve-∀ majorant
          ∣ matrix row column ∣
          (Mass.absoluteRectRowMass columns matrix row)))
      summed)

rectApplyAbsoluteUnitBound :
  ∀ {Row Column : Set}
    (columns : List Column)
    (matrix : Mass.RectMatrix Row Column)
    (vector : Column → ℚ) →
  (∀ column → ∣ vector column ∣ ≤ (+ 1 / 1)) →
  ∀ row →
  ∣ rectApply columns matrix vector row ∣
  ≤ Mass.absoluteRectRowMass columns matrix row
rectApplyAbsoluteUnitBound columns matrix vector vectorBound row =
  subst
    (λ upper →
      ∣ rectApply columns matrix vector row ∣ ≤ upper)
    (ℚRing.solve-∀ (Mass.absoluteRectRowMass columns matrix row))
    (rectApplyAbsoluteBound columns matrix vector (+ 1 / 1)
      (ℚP.nonNegative⁻¹ (+ 1 / 1)) vectorBound row)

finiteRectangularAbsoluteApplyLevel : ProofLevel
finiteRectangularAbsoluteApplyLevel = machineChecked
