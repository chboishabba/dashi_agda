module DASHI.Physics.YangMills.YMClayCMP102Section45RealFilteredDegreeAcceptanceExact where

------------------------------------------------------------------------
-- Section45 original CMP102: full Bishop REAL majorant for each
-- selected original shifted positive A and B Cauchy cell. All index
-- degrees are preserved, including B first count c=1 and X=0.
-- Remaining debt: one finite filtered-positive SUM/rectangle order
-- theorem plus original factorial mass transport; no Wilson gap.
-- Native pinned Agda 2.9 --safe ACCEPTANCE NOT RUN.
------------------------------------------------------------------------
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Real as R
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Foundations.BishopQuarterFilteredDegreeMajorantExact as M

originalRealQuarterDegree :
  ∀ X → R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ count degree → count ≤ degree →
  R._≤_ (R.pow (R.∣ X ∣) degree)
    (R.pow Half.bishopQuarter count)
originalRealQuarterDegree = M.bishopQuarterDegreeMajorant

originalARealFilteredCell :
  ∀ X → R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ n i j → n ≤ i + j →
  R._≤_ (R.pow (R.∣ X ∣) (suc (i + j)))
    (R.pow Half.bishopQuarter (suc n))
originalARealFilteredCell = M.originalAShiftedCauchyCellQuarterMajorant

originalBRealFilteredCell :
  ∀ X → R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ n i j → n ≤ i + j →
  R._≤_ (R.pow (R.∣ X ∣) (suc (suc (i + j))))
    (R.pow Half.bishopQuarter (suc (suc n)))
originalBRealFilteredCell = M.originalBShiftedCauchyCellQuarterMajorant

originalBFirstRealFilteredCell :
  ∀ X → R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ i j →
  R._≤_ (R.pow (R.∣ X ∣) (suc (suc (i + j))))
    (R.pow Half.bishopQuarter (suc zero))
originalBFirstRealFilteredCell = M.originalBFirstCountQuarterMajorant
