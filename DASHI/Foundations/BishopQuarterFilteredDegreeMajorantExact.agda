module DASHI.Foundations.BishopQuarterFilteredDegreeMajorantExact where

------------------------------------------------------------------------
-- Section45: actual Bishop REAL power majorant for every
-- selected cell of the original CMP102 shifted Cauchy wings.
--
-- Source donors (no invented sequence):
--  Sequence.x≤y∧nonNegx⇒xⁿ≤yⁿ  : u<=q -> u^degree<=q^degree
--  BishopUnitIntervalPower...Antitone : degree>=count ->
--                                     q^degree<=q^count
-- The actual original quarter q is a Bishop-embedded rational.
--
-- Unlike previous Nat exponent bookkeeping, this pays the FULL
-- analytic power inequality for signed X through u=|X| and
-- respects u=0. The remaining source obligation is a finite
-- positive filtered SUM/order comparison for original Cauchy
-- rectangle minus triangle, not a different analytic power law.
--
-- Pinned Agda 2.9 native typechecking UNRUN. Not Wilson/OS/gap.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Integer.Base as Z using (+_; +≤+)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ; *≤*)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Foundations.BishopUnitIntervalPowerSuccessorExact as Powers
import DASHI.Foundations.FiniteCauchyOriginalShiftedDegreeFilterExact as Degree

originalBishopQuarterBelowOne :
  R._≤_ Half.bishopQuarter R.1ℝ
originalBishopQuarterBelowOne =
  P.p≤q⇒p⋆≤q⋆ (+ 1 / 4) 1ℚᵘ
    (Q.*≤* (Z.+≤+ (s≤s z≤n)))

-- A nonnegative original modulus lies below the genuine quarter,
-- hence the embedded quarter itself is nonnegative.
originalBishopQuarterNonnegativeFromModulus :
  ∀ (X : R.ℝ) →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  R.NonNegative Half.bishopQuarter
originalBishopQuarterNonnegativeFromModulus X inside =
  P.0≤x⇒nonNegx
    (P.≤-trans
      (P.nonNegx⇒0≤x (P.nonNeg∣x∣ X))
      inside)

bishopQuarterDegreeMajorant :
  ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ (count degree : Nat) →
  count ≤ degree →
  R._≤_
    (R.pow (R.∣ X ∣) degree)
    (R.pow Half.bishopQuarter count)
bishopQuarterDegreeMajorant X inside count degree count≤degree =
  P.≤-trans
    (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
      degree inside (P.nonNeg∣x∣ X))
    (Powers.bishopUnitIntervalPowerAntitone
      Half.bishopQuarter
      (originalBishopQuarterNonnegativeFromModulus X inside)
      originalBishopQuarterBelowOne
      count≤degree)

-- Actual A(c-1) retained Cauchy cells have degree i+j+1>=c.
originalAShiftedCauchyCellQuarterMajorant :
  ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ n i j →
  n ≤ i + j →
  R._≤_
    (R.pow (R.∣ X ∣) (suc (i + j)))
    (R.pow Half.bishopQuarter (suc n))
originalAShiftedCauchyCellQuarterMajorant X inside n i j cutoff =
  bishopQuarterDegreeMajorant X inside
    (suc n) (suc (i + j))
    (Degree.aOriginalShiftedCellDegree n i j cutoff)

-- Actual B(c-2) retained Cauchy cells have degree i+j+2>=c.
originalBShiftedCauchyCellQuarterMajorant :
  ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ n i j →
  n ≤ i + j →
  R._≤_
    (R.pow (R.∣ X ∣) (suc (suc (i + j))))
    (R.pow Half.bishopQuarter (suc (suc n)))
originalBShiftedCauchyCellQuarterMajorant X inside n i j cutoff =
  bishopQuarterDegreeMajorant X inside
    (suc (suc n)) (suc (suc (i + j)))
    (Degree.bOriginalShiftedCellDegree n i j cutoff)

-- First B count c=1 is a TRUE square singleton, not a c-2
-- negative index. Its exponent is two and is bounded by q^1.
originalBFirstCountQuarterMajorant :
  ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ i j →
  R._≤_
    (R.pow (R.∣ X ∣) (suc (suc (i + j))))
    (R.pow Half.bishopQuarter (suc zero))
originalBFirstCountQuarterMajorant X inside i j =
  bishopQuarterDegreeMajorant X inside
    (suc zero) (suc (suc (i + j)))
    (Degree.bOriginalCountOneDegree i j)
