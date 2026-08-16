module DASHI.Physics.Closure.NSTriadKNComFirstDifferenceCommonHatNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 63 B0 FALSIFIER
--
-- Round62 proved that raw nested hard-low-pass odd-P/Q activity is not a
-- width-one common hat.  A tempting repair is to take one discrete difference
-- in the cutoff index.  This file proves that this is STILL insufficient.
--
-- For the canonical selector and the existing witness
--
--   input shell 0, output shell 3,
--
-- let
--
--   c_j = chi_{<=j}(output) - chi_{<=j}(input),
--   a_0 = c_0,
--   a_{j+1} = c_{j+1} - c_j.
--
-- Then exactly
--
--   a_0 = -1,
--   a_3 =  1,
--   a_0 a_3 = -1 != 0.
--
-- Thus the first-difference annular pieces have a genuine cross-channel at
-- operator-shell separation three.  No width-one `DyadicHatSupport` can contain
-- both indices 0 and 3.
--
-- CONSEQUENCE
--
-- B0 cannot be merely
--
--   raw commutator -> first cutoff difference -> common hat.
--
-- It must use a stronger Bony/paraproduct localization (or an equivalent
-- cancellation/factorization that annihilates the far cross-channel) BEFORE
-- invoking the Round46/47 common-hat machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact as Raw
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat

boolGrade : Bool → ℚ
boolGrade false = 0ℚ
boolGrade true = 1ℚ

rawProjectorGrade :
  ∀ {r} → C3.RealField r → Nat → ℚ
rawProjectorGrade F cutoff =
  boolGrade (LP.lowSelect (Concrete.selectorOnlyModel F) cutoff Raw.farOutput)
  - boolGrade (LP.lowSelect (Concrete.selectorOnlyModel F) cutoff Raw.farInput)

firstDifferenceGrade :
  ∀ {r} → C3.RealField r → Nat → ℚ
firstDifferenceGrade F zero = rawProjectorGrade F zero
firstDifferenceGrade F (suc cutoff) =
  rawProjectorGrade F (suc cutoff) - rawProjectorGrade F cutoff

farInputLowAtThree :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (Concrete.selectorOnlyModel F)
    (suc (suc (suc zero))) Raw.farInput ≡ true
farInputLowAtThree F rewrite Raw.farInputShellIsZero = refl

farOutputLowAtThree :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (Concrete.selectorOnlyModel F)
    (suc (suc (suc zero))) Raw.farOutput ≡ true
farOutputLowAtThree F rewrite Raw.farOutputShellIsThree = refl

rawGradeAtZeroIsNegativeOne :
  ∀ {r} (F : C3.RealField r) →
  rawProjectorGrade F zero ≡ 0ℚ - 1ℚ
rawGradeAtZeroIsNegativeOne F
  rewrite Raw.farOutputHighAtZero F
        | Raw.farInputLowAtZero F = refl

rawGradeAtTwoIsNegativeOne :
  ∀ {r} (F : C3.RealField r) →
  rawProjectorGrade F (suc (suc zero)) ≡ 0ℚ - 1ℚ
rawGradeAtTwoIsNegativeOne F
  rewrite Raw.farOutputHighAtTwo F
        | Raw.farInputLowAtTwo F = refl

rawGradeAtThreeIsZero :
  ∀ {r} (F : C3.RealField r) →
  rawProjectorGrade F (suc (suc (suc zero))) ≡ 0ℚ
rawGradeAtThreeIsZero F
  rewrite farOutputLowAtThree F
        | farInputLowAtThree F = solve []

firstDifferenceAtZeroIsNegativeOne :
  ∀ {r} (F : C3.RealField r) →
  firstDifferenceGrade F zero ≡ 0ℚ - 1ℚ
firstDifferenceAtZeroIsNegativeOne = rawGradeAtZeroIsNegativeOne

firstDifferenceAtThreeIsOne :
  ∀ {r} (F : C3.RealField r) →
  firstDifferenceGrade F (suc (suc (suc zero))) ≡ 1ℚ
firstDifferenceAtThreeIsOne F
  rewrite rawGradeAtThreeIsZero F
        | rawGradeAtTwoIsNegativeOne F = solve []

farFirstDifferenceCrossProductIsNegativeOne :
  ∀ {r} (F : C3.RealField r) →
  firstDifferenceGrade F zero
    * firstDifferenceGrade F (suc (suc (suc zero)))
  ≡ 0ℚ - 1ℚ
farFirstDifferenceCrossProductIsNegativeOne F
  rewrite firstDifferenceAtZeroIsNegativeOne F
        | firstDifferenceAtThreeIsOne F = solve []

negativeOneNonzero : (0ℚ - 1ℚ) ≢ 0ℚ
negativeOneNonzero ()

farFirstDifferenceCrossProductNonzero :
  ∀ {r} (F : C3.RealField r) →
  firstDifferenceGrade F zero
    * firstDifferenceGrade F (suc (suc (suc zero)))
  ≢ 0ℚ
farFirstDifferenceCrossProductNonzero F equality =
  negativeOneNonzero
    (trans (sym (farFirstDifferenceCrossProductIsNegativeOne F)) equality)

zeroAndThreeNotWithinOne :
  ¬ Width.WithinOne zero (suc (suc (suc zero)))
zeroAndThreeNotWithinOne ()

noCommonHatContainsZeroAndThree :
  (support : Hat.DyadicHatSupport) →
  zero Width.∈ Hat.activeShells support →
  suc (suc (suc zero)) Width.∈ Hat.activeShells support →
  ⊥
noCommonHatContainsZeroAndThree support zeroActive threeActive =
  zeroAndThreeNotWithinOne
    (Width.activeShellPairWithinOne
      support zero (suc (suc (suc zero))) zeroActive threeActive)

naiveFirstDifferenceStillHasFarCrossChannel : Bool
naiveFirstDifferenceStillHasFarCrossChannel = true

b0RequiresStrongerThanFirstDifference : Bool
b0RequiresStrongerThanFirstDifference = true

naiveFirstDifferenceStillHasFarCrossChannelIsTrue :
  naiveFirstDifferenceStillHasFarCrossChannel ≡ true
naiveFirstDifferenceStillHasFarCrossChannelIsTrue = refl

b0RequiresStrongerThanFirstDifferenceIsTrue :
  b0RequiresStrongerThanFirstDifference ≡ true
b0RequiresStrongerThanFirstDifferenceIsTrue = refl
