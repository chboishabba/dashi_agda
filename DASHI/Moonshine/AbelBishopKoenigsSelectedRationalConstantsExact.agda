module DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact where

------------------------------------------------------------------------
-- SELECTED KOENIGS RATIOS: CORRECTED EXACT RATIONAL ARITHMETIC.
--
-- Original constructive exponential/log sources remain separate.
-- This file proves only rational comparisons; it does not manufacture
-- a Bishop fixed point, logarithm branch or physical contraction.
--
-- Original proposed radius 1/8 with lower norm 2499/2000 yields
-- 1/(2499/2000) > 4/5, so kappa=4/5 was NOT valid there.
-- Use radius 1/10 and the weaker certified norm requirement
-- |p| >= 27/20; then |w| >= 5/4 on the disk and
-- |Log'(w)| <= 4/5 (once the Bishop derivative theorem is paid).
--
-- |p| <= 69/50 and kappa <= 4/5 imply
-- beta <= (69/50) * (4/5)^2 = 552/625 < 1.
-- M2 <= 8/25 and radius <= 1/10 give
-- C <= (69/50)*(8/25)*(1/10)^2 < 7/1000.
--
-- All inequalities are exact rational, not float estimations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_; _≤_; _≤ᵇ_; _+_; _-_; _*_)
import Data.Rational.Properties as ℚP

centerReal centerImag : ℚ
centerReal = + 31813 / 100000
centerImag = + 133724 / 100000

newtonRadius selectedLogDiskRadius : ℚ
newtonRadius = + 1 / 200
selectedLogDiskRadius = + 1 / 10

selectedModulusLower selectedModulusUpper : ℚ
selectedModulusLower = + 27 / 20
selectedModulusUpper = + 69 / 50

selectedDiskModulusLower : ℚ
selectedDiskModulusLower = + 5 / 4

selectedLogLipschitz : ℚ
selectedLogLipschitz = + 4 / 5

selectedLogSecondRemainder : ℚ
selectedLogSecondRemainder = + 8 / 25

selectedIncrementRatio : ℚ
selectedIncrementRatio = + 552 / 625

selectedIncrementConstantUpper : ℚ
selectedIncrementConstantUpper = + 7 / 1000

zeroQ oneQ : ℚ
zeroQ = + 0 / 1
oneQ = + 1 / 1

selectedDiskModulusLowerExact :
  selectedModulusLower - selectedLogDiskRadius
    ≡ selectedDiskModulusLower
selectedDiskModulusLowerExact = refl

selectedLipschitzReciprocalExact :
  selectedDiskModulusLower * selectedLogLipschitz ≡ oneQ
selectedLipschitzReciprocalExact = refl

selectedSecondRemainderExact :
  (+ 2 / 1) * selectedDiskModulusLower *
    selectedDiskModulusLower * selectedLogSecondRemainder
  ≡ oneQ
selectedSecondRemainderExact = refl

selectedGeometricRatioExact :
  selectedModulusUpper * selectedLogLipschitz *
    selectedLogLipschitz
  ≡ selectedIncrementRatio
selectedGeometricRatioExact = refl

selectedGeometricRatioLessThanOne :
  selectedIncrementRatio ≤ oneQ
selectedGeometricRatioLessThanOne = ℚP.≤ᵇ⇒≤ tt

selectedGeometricRatioStrictWitness :
  selectedIncrementRatio ≤ (+ 9 / 10)
selectedGeometricRatioStrictWitness = ℚP.≤ᵇ⇒≤ tt

selectedIncrementConstantBound :
  selectedModulusUpper * selectedLogSecondRemainder *
    selectedLogDiskRadius * selectedLogDiskRadius
  ≤ selectedIncrementConstantUpper
selectedIncrementConstantBound = ℚP.≤ᵇ⇒≤ tt

