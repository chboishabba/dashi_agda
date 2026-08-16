module DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact where

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
-- ROUND 62 RAW-SUPPORT FALSIFIER
--
-- The exact Round62 commutator identity shows that raw hard-low-pass odd-P/Q
-- activity at cutoff s is simply
--
--   chi_{<=s}(output) != chi_{<=s}(input).
--
-- Therefore a single transport entry whose input and output shell indices are
-- separated by more than one remains active for several consecutive cutoffs.
-- Such raw cutoff activity CANNOT itself be identified with one width-one
-- dyadic hat.
--
-- Concrete canonical-selector witness:
--
--   input  q = (1,1,0),        j(q)=0,
--   advector p = (7,0,0),
--   output k = (8,1,0)=p+q,   j(k)=3.
--
-- The same literal odd-P/Q transport entry is active at cutoff 0 and cutoff 2.
-- Yet no `DyadicHatSupport` can contain both shell indices 0 and 2, because
-- every concrete hat has width one.
--
-- Hence the Round46/58 common-hat bridge must NOT be interpreted as a theorem
-- about the raw hard-low-pass commutator support.  A genuine B proof must first
-- perform the shell-difference / hatted localization that converts the nested
-- low-pass sweep into adjacent annular pieces, and only THEN identify the
-- resulting pair support with a common dyadic hat.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat

farP farInput farOutput : Z3.FourierMode
farP = Z3.mode (+ 7) (+ 0) (+ 0)
farInput = Z3.mode (+ 1) (+ 1) (+ 0)
farOutput = Z3.mode (+ 8) (+ 1) (+ 0)

farResonance : Z3.addMode farP farInput ≡ farOutput
farResonance = refl

farEntry : Matrix.PhysicalTransportMatrixEntry farInput farOutput
farEntry = Matrix.physical-transport-matrix-entry farP farResonance

farInputInfinityNormIsOne :
  Infinity.infinityNorm farInput ≡ Shell.pow2 zero
farInputInfinityNormIsOne = refl

farOutputInfinityNormIsEight :
  Infinity.infinityNorm farOutput ≡ Shell.pow2 (suc (suc (suc zero)))
farOutputInfinityNormIsEight = refl

farInputShellIsZero : Shell.shellIndex farInput ≡ zero
farInputShellIsZero
  rewrite farInputInfinityNormIsOne
        | Shell.shellIndexPowerOfTwo zero = refl

farOutputShellIsThree :
  Shell.shellIndex farOutput ≡ suc (suc (suc zero))
farOutputShellIsThree
  rewrite farOutputInfinityNormIsEight
        | Shell.shellIndexPowerOfTwo (suc (suc (suc zero))) = refl

farInputLowAtZero :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (Concrete.selectorOnlyModel F) zero farInput ≡ true
farInputLowAtZero F rewrite farInputShellIsZero = refl

farOutputHighAtZero :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (Concrete.selectorOnlyModel F) zero farOutput ≡ false
farOutputHighAtZero F rewrite farOutputShellIsThree = refl

farInputLowAtTwo :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (Concrete.selectorOnlyModel F)
    (suc (suc zero)) farInput ≡ true
farInputLowAtTwo F rewrite farInputShellIsZero = refl

farOutputHighAtTwo :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (Concrete.selectorOnlyModel F)
    (suc (suc zero)) farOutput ≡ false
farOutputHighAtTwo F rewrite farOutputShellIsThree = refl

rawFarEntryActiveAtZero :
  ∀ {r} (F : C3.RealField r) →
  Odd.oddPQActive
    (Concrete.selectorOnlyModel F) zero farInput farOutput ≡ true
rawFarEntryActiveAtZero F
  rewrite farOutputHighAtZero F
        | farInputLowAtZero F = refl

rawFarEntryActiveAtTwo :
  ∀ {r} (F : C3.RealField r) →
  Odd.oddPQActive
    (Concrete.selectorOnlyModel F) (suc (suc zero))
    farInput farOutput ≡ true
rawFarEntryActiveAtTwo F
  rewrite farOutputHighAtTwo F
        | farInputLowAtTwo F = refl

zeroAndTwoNotWithinOne : ¬ Width.WithinOne zero (suc (suc zero))
zeroAndTwoNotWithinOne ()

noCommonHatContainsZeroAndTwo :
  (support : Hat.DyadicHatSupport) →
  zero Width.∈ Hat.activeShells support →
  suc (suc zero) Width.∈ Hat.activeShells support →
  ⊥
noCommonHatContainsZeroAndTwo support zeroActive twoActive =
  zeroAndTwoNotWithinOne
    (Width.activeShellPairWithinOne
      support zero (suc (suc zero)) zeroActive twoActive)

record RawHardLowPassPairClaim : Set where
  field
    commonHat : Hat.DyadicHatSupport
    cutoffZeroInHat : zero Width.∈ Hat.activeShells commonHat
    cutoffTwoInHat : suc (suc zero) Width.∈ Hat.activeShells commonHat

open RawHardLowPassPairClaim public

rawHardLowPassPairClaimImpossible : RawHardLowPassPairClaim → ⊥
rawHardLowPassPairClaimImpossible claim =
  noCommonHatContainsZeroAndTwo
    (commonHat claim) (cutoffZeroInHat claim) (cutoffTwoInHat claim)

rawHardLowPassOddPQCanSpanMoreThanWidthOne : Bool
rawHardLowPassOddPQCanSpanMoreThanWidthOne = true

rawHardLowPassCannotBeTheCommonHatSupport : Bool
rawHardLowPassCannotBeTheCommonHatSupport = true

hattedDifferenceLocalizationRequiredBeforeCommonHat : Bool
hattedDifferenceLocalizationRequiredBeforeCommonHat = true

rawHardLowPassOddPQCanSpanMoreThanWidthOneIsTrue :
  rawHardLowPassOddPQCanSpanMoreThanWidthOne ≡ true
rawHardLowPassOddPQCanSpanMoreThanWidthOneIsTrue = refl

rawHardLowPassCannotBeTheCommonHatSupportIsTrue :
  rawHardLowPassCannotBeTheCommonHatSupport ≡ true
rawHardLowPassCannotBeTheCommonHatSupportIsTrue = refl

hattedDifferenceLocalizationRequiredBeforeCommonHatIsTrue :
  hattedDifferenceLocalizationRequiredBeforeCommonHat ≡ true
hattedDifferenceLocalizationRequiredBeforeCommonHatIsTrue = refl
