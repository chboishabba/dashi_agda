module DASHI.ComputerScience.TekumSSPFRACTRANBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Core.DependentRecoverableProjectionExact as Recoverable
import DASHI.Foundations.SSPTritCarrier as SSPTrit
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- 1. Direct same-carrier Tekum-trit <-> SSP-trit bridge.

tekumTritToSSP : Trit.Trit → SSPTrit.SSPTrit
tekumTritToSSP = SSPTrit.fromTrit

sspToTekumTrit : SSPTrit.SSPTrit → Trit.Trit
sspToTekumTrit = SSPTrit.toTrit

tekumSSPRoundTrip :
  (t : Trit.Trit) → sspToTekumTrit (tekumTritToSSP t) ≡ t
tekumSSPRoundTrip = SSPTrit.toTrit-fromTrit

sspTekumRoundTrip :
  (t : SSPTrit.SSPTrit) → tekumTritToSSP (sspToTekumTrit t) ≡ t
sspTekumRoundTrip = SSPTrit.fromTrit-toTrit

------------------------------------------------------------------------
-- 2. Position-aware signed SSP/FRACTRAN presentation.

record PositionedTrit : Set where
  constructor positionedTrit
  field
    position : Nat
    digit : Trit.Trit
open PositionedTrit public

orientationOfTrit : Trit.Trit → Signed.FibreOrientation
orientationOfTrit Trit.neg = Signed.inverseOrientation
orientationOfTrit Trit.zer = Signed.mediatedOrientation
orientationOfTrit Trit.pos = Signed.forwardOrientation

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

weightedMultiplicity : PositionedTrit → Signed.SignedMultiplicity
weightedMultiplicity (positionedTrit k Trit.neg) =
  Signed.negativeMultiplicity (pow3 k)
weightedMultiplicity (positionedTrit k Trit.zer) =
  Signed.zeroMultiplicity
weightedMultiplicity (positionedTrit k Trit.pos) =
  Signed.positiveMultiplicity (pow3 k)

------------------------------------------------------------------------
-- 3. Dependent residual: orientation is the coarse SSP/FRACTRAN surface;
--    position reopens the exact Tekum digit and radix weight.

data OrientationResidual : Signed.FibreOrientation → Set where
  inverseAt : Nat → OrientationResidual Signed.inverseOrientation
  mediatedAt : Nat → OrientationResidual Signed.mediatedOrientation
  forwardAt : Nat → OrientationResidual Signed.forwardOrientation

positionedProject : PositionedTrit → Signed.FibreOrientation
positionedProject (positionedTrit k t) = orientationOfTrit t

positionedResidual :
  (x : PositionedTrit) → OrientationResidual (positionedProject x)
positionedResidual (positionedTrit k Trit.neg) = inverseAt k
positionedResidual (positionedTrit k Trit.zer) = mediatedAt k
positionedResidual (positionedTrit k Trit.pos) = forwardAt k

positionedReopen :
  (o : Signed.FibreOrientation) → OrientationResidual o → PositionedTrit
positionedReopen Signed.inverseOrientation (inverseAt k) =
  positionedTrit k Trit.neg
positionedReopen Signed.mediatedOrientation (mediatedAt k) =
  positionedTrit k Trit.zer
positionedReopen Signed.forwardOrientation (forwardAt k) =
  positionedTrit k Trit.pos

positionedReopenExact :
  (x : PositionedTrit) →
  positionedReopen (positionedProject x) (positionedResidual x) ≡ x
positionedReopenExact (positionedTrit k Trit.neg) = refl
positionedReopenExact (positionedTrit k Trit.zer) = refl
positionedReopenExact (positionedTrit k Trit.pos) = refl

tekumPositionedSSPProjection :
  Recoverable.DependentExactRecoverableProjection
    PositionedTrit Signed.FibreOrientation
tekumPositionedSSPProjection =
  Recoverable.dependentExactRecoverableProjection
    OrientationResidual
    positionedProject
    positionedResidual
    positionedReopen
    positionedReopenExact

positionedCodeSeparatesTekumDigit :
  Recoverable.DependentCodeSeparating tekumPositionedSSPProjection
positionedCodeSeparatesTekumDigit =
  Recoverable.dependentCodeSeparating tekumPositionedSSPProjection

------------------------------------------------------------------------
-- 4. Executable FRACTRAN-style instruction compiler.
--
-- +1 at position k -> 3^k introductions of the selected prime.
-- -1 at position k -> 3^k inverse-prime introductions.
--  0               -> no arithmetic instruction.

repeatInstruction : Nat → Signed.WeaveInstruction → List Signed.WeaveInstruction
repeatInstruction zero instruction = []
repeatInstruction (suc n) instruction =
  instruction ∷ repeatInstruction n instruction

compilePositionedOn :
  Signed.SSPPrime → PositionedTrit → List Signed.WeaveInstruction
compilePositionedOn lane (positionedTrit k Trit.neg) =
  repeatInstruction (pow3 k) (Signed.introduceInversePrime lane)
compilePositionedOn lane (positionedTrit k Trit.zer) = []
compilePositionedOn lane (positionedTrit k Trit.pos) =
  repeatInstruction (pow3 k) (Signed.introducePrime lane)

positiveUnitAtZeroCompilesToOnePrime :
  compilePositionedOn Signed.ssp3 (positionedTrit 0 Trit.pos)
  ≡ Signed.introducePrime Signed.ssp3 ∷ []
positiveUnitAtZeroCompilesToOnePrime = refl

negativeUnitAtOneCompilesToThreeInversePrimes :
  compilePositionedOn Signed.ssp3 (positionedTrit 1 Trit.neg)
  ≡ Signed.introduceInversePrime Signed.ssp3
    ∷ Signed.introduceInversePrime Signed.ssp3
    ∷ Signed.introduceInversePrime Signed.ssp3
    ∷ []
negativeUnitAtOneCompilesToThreeInversePrimes = refl

record TekumSSPFRACTRANBoundary : Set where
  constructor tekumSSPFractranBoundary
  field
    tekumTritAndSSPTritAreExactlyBidi : Bool
    positionedOrientationPlusResidualReopensExactly : Bool
    radixWeightCompilesToSignedPrimeMultiplicity : Bool
    selectedPrimeLaneIsRepresentationChoiceNotNumericIdentity : Bool
    coarseOrientationAloneRetainsPosition : Bool

canonicalTekumSSPFRACTRANBoundary : TekumSSPFRACTRANBoundary
canonicalTekumSSPFRACTRANBoundary =
  tekumSSPFractranBoundary true true true true false
