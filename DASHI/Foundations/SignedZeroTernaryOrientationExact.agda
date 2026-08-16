module DASHI.Foundations.SignedZeroTernaryOrientationExact where

------------------------------------------------------------------------
-- EXISTING DASHI SOURCE SURFACES
--
-- DASHI.Physics.Closure.SignedZeroTorsionReceipt records +0 and -0 over the
-- same scalar neutral value, distinguished by arrival direction and
-- torsion/helicity orientation.
--
-- DASHI.Foundations.CounterpositionOrderedJoinExact records binary opposition
-- as the zero-free subcarrier of balanced ternary.
--
-- DASHI CONTRIBUTION
--
-- Complete that zero-free binary orientation to the ternary signed-neutral
-- axis
--
--   -0  ->  0  ->  +0.
--
-- The centre is not a third scalar zero. All three points project to the same
-- neutral scalar; the outer points recover the already-formal +0/-0 path
-- bookkeeping, while the centre records no directed arrival/torsion witness.
-- Thus the old C2 polarity is retained exactly as the extremal subcarrier of
-- a C3-shaped orientation axis rather than treated as the whole geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Optional (A : Set) : Set where
  none : Optional A
  some : A → Optional A

import DASHI.Foundations.StageSymmetryCarrierTowerExact as Sym
import DASHI.Physics.Closure.SignedZeroTorsionReceipt as Signed

data SignedNeutralPhase3 : Set where
  minusZeroPhase neutralZeroPhase plusZeroPhase : SignedNeutralPhase3

rotateSignedNeutral : SignedNeutralPhase3 → SignedNeutralPhase3
rotateSignedNeutral minusZeroPhase = neutralZeroPhase
rotateSignedNeutral neutralZeroPhase = plusZeroPhase
rotateSignedNeutral plusZeroPhase = minusZeroPhase

rotateSignedNeutralOrderThree :
  (phase : SignedNeutralPhase3) →
  rotateSignedNeutral
    (rotateSignedNeutral (rotateSignedNeutral phase)) ≡ phase
rotateSignedNeutralOrderThree minusZeroPhase = refl
rotateSignedNeutralOrderThree neutralZeroPhase = refl
rotateSignedNeutralOrderThree plusZeroPhase = refl

toC3 : SignedNeutralPhase3 → Sym.C3
toC3 minusZeroPhase = Sym.negative
toC3 neutralZeroPhase = Sym.neutral
toC3 plusZeroPhase = Sym.positive

fromC3 : Sym.C3 → SignedNeutralPhase3
fromC3 Sym.negative = minusZeroPhase
fromC3 Sym.neutral = neutralZeroPhase
fromC3 Sym.positive = plusZeroPhase

fromAfterToC3 :
  (phase : SignedNeutralPhase3) →
  fromC3 (toC3 phase) ≡ phase
fromAfterToC3 minusZeroPhase = refl
fromAfterToC3 neutralZeroPhase = refl
fromAfterToC3 plusZeroPhase = refl

toAfterFromC3 :
  (phase : Sym.C3) →
  toC3 (fromC3 phase) ≡ phase
toAfterFromC3 Sym.negative = refl
toAfterFromC3 Sym.neutral = refl
toAfterFromC3 Sym.positive = refl

------------------------------------------------------------------------
-- Existing binary orientation embeds as the two noncentral extrema.
------------------------------------------------------------------------

embedC2Extremal : Sym.C2 → SignedNeutralPhase3
embedC2Extremal Sym.direct = plusZeroPhase
embedC2Extremal Sym.inverse = minusZeroPhase

binaryExtremalNeverNeutral :
  (orientation : Sym.C2) →
  embedC2Extremal orientation ≡ neutralZeroPhase → ⊥
binaryExtremalNeverNeutral Sym.direct ()
binaryExtremalNeverNeutral Sym.inverse ()

------------------------------------------------------------------------
-- Scalar projection and path-sensitive signed-zero refinement.
------------------------------------------------------------------------

neutralScalar : SignedNeutralPhase3 → Signed.ScalarNeutralValue
neutralScalar minusZeroPhase = Signed.neutralScalarZero
neutralScalar neutralZeroPhase = Signed.neutralScalarZero
neutralScalar plusZeroPhase = Signed.neutralScalarZero

allSignedNeutralPhasesShareScalar :
  (left right : SignedNeutralPhase3) →
  neutralScalar left ≡ neutralScalar right
allSignedNeutralPhasesShareScalar minusZeroPhase minusZeroPhase = refl
allSignedNeutralPhasesShareScalar minusZeroPhase neutralZeroPhase = refl
allSignedNeutralPhasesShareScalar minusZeroPhase plusZeroPhase = refl
allSignedNeutralPhasesShareScalar neutralZeroPhase minusZeroPhase = refl
allSignedNeutralPhasesShareScalar neutralZeroPhase neutralZeroPhase = refl
allSignedNeutralPhasesShareScalar neutralZeroPhase plusZeroPhase = refl
allSignedNeutralPhasesShareScalar plusZeroPhase minusZeroPhase = refl
allSignedNeutralPhasesShareScalar plusZeroPhase neutralZeroPhase = refl
allSignedNeutralPhasesShareScalar plusZeroPhase plusZeroPhase = refl

signedZeroWitness : SignedNeutralPhase3 → Optional Signed.SignedZero
signedZeroWitness minusZeroPhase = some Signed.minusZero
signedZeroWitness neutralZeroPhase = none
signedZeroWitness plusZeroPhase = some Signed.plusZero

arrivalWitness :
  SignedNeutralPhase3 → Optional Signed.NeutralArrivalDirection
arrivalWitness minusZeroPhase =
  some Signed.arrivedFromNegativeDirection
arrivalWitness neutralZeroPhase = none
arrivalWitness plusZeroPhase =
  some Signed.arrivedFromPositiveDirection

torsionWitness :
  SignedNeutralPhase3 → Optional Signed.TorsionOrientation
torsionWitness minusZeroPhase =
  some Signed.negativeTorsionHelicityOrientation
torsionWitness neutralZeroPhase = none
torsionWitness plusZeroPhase =
  some Signed.positiveTorsionHelicityOrientation

minusPhaseRecoversExistingMinusZero :
  signedZeroWitness minusZeroPhase ≡ some Signed.minusZero
minusPhaseRecoversExistingMinusZero = refl

plusPhaseRecoversExistingPlusZero :
  signedZeroWitness plusZeroPhase ≡ some Signed.plusZero
plusPhaseRecoversExistingPlusZero = refl

centreCarriesNoDirectedSignedZero :
  signedZeroWitness neutralZeroPhase ≡ none
centreCarriesNoDirectedSignedZero = refl

------------------------------------------------------------------------
-- Authority / interpretation boundary.
------------------------------------------------------------------------

record SignedZeroTernaryOrientationBoundary : Set where
  field
    ternaryCompletionConstructed : Bool
    ternaryCompletionConstructedIsTrue :
      ternaryCompletionConstructed ≡ true

    binaryPolarityRetainedAsExtremalSubcarrier : Bool
    binaryPolarityRetainedAsExtremalSubcarrierIsTrue :
      binaryPolarityRetainedAsExtremalSubcarrier ≡ true

    centreIsSecondScalarZero : Bool
    centreIsSecondScalarZeroIsFalse :
      centreIsSecondScalarZero ≡ false

    directedSignedZeroRequiredAtCentre : Bool
    directedSignedZeroRequiredAtCentreIsFalse :
      directedSignedZeroRequiredAtCentre ≡ false

canonicalSignedZeroTernaryOrientationBoundary :
  SignedZeroTernaryOrientationBoundary
canonicalSignedZeroTernaryOrientationBoundary =
  record
    { ternaryCompletionConstructed = true
    ; ternaryCompletionConstructedIsTrue = refl
    ; binaryPolarityRetainedAsExtremalSubcarrier = true
    ; binaryPolarityRetainedAsExtremalSubcarrierIsTrue = refl
    ; centreIsSecondScalarZero = false
    ; centreIsSecondScalarZeroIsFalse = refl
    ; directedSignedZeroRequiredAtCentre = false
    ; directedSignedZeroRequiredAtCentreIsFalse = refl
    }
