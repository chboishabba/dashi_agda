module DASHI.Analysis.NonArchimedeanHalfPeriodCharacterClassifierExact where

------------------------------------------------------------------------
-- HALF-PERIOD CHARACTER CLASSIFIER
--
-- For dyadic characters χ_k(x)=ζ^(kx), the deck shift x |-> x+2^(n-1)
-- acts by the half-period phase ζ^(k 2^(n-1)).  Once one owns
--
--   ζ^(2^(n-1)) = -1
--
-- this phase is (-1)^k, so the deck -1 eigenspace is exactly the odd
-- frequencies.  This module isolates that small producer so the stronger
-- tau-odd <-> odd-frequency statement is not left as an opaque semantic weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record HalfPeriodCharacterData : Set₁ where
  field
    Frequency : Set
    Point : Set
    Scalar : Set

    characterValue : Frequency → Point → Scalar
    deckShift : Point → Point
    negate : Scalar → Scalar

    oddFrequency : Frequency → Set
    evenFrequency : Frequency → Set

    halfPeriodPhase : Frequency → Scalar

    characterDeckShiftFactorization :
      (k : Frequency) (x : Point) → Set

    primitiveHalfTurnIsMinusOne : Set

    oddPhaseIsMinusOne :
      (k : Frequency) → oddFrequency k → Set

    evenPhaseIsPlusOne :
      (k : Frequency) → evenFrequency k → Set

    minusOnePhaseActsAsNegation :
      (k : Frequency) (x : Point) → oddFrequency k →
      characterValue k (deckShift x) ≡ negate (characterValue k x)

    tauOddCharacterForcesOddPhase :
      (k : Frequency) →
      ((x : Point) →
        characterValue k (deckShift x) ≡ negate (characterValue k x)) →
      oddFrequency k

open HalfPeriodCharacterData public

TauOddCharacter :
  (data : HalfPeriodCharacterData) →
  Frequency data → Set
TauOddCharacter data k =
  (x : Point data) →
  characterValue data k (deckShift data x)
  ≡ negate data (characterValue data k x)

oddImpliesTauOdd :
  (data : HalfPeriodCharacterData) →
  (k : Frequency data) →
  oddFrequency data k →
  TauOddCharacter data k
oddImpliesTauOdd data k hk x =
  minusOnePhaseActsAsNegation data k x hk

tauOddImpliesOdd :
  (data : HalfPeriodCharacterData) →
  (k : Frequency data) →
  TauOddCharacter data k →
  oddFrequency data k
tauOddImpliesOdd data k h =
  tauOddCharacterForcesOddPhase data k h

record HalfPeriodClassifierStatus : Set where
  constructor halfPeriodClassifierStatus
  field
    characterShiftFactorizationIsElementary : Bool
    primitiveHalfTurnProducerRequired : Bool
    parityPhaseProducerRequired : Bool
    oddTauOddIffCompilesOnceThoseProducersExist : Bool
    finalSpectralMagnitudeRequiredHere : Bool

canonicalHalfPeriodClassifierStatus : HalfPeriodClassifierStatus
canonicalHalfPeriodClassifierStatus =
  halfPeriodClassifierStatus true true true true false


data HalfPeriodObligation : Set where
  provePrimitiveHalfTurnMinusOne : HalfPeriodObligation
  proveParityOfHalfTurnPowers : HalfPeriodObligation
  compileOddTauOddIff : HalfPeriodObligation
  assumeSpectralCircleMagnitude : HalfPeriodObligation


data HalfPeriodDisposition : Set where
  live : HalfPeriodDisposition
  downstream : HalfPeriodDisposition
  forbiddenShortcut : HalfPeriodDisposition

halfPeriodDisposition : HalfPeriodObligation → HalfPeriodDisposition
halfPeriodDisposition provePrimitiveHalfTurnMinusOne = live
halfPeriodDisposition proveParityOfHalfTurnPowers = live
halfPeriodDisposition compileOddTauOddIff = downstream
halfPeriodDisposition assumeSpectralCircleMagnitude = forbiddenShortcut

highestAlphaHalfPeriodPath : List HalfPeriodObligation
highestAlphaHalfPeriodPath =
  provePrimitiveHalfTurnMinusOne ∷
  proveParityOfHalfTurnPowers ∷
  compileOddTauOddIff ∷
  []

oddTauOddIsCompilerOutputOnceHalfPeriodOwned :
  HalfPeriodClassifierStatus.oddTauOddIffCompilesOnceThoseProducersExist
    canonicalHalfPeriodClassifierStatus
  ≡ true
oddTauOddIsCompilerOutputOnceHalfPeriodOwned = refl
