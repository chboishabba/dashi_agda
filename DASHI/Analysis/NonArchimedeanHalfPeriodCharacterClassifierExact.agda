module DASHI.Analysis.NonArchimedeanHalfPeriodCharacterClassifierExact where

------------------------------------------------------------------------
-- HALF-PERIOD CHARACTER CLASSIFIER
--
-- For dyadic characters chi_k(x)=zeta^(kx), the deck shift
-- x |-> x+2^(n-1) acts by the half-period phase zeta^(k 2^(n-1)).
-- Once zeta^(2^(n-1))=-1, the phase is (-1)^k.  Therefore the deck -1
-- eigenspace is exactly the odd-frequency character sector.
--
-- The converse is compiled, not assumed: evaluate the tau-odd equation at
-- x=0, recover halfPeriodPhase k = -1, then rule out the even branch because
-- even frequencies have phase +1 and +1 != -1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

data Empty : Set where

absurd : ∀ {A : Set} → Empty → A
absurd ()

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

record HalfPeriodCharacterData : Set₁ where
  field
    Frequency : Set
    Point : Set
    Scalar : Set

    characterValue : Frequency → Point → Scalar
    deckShift : Point → Point
    scale : Scalar → Scalar → Scalar
    negate : Scalar → Scalar

    one minusOne : Scalar
    zeroPoint : Point

    oddFrequency : Frequency → Set
    evenFrequency : Frequency → Set
    halfPeriodPhase : Frequency → Scalar

    characterDeckShiftFactorization :
      (k : Frequency) (x : Point) →
      characterValue k (deckShift x)
      ≡ scale (halfPeriodPhase k) (characterValue k x)

    primitiveHalfTurnIsMinusOne : Set

    oddPhaseIsMinusOne :
      (k : Frequency) → oddFrequency k →
      halfPeriodPhase k ≡ minusOne

    evenPhaseIsPlusOne :
      (k : Frequency) → evenFrequency k →
      halfPeriodPhase k ≡ one

    scaleMinusOneIsNegation :
      (value : Scalar) → scale minusOne value ≡ negate value

    phaseObservedAtZero :
      (k : Frequency) →
      characterValue k (deckShift zeroPoint) ≡ halfPeriodPhase k

    negatedCharacterAtZeroIsMinusOne :
      (k : Frequency) →
      negate (characterValue k zeroPoint) ≡ minusOne

    paritySplit :
      (k : Frequency) → Either (oddFrequency k) (evenFrequency k)

    oneNotMinusOne : one ≡ minusOne → Empty

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
  trans
    (characterDeckShiftFactorization data k x)
    (trans
      (cong
        (λ phase → scale data phase (characterValue data k x))
        (oddPhaseIsMinusOne data k hk))
      (scaleMinusOneIsNegation data (characterValue data k x)))

phaseMinusOneFromTauOdd :
  (data : HalfPeriodCharacterData) →
  (k : Frequency data) →
  TauOddCharacter data k →
  halfPeriodPhase data k ≡ minusOne data
phaseMinusOneFromTauOdd data k h =
  trans
    (sym (phaseObservedAtZero data k))
    (trans
      (h (zeroPoint data))
      (negatedCharacterAtZeroIsMinusOne data k))

tauOddImpliesOdd :
  (data : HalfPeriodCharacterData) →
  (k : Frequency data) →
  TauOddCharacter data k →
  oddFrequency data k
tauOddImpliesOdd data k h with paritySplit data k
... | left hk = hk
... | right hk-even =
  absurd
    (oneNotMinusOne data
      (trans
        (sym (evenPhaseIsPlusOne data k hk-even))
        (phaseMinusOneFromTauOdd data k h)))

record HalfPeriodClassifierStatus : Set where
  constructor halfPeriodClassifierStatus
  field
    characterShiftFactorizationIsElementary : Bool
    primitiveHalfTurnProducerRequired : Bool
    parityPhaseProducerRequired : Bool
    tauOddConverseIsCompiledNotAssumed : Bool
    oddTauOddIffCompilesOnceThoseProducersExist : Bool
    finalSpectralMagnitudeRequiredHere : Bool

canonicalHalfPeriodClassifierStatus : HalfPeriodClassifierStatus
canonicalHalfPeriodClassifierStatus =
  halfPeriodClassifierStatus true true true true true false


data HalfPeriodObligation : Set where
  instantiatePrimitiveHalfTurnMinusOne : HalfPeriodObligation
  instantiateParityOfMinusOnePowers : HalfPeriodObligation
  instantiateZeroEvaluation : HalfPeriodObligation
  compileOddTauOddIff : HalfPeriodObligation
  assumeSpectralCircleMagnitude : HalfPeriodObligation


data HalfPeriodDisposition : Set where
  upstreamReusable : HalfPeriodDisposition
  live : HalfPeriodDisposition
  downstream : HalfPeriodDisposition
  forbiddenShortcut : HalfPeriodDisposition

halfPeriodDisposition : HalfPeriodObligation → HalfPeriodDisposition
halfPeriodDisposition instantiatePrimitiveHalfTurnMinusOne = upstreamReusable
halfPeriodDisposition instantiateParityOfMinusOnePowers = upstreamReusable
halfPeriodDisposition instantiateZeroEvaluation = live
halfPeriodDisposition compileOddTauOddIff = downstream
halfPeriodDisposition assumeSpectralCircleMagnitude = forbiddenShortcut

highestAlphaHalfPeriodPath : List HalfPeriodObligation
highestAlphaHalfPeriodPath =
  instantiatePrimitiveHalfTurnMinusOne ∷
  instantiateParityOfMinusOnePowers ∷
  instantiateZeroEvaluation ∷
  compileOddTauOddIff ∷
  []

oddTauOddIsCompilerOutputOnceHalfPeriodOwned :
  HalfPeriodClassifierStatus.oddTauOddIffCompilesOnceThoseProducersExist
    canonicalHalfPeriodClassifierStatus
  ≡ true
oddTauOddIsCompilerOutputOnceHalfPeriodOwned = refl

tauOddConverseIsNotAnIndependentHypothesis :
  HalfPeriodClassifierStatus.tauOddConverseIsCompiledNotAssumed
    canonicalHalfPeriodClassifierStatus
  ≡ true
tauOddConverseIsNotAnIndependentHypothesis = refl
