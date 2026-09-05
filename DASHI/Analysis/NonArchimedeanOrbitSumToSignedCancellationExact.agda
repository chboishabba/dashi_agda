module DASHI.Analysis.NonArchimedeanOrbitSumToSignedCancellationExact where

------------------------------------------------------------------------
-- ORBIT SUM -> SIGNED CANCELLATION
--
-- Once C2=-C1, factorwise character conjugation gives
--
--   W2 = omega^(sum C1) * W1.
--
-- If the orbit sum is the dyadic half period, primitive-root arithmetic gives
-- omega^(sum C1) = -1.  Therefore W2=-W1 and W1+W2=0.
--
-- This is the shortest signed path to the existing minus-two compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record OrbitSumPhaseCancellation : Set₁ where
  field
    Scalar : Set
    zero negOne : Scalar
    add multiply : Scalar → Scalar → Scalar
    negate : Scalar → Scalar

    W1 W2 orbitSumPhase : Scalar

    negativeOrbitWeightFactorsThroughOrbitSumPhase :
      W2 ≡ multiply orbitSumPhase W1

    orbitSumPhaseIsMinusOne :
      orbitSumPhase ≡ negOne

    negOneActsAsNegation :
      multiply negOne W1 ≡ negate W1

    addInverse :
      add W1 (negate W1) ≡ zero

open OrbitSumPhaseCancellation public

negativeOrbitWeightIsNegative :
  (data : OrbitSumPhaseCancellation) →
  W2 data ≡ negate data (W1 data)
negativeOrbitWeightIsNegative data =
  trans
    (negativeOrbitWeightFactorsThroughOrbitSumPhase data)
    (trans
      (cong (λ phase → multiply data phase (W1 data))
        (orbitSumPhaseIsMinusOne data))
      (negOneActsAsNegation data))

orbitWeightsCancel :
  (data : OrbitSumPhaseCancellation) →
  add data (W1 data) (W2 data) ≡ zero data
orbitWeightsCancel data =
  trans
    (cong (add data (W1 data))
      (negativeOrbitWeightIsNegative data))
    (addInverse data)

record SignedClosureStatus : Set where
  constructor signedClosureStatus
  field
    negativeOrbitConjugationOwnedStructurally : Bool
    orbitSumHalfPeriodIsEnoughForMinusSign : Bool
    explicitComplexPhaseValueRequired : Bool
    cancellationCompilesFromOrbitSumPhase : Bool
    pairedProductTwoStillRequiredForMinusTwoSquares : Bool

canonicalSignedClosureStatus : SignedClosureStatus
canonicalSignedClosureStatus =
  signedClosureStatus true true false true true

orbitSumIsSufficientSignedProducer :
  SignedClosureStatus.orbitSumHalfPeriodIsEnoughForMinusSign
    canonicalSignedClosureStatus
  ≡ true
orbitSumIsSufficientSignedProducer = refl
