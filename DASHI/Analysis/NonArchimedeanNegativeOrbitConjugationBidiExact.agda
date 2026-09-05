module DASHI.Analysis.NonArchimedeanNegativeOrbitConjugationBidiExact where

------------------------------------------------------------------------
-- NEGATIVE ORBIT -> CONJUGATE ORBIT WEIGHT
--
-- For the dyadic character weight
--
--   w(k) = 1 + omega^(-k),
--
-- complex conjugation sends w(k) to w(-k).  Hence a genuine negative-orbit
-- receipt C2 = -C1 transports the full orbit product to
--
--   W2 = conjugate(W1).
--
-- The external Lean theorem W_1_mul_W_2_eq_two accepts C2=-C1 but does not use
-- that receipt in its proof.  This owner reserves the receipt for the stronger
-- same-object conjugation statement instead of discarding it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record NegativeOrbitConjugationReceipt : Set₁ where
  field
    Orbit : Set
    Scalar : Set

    negateOrbit : Orbit → Orbit
    orbitWeight : Orbit → Scalar
    conjugate : Scalar → Scalar

    negativeOrbit : Orbit
    positiveOrbit : Orbit

    negativeOrbitIsNegation :
      negativeOrbit ≡ negateOrbit positiveOrbit

    weightCommutesWithOrbitNegation :
      (orbit : Orbit) →
      orbitWeight (negateOrbit orbit) ≡ conjugate (orbitWeight orbit)

open NegativeOrbitConjugationReceipt public

negativeOrbitWeightIsConjugate :
  (receipt : NegativeOrbitConjugationReceipt) →
  orbitWeight receipt (negativeOrbit receipt)
  ≡ conjugate receipt (orbitWeight receipt (positiveOrbit receipt))
negativeOrbitWeightIsConjugate receipt with
  negativeOrbitIsNegation receipt
... | refl = weightCommutesWithOrbitNegation receipt (positiveOrbit receipt)

record SourceNegativeOrbitStatus : Set where
  constructor sourceNegativeOrbitStatus
  field
    negativeOrbitReceiptPresentInCyclotomicProductTheorem : Bool
    negativeOrbitReceiptUsedByProductEqualsTwoProof : Bool
    factorLevelComplexConjugationAvailable : Bool
    orbitProductConjugationMayReuseNegativeOrbitReceipt : Bool
    productEqualsTwoImpliesCancellationByItself : Bool

canonicalSourceNegativeOrbitStatus : SourceNegativeOrbitStatus
canonicalSourceNegativeOrbitStatus =
  sourceNegativeOrbitStatus true false true true false

record CancellationRefinement : Set where
  constructor cancellationRefinement
  field
    twoIndependentOrbitWeightsRemain : Bool
    negativeWeightCompilesAsConjugatePositiveWeight : Bool
    remainingLeafIsZeroRealTraceOfPositiveWeight : Bool
    explicitPlusMinusISqrtTwoRequired : Bool

canonicalCancellationRefinement : CancellationRefinement
canonicalCancellationRefinement =
  cancellationRefinement false true true false

negativeOrbitReceiptShouldNotBeDiscarded :
  SourceNegativeOrbitStatus.negativeOrbitReceiptUsedByProductEqualsTwoProof
    canonicalSourceNegativeOrbitStatus
  ≡ false
negativeOrbitReceiptShouldNotBeDiscarded = refl

remainingCancellationLeafIsOneOrbitTrace :
  CancellationRefinement.remainingLeafIsZeroRealTraceOfPositiveWeight
    canonicalCancellationRefinement
  ≡ true
remainingCancellationLeafIsOneOrbitTrace = refl
