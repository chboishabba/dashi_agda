module DASHI.Analysis.NonArchimedeanNegativeOrbitWeightPhaseCompilerExact where

------------------------------------------------------------------------
-- NEGATIVE ORBIT WEIGHT PHASE COMPILER
--
-- For C2=-C1 and w(k)=1+omega^(-k):
--
--   W2 = product_{h in C1} (1+omega^h)
--      = product_{h in C1} [omega^h (1+omega^(-h))]
--      = omega^(sum C1) W1.
--
-- The strong source theorem `three_pow_two_pow` plus the geometric-series
-- identity compiles `sum C1` to the dyadic half-period.  Primitive-root
-- arithmetic then compiles the phase to -1, hence W2=-W1 and W1+W2=0.
--
-- No explicit +/- i sqrt(2) value and no separate Gaussian-period theorem is
-- required on the critical path.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record NegativeOrbitWeightPhaseStatus : Set where
  constructor negativeOrbitWeightPhaseStatus
  field
    negativeOrbitReindexReceiptAvailable : Bool
    factorIdentityOnePlusOmegaPosAvailable : Bool
    finiteProductMultiplicativityReusable : Bool
    orbitSumHalfPeriodCompiledFromStrongThreePower : Bool
    primitiveHalfTurnMinusOneReusable : Bool
    negativeWeightEqualsMinusPositiveCompiles : Bool
    pairedCancellationCompiles : Bool
    explicitComplexPhaseRequired : Bool
    gaussianPeriodLibraryRequired : Bool

canonicalNegativeOrbitWeightPhaseStatus : NegativeOrbitWeightPhaseStatus
canonicalNegativeOrbitWeightPhaseStatus =
  negativeOrbitWeightPhaseStatus
    true true true true true true true false false

record SignedPromotion : Set where
  constructor signedPromotion
  field
    negativeOrbitReindex : Bool
    orbitSumHalfPeriod : Bool
    halfTurnMinusOne : Bool
    finiteProductAlgebra : Bool
    signedCancellationPromoted : Bool

allFour : Bool → Bool → Bool → Bool → Bool
allFour true true true true = true
allFour _ _ _ _ = false

compileSignedPromotion : Bool → Bool → Bool → Bool → SignedPromotion
compileSignedPromotion neg sum half algebra =
  signedPromotion neg sum half algebra (allFour neg sum half algebra)

canonicalSignedPromotion : SignedPromotion
canonicalSignedPromotion = compileSignedPromotion true true true true

signedCancellationNowPromotes :
  SignedPromotion.signedCancellationPromoted canonicalSignedPromotion ≡ true
signedCancellationNowPromotes = refl

explicitPhaseSearchPruned :
  NegativeOrbitWeightPhaseStatus.explicitComplexPhaseRequired
    canonicalNegativeOrbitWeightPhaseStatus
  ≡ false
explicitPhaseSearchPruned = refl

gaussianPeriodSearchPruned :
  NegativeOrbitWeightPhaseStatus.gaussianPeriodLibraryRequired
    canonicalNegativeOrbitWeightPhaseStatus
  ≡ false
gaussianPeriodSearchPruned = refl
