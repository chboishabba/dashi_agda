module DASHI.Moonshine.OggSSPSmallCharacteristicJointCorrectionCutsetExact where

------------------------------------------------------------------------
-- JOINT SMALL-CHARACTERISTIC CORRECTION CUTSET
--
-- EXTERNAL DUNCAN--SWISHER FACT
--
-- Remark 1.3 records that at p=2,3 BOTH of their presentations have the same
-- exceptional baseline:
--
--   modular-function three-term RHS:
--     p=2 -> 36, p=3 -> 18
--
--   supersingular/automorphism RHS:
--     p=2 -> 36, p=3 -> 18.
--
-- Both miss the Monster exponents by 10 and 2.
--
-- DASHI REQUIREMENT
--
-- A preferred exceptional analytic object should not merely patch one
-- presentation.  The same independently defined E_p should refine both the
-- Hauptmodul and supersingular descriptions:
--
--   modularBaseline(p)      + E_p = v_p(|M|)
--   supersingularBaseline(p)+ E_p = v_p(|M|).
--
-- This is a stronger acceptance test than matching the total gap alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact as Fourth
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two externally sourced baseline presentations.
------------------------------------------------------------------------

data SmallPrime : Set where
  pTwo pThree : SmallPrime

modularBaseline :
  SmallPrime ->
  Nat
modularBaseline pTwo =
  Baseline.baselineTotal Baseline.pTwo
modularBaseline pThree =
  Baseline.baselineTotal Baseline.pThree

supersingularBaseline :
  SmallPrime ->
  Nat
supersingularBaseline pTwo =
  Exponent.duncanSwisherExceptionalRHS Lane.p2
supersingularBaseline pThree =
  Exponent.duncanSwisherExceptionalRHS Lane.p3

actualMonsterExponent :
  SmallPrime ->
  Nat
actualMonsterExponent pTwo =
  Exponent.monsterOrderExponent Lane.p2
actualMonsterExponent pThree =
  Exponent.monsterOrderExponent Lane.p3

exceptionalPayment :
  SmallPrime ->
  Nat
exceptionalPayment pTwo =
  Fourth.exceptionalFourthTerm Baseline.pTwo
exceptionalPayment pThree =
  Fourth.exceptionalFourthTerm Baseline.pThree

p2ModularBaselineIsThirtySix :
  modularBaseline pTwo ≡ 36
p2ModularBaselineIsThirtySix = refl

p3ModularBaselineIsEighteen :
  modularBaseline pThree ≡ 18
p3ModularBaselineIsEighteen = refl

p2SupersingularBaselineIsThirtySix :
  supersingularBaseline pTwo ≡ 36
p2SupersingularBaselineIsThirtySix = refl

p3SupersingularBaselineIsEighteen :
  supersingularBaseline pThree ≡ 18
p3SupersingularBaselineIsEighteen = refl

------------------------------------------------------------------------
-- 2. Exact equality of the two baselines at the exceptional primes.
------------------------------------------------------------------------

p2BaselinesAgree :
  modularBaseline pTwo
  ≡ supersingularBaseline pTwo
p2BaselinesAgree = refl

p3BaselinesAgree :
  modularBaseline pThree
  ≡ supersingularBaseline pThree
p3BaselinesAgree = refl

------------------------------------------------------------------------
-- 3. Same finite exceptional payment repairs both numerically.
------------------------------------------------------------------------

p2ModularPlusExceptionalPaysMonster :
  modularBaseline pTwo
  + exceptionalPayment pTwo
  ≡ actualMonsterExponent pTwo
p2ModularPlusExceptionalPaysMonster = refl

p3ModularPlusExceptionalPaysMonster :
  modularBaseline pThree
  + exceptionalPayment pThree
  ≡ actualMonsterExponent pThree
p3ModularPlusExceptionalPaysMonster = refl

p2SupersingularPlusExceptionalPaysMonster :
  supersingularBaseline pTwo
  + exceptionalPayment pTwo
  ≡ actualMonsterExponent pTwo
p2SupersingularPlusExceptionalPaysMonster = refl

p3SupersingularPlusExceptionalPaysMonster :
  supersingularBaseline pThree
  + exceptionalPayment pThree
  ≡ actualMonsterExponent pThree
p3SupersingularPlusExceptionalPaysMonster = refl

------------------------------------------------------------------------
-- 4. Analytic/geometric joint authority.
--
-- An admissible theorem must derive the SAME exceptional object on both sides,
-- rather than fitting two unrelated corrections of equal numerical size.
------------------------------------------------------------------------

record JointSmallPrimeExceptionalAuthority : Set₁ where
  field
    exceptionalAnalyticTerm :
      Fourth.SmallPrimeExceptionalAnalyticTerm

    p2RefinesPublishedHauptmodulSide : Bool
    p2RefinesPublishedHauptmodulSideIsTrue :
      p2RefinesPublishedHauptmodulSide ≡ true

    p3RefinesPublishedHauptmodulSide : Bool
    p3RefinesPublishedHauptmodulSideIsTrue :
      p3RefinesPublishedHauptmodulSide ≡ true

    p2RefinesPublishedSupersingularSide : Bool
    p2RefinesPublishedSupersingularSideIsTrue :
      p2RefinesPublishedSupersingularSide ≡ true

    p3RefinesPublishedSupersingularSide : Bool
    p3RefinesPublishedSupersingularSideIsTrue :
      p3RefinesPublishedSupersingularSide ≡ true

    sameExceptionalObjectUsedOnBothDescriptions : Bool
    sameExceptionalObjectUsedOnBothDescriptionsIsTrue :
      sameExceptionalObjectUsedOnBothDescriptions ≡ true

    compatibilityProvedWithoutUsingMonsterTargetToDefineObject : Bool
    compatibilityProvedWithoutUsingMonsterTargetToDefineObjectIsTrue :
      compatibilityProvedWithoutUsingMonsterTargetToDefineObject ≡ true

open JointSmallPrimeExceptionalAuthority public

------------------------------------------------------------------------
-- 5. Joint authority licenses the four-term extension immediately.
------------------------------------------------------------------------

asFourTermExtension :
  JointSmallPrimeExceptionalAuthority ->
  Fourth.AnalyticallyLicensedFourTermExtension
asFourTermExtension authority =
  Fourth.licenseFourTermExtension
    (exceptionalAnalyticTerm authority)

------------------------------------------------------------------------
-- 6. Wrong-type guards.
------------------------------------------------------------------------

data ModularCorrectionAloneCreatesJointAuthority : Set where
data SupersingularCorrectionAloneCreatesJointAuthority : Set where
data EqualBaselineNumbersCreateJointAuthority : Set where
data SameGapSizeCreatesSameExceptionalObject : Set where
data DuncanSwisherProvedJointSmallPrimeCorrection : Set where

modularCorrectionAloneDoesNotCreateJointAuthority :
  ModularCorrectionAloneCreatesJointAuthority -> ⊥
modularCorrectionAloneDoesNotCreateJointAuthority ()

supersingularCorrectionAloneDoesNotCreateJointAuthority :
  SupersingularCorrectionAloneCreatesJointAuthority -> ⊥
supersingularCorrectionAloneDoesNotCreateJointAuthority ()

equalBaselineNumbersDoNotCreateJointAuthority :
  EqualBaselineNumbersCreateJointAuthority -> ⊥
equalBaselineNumbersDoNotCreateJointAuthority ()

sameGapSizeDoesNotCreateSameExceptionalObject :
  SameGapSizeCreatesSameExceptionalObject -> ⊥
sameGapSizeDoesNotCreateSameExceptionalObject ()

duncanSwisherNotCreditedWithJointCorrection :
  DuncanSwisherProvedJointSmallPrimeCorrection -> ⊥
duncanSwisherNotCreditedWithJointCorrection ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record JointCorrectionCutsetBoundary : Set where
  constructor joint-correction-cutset-boundary
  field
    p2TwoPublishedBaselinesAgreeAtThirtySix : Bool
    p3TwoPublishedBaselinesAgreeAtEighteen : Bool
    sameFiniteP2PaymentRepairsBothNumerically : Bool
    sameFiniteP3PaymentRepairsBothNumerically : Bool
    jointExceptionalAuthoritySpecified : Bool
    sameExceptionalObjectRequiredOnBothSides : Bool
    noTargetCircularityRequired : Bool
    duncanSwisherCreditedWithJointCorrection : Bool
    jointAuthorityCurrentlyInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalJointCorrectionCutsetBoundary :
  JointCorrectionCutsetBoundary
canonicalJointCorrectionCutsetBoundary =
  joint-correction-cutset-boundary
    true true true true true true true false false true
