module DASHI.Wikimedia.IbrahimMonster6BPositiveDegreeNormalizationAcquisitionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Wikimedia.IbrahimMonster6BPositiveDegreeNormalizationAcquisitionExact as A

receipt : A.SixBPositiveDegreeNormalizationAcquisition
receipt = A.currentSixBPositiveDegreeNormalizationAcquisition

variantCountRegression : A.variantCount receipt ≡ 3
variantCountRegression = refl

qOneRegression : A.qOne receipt ≡ 78
qOneRegression = refl

qTwoRegression : A.qTwo receipt ≡ 364
qTwoRegression = refl

qThreeRegression : A.qThree receipt ≡ 1365
qThreeRegression = refl

qFourRegression : A.qFour receipt ≡ 4380
qFourRegression = refl

qFiveRegression : A.qFive receipt ≡ 12520
qFiveRegression = refl

qSixRegression : A.qSix receipt ≡ 32772
qSixRegression = refl

positiveDegreeAgreementRegression :
  A.positiveDegreeAgreementThroughQSixPaid receipt ≡ true
positiveDegreeAgreementRegression = refl

normalizationConstantsDifferRegression :
  A.qZeroNormalizationDependent receipt ≡ true
normalizationConstantsDifferRegression = refl

c6BridgeSignalRegression :
  A.qSixMatchesC6WeightTwoM1M5 receipt ≡ true
c6BridgeSignalRegression = refl

sameObjectFirewallRegression :
  A.normalizationAgreementCreatesSameObject receipt ≡ false
sameObjectFirewallRegression = refl

actionFirewallRegression :
  A.oeisPositiveDegreeAgreementCreatesLiteralAction receipt ≡ false
actionFirewallRegression = refl
