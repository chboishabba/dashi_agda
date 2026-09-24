{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.DrellYanRatioCancellationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_*_)
open import Relation.Binary.PropositionalEquality using (_≢_)

------------------------------------------------------------------------
-- A good ratio does not imply either absolute component is correct.
--
-- Cross multiplication avoids division entirely.  The witness below has the
-- same ratio 2/1 = 200/100 while both predicted absolute components differ by
-- a factor 100.  This is the exact firewall needed when interpreting the good
-- CMS t43 ratio alongside the failed absolute Z-window W4 projection.
------------------------------------------------------------------------

ratioEquivalent :
  Nat → Nat → Nat → Nat → Set
ratioEquivalent numerator denominator
    predictedNumerator predictedDenominator =
  numerator * predictedDenominator
  ≡ predictedNumerator * denominator

ratioCancellationWitness :
  ratioEquivalent 2 1 200 100
ratioCancellationWitness = refl

ratioCancellationNumeratorIsAbsolutelyWrong :
  2 ≢ 200
ratioCancellationNumeratorIsAbsolutelyWrong ()

ratioCancellationDenominatorIsAbsolutelyWrong :
  1 ≢ 100
ratioCancellationDenominatorIsAbsolutelyWrong ()

ratioAgreementImpliesAbsoluteAgreement : Bool
ratioAgreementImpliesAbsoluteAgreement = false

ratioAgreementImpliesAbsoluteAgreementIsFalse :
  ratioAgreementImpliesAbsoluteAgreement ≡ false
ratioAgreementImpliesAbsoluteAgreementIsFalse = refl

cmsRatioContactProvesAbsoluteZWindowAccuracy : Bool
cmsRatioContactProvesAbsoluteZWindowAccuracy = false

cmsRatioContactProvesAbsoluteZWindowAccuracyIsFalse :
  cmsRatioContactProvesAbsoluteZWindowAccuracy ≡ false
cmsRatioContactProvesAbsoluteZWindowAccuracyIsFalse = refl

cmsRatioContactConstrainsSharedRelativeStructure : Bool
cmsRatioContactConstrainsSharedRelativeStructure = true

cmsRatioContactConstrainsSharedRelativeStructureIsTrue :
  cmsRatioContactConstrainsSharedRelativeStructure ≡ true
cmsRatioContactConstrainsSharedRelativeStructureIsTrue = refl
