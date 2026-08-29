module DASHI.Governance.CaceresAuthorityWithoutEnforcementExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- BERTA CACERES / COPINH: RECOGNITION, PROTECTION, ENFORCEMENT
--
-- Sources are deliberately institutional/judicial-process records:
--   * IACHR Resolution 88/2021 (continuing precautionary-measures follow-up);
--   * 2019 international trial-observer report reproducing the Honduran
--     sentencing finding concerning DESA executives' knowledge/consent;
--   * 2021 FIDH record of COPINH/Rio Blanco victim recognition in the related
--     Gualcarque corruption proceeding.
--
-- This module does NOT claim later judgments created Lenca/COPINH authority.
-- It formalises the narrower separation: recognized/protected/represented
-- standing does not imply effective power to prevent harm or enforce remedy.
------------------------------------------------------------------------

data Standing : Set where
  communityStanding victimStanding protectedBeneficiary : Standing

data EnforcementState : Set where
  preventionEffective preventionFailed remedyIncomplete : EnforcementState

data HasStanding : Standing → Set where
  communityHasStanding : HasStanding communityStanding
  victimRecognized : HasStanding victimStanding
  precautionaryBeneficiary : HasStanding protectedBeneficiary

data EffectiveEnforcement : Standing → Set where

recognizedStandingWithoutEnforcement : HasStanding victimStanding
recognizedStandingWithoutEnforcement = victimRecognized

victimStandingDoesNotConstructEnforcement : EffectiveEnforcement victimStanding → ⊥
victimStandingDoesNotConstructEnforcement ()

protectedStatusDoesNotConstructEnforcement : EffectiveEnforcement protectedBeneficiary → ⊥
protectedStatusDoesNotConstructEnforcement ()

iachrSource : Sources.SourceReference
iachrSource = Sources.iachr2021

observerMissionSource : Sources.SourceReference
observerMissionSource = Sources.caceresObserverMission2019

victimRecognitionSource : Sources.SourceReference
victimRecognitionSource = Sources.copinhVictim2021

record CaceresAuthorityEnforcementBoundary : Set where
  constructor caceresAuthorityEnforcementBoundary
  field
    legalVictimRecognitionImpliesEffectivePrevention : Bool
    legalVictimRecognitionImpliesEffectivePreventionIsFalse : legalVictimRecognitionImpliesEffectivePrevention ≡ false
    precautionaryMeasureImpliesProtectionAlreadyEffective : Bool
    precautionaryMeasureImpliesProtectionAlreadyEffectiveIsFalse : precautionaryMeasureImpliesProtectionAlreadyEffective ≡ false
    convictionClosesAllResponsibilityQuestions : Bool
    convictionClosesAllResponsibilityQuestionsIsFalse : convictionClosesAllResponsibilityQuestions ≡ false
    laterJudgmentCreatesIndigenousAuthorityRetroactively : Bool
    laterJudgmentCreatesIndigenousAuthorityRetroactivelyIsFalse : laterJudgmentCreatesIndigenousAuthorityRetroactively ≡ false
    documentedStandingEqualsEnforcementPower : Bool
    documentedStandingEqualsEnforcementPowerIsFalse : documentedStandingEqualsEnforcementPower ≡ false

canonicalCaceresAuthorityEnforcementBoundary : CaceresAuthorityEnforcementBoundary
canonicalCaceresAuthorityEnforcementBoundary =
  caceresAuthorityEnforcementBoundary false refl false refl false refl false refl false refl
