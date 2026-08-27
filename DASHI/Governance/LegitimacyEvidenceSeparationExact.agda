module DASHI.Governance.LegitimacyEvidenceSeparationExact where

------------------------------------------------------------------------
-- LEGITIMACY EVIDENCE SEPARATION
--
-- SOURCE CALIBRATION
-- David Beetham, The Legitimation of Power, Macmillan, 1991.
-- DOI 10.1007/978-1-349-21599-7.
-- Second edition: Bloomsbury Academic, 2013, ISBN 9780230279728.
--
-- Beetham motivates distinct rule-conformity, justificatory-belief and consent
-- dimensions of legitimacy. The records/countermodels below are DASHI
-- constructions and do not decide legitimacy of any live institution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record LegitimacyEvidence (Power : Set) : Set₁ where
  constructor legitimacy-evidence
  field
    RuleConformity : Power → Set
    JustifiableBySharedBelief : Power → Set
    ExpressedConsent : Power → Set

open LegitimacyEvidence public

record AdmittedLegitimacy {Power : Set}
    (evidence : LegitimacyEvidence Power)
    (power : Power) : Set₁ where
  constructor admitted-legitimacy
  field
    ruleWitness : RuleConformity evidence power
    justificationWitness : JustifiableBySharedBelief evidence power
    consentWitness : ExpressedConsent evidence power

open AdmittedLegitimacy public

data DemoPower : Set where legalOnly justifiedOnly consentOnly allThree effectiveRepairNoLegitimacy : DemoPower

data RuleEvidence : DemoPower → Set where
  legalRule : RuleEvidence legalOnly
  allRule : RuleEvidence allThree

data BeliefEvidence : DemoPower → Set where
  justifiedBelief : BeliefEvidence justifiedOnly
  allBelief : BeliefEvidence allThree

data ConsentEvidence : DemoPower → Set where
  consentGiven : ConsentEvidence consentOnly
  allConsent : ConsentEvidence allThree

demoEvidence : LegitimacyEvidence DemoPower
demoEvidence = legitimacy-evidence RuleEvidence BeliefEvidence ConsentEvidence

canonicalAdmittedLegitimacy : AdmittedLegitimacy demoEvidence allThree
canonicalAdmittedLegitimacy = admitted-legitimacy allRule allBelief allConsent

legalOnlyIsNotAdmittedLegitimacy : AdmittedLegitimacy demoEvidence legalOnly → ⊥
legalOnlyIsNotAdmittedLegitimacy legitimacy =
  (λ ()) (justificationWitness legitimacy)

justifiedOnlyIsNotAdmittedLegitimacy : AdmittedLegitimacy demoEvidence justifiedOnly → ⊥
justifiedOnlyIsNotAdmittedLegitimacy legitimacy =
  (λ ()) (ruleWitness legitimacy)

consentOnlyIsNotAdmittedLegitimacy : AdmittedLegitimacy demoEvidence consentOnly → ⊥
consentOnlyIsNotAdmittedLegitimacy legitimacy =
  (λ ()) (ruleWitness legitimacy)

record LegitimacyBoundary : Set where
  constructor legitimacy-boundary
  field
    effectivePowerImpliesLegitimacy : Bool
    effectivePowerImpliesLegitimacyIsFalse : effectivePowerImpliesLegitimacy ≡ false
    legalityAloneImpliesLegitimacy : Bool
    legalityAloneImpliesLegitimacyIsFalse : legalityAloneImpliesLegitimacy ≡ false
    successfulRepairImpliesLegitimateAuthority : Bool
    successfulRepairImpliesLegitimateAuthorityIsFalse :
      successfulRepairImpliesLegitimateAuthority ≡ false
    formalAdmissionDecidesLivePoliticalLegitimacy : Bool
    formalAdmissionDecidesLivePoliticalLegitimacyIsFalse :
      formalAdmissionDecidesLivePoliticalLegitimacy ≡ false

canonicalLegitimacyBoundary : LegitimacyBoundary
canonicalLegitimacyBoundary =
  legitimacy-boundary false refl false refl false refl false refl
