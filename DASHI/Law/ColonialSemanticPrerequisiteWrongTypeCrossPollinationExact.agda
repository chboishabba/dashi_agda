module DASHI.Law.ColonialSemanticPrerequisiteWrongTypeCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Wrong
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Law.AustralianColonialWrongTypeAuthorityReclassificationExact as ColonialWrong
import DASHI.Law.AustralianColonialPrimarySourceAttributionExact as Primary
import DASHI.Law.MaboNeverCededSemanticEscalationCrossPollinationExact as Mabo
import DASHI.Law.SecurityThreatSemanticBroadeningTopologyExact as Security

------------------------------------------------------------------------
-- Conditional prerequisite theorem shape.
-- If a legal-administrative power is internally available only when antecedent
-- authority/law is represented as non-governing, then an authority-erasing or
-- authority-subordinating semantic projection is a prerequisite of that
-- internal justification.  This is a structural conditional, not a universal
-- psychological claim about every colonial official.
------------------------------------------------------------------------

data AdministrativePowerKind : Set where
  receiveEnglishLawAsSettledColony : AdministrativePowerKind
  allocateLandAsCrownAdministration : AdministrativePowerKind
  governProtectedPopulation : AdministrativePowerKind
  assimilateAdministrativePopulation : AdministrativePowerKind
  modernPublicOrderControl : AdministrativePowerKind

data AuthorityPremise : Set where
  antecedentAuthorityGoverning : AuthorityPremise
  antecedentAuthorityNonGoverning : AuthorityPremise
  antecedentAuthoritySubordinated : AuthorityPremise
  premiseOpen : AuthorityPremise

record InternalPowerJustification : Set where
  constructor internalPowerJustification
  field
    power : AdministrativePowerKind
    requiredPremise : AuthorityPremise
    classificationReceipt : String
    legalOperationalEffect : String
    sourceRole : Primary.PrimarySourceRole

open InternalPowerJustification public

cooperReceptionJustification : InternalPowerJustification
cooperReceptionJustification = internalPowerJustification
  receiveEnglishLawAsSettledColony
  antecedentAuthorityNonGoverning
  "Cooper v Stuart [1889] UKPC 16 paras 11-13: NSW placed in settled-colony class by reference to no settled inhabitants/law"
  "applicable English law received and land transactions governed within that colonial legal frame"
  Primary.privyCouncilHolding

record SemanticPrerequisiteReceipt (j : InternalPowerJustification) : Set where
  constructor semanticPrerequisiteReceipt
  field
    projection : ColonialWrong.AuthorityReclassification
    premiseRequiresReclassification : requiredPremise j ≡ antecedentAuthorityNonGoverning ⊎ requiredPremise j ≡ antecedentAuthoritySubordinated
    projectionSuppliesAdministrativeTarget : Set
    sourceAndSynthesisSeparated : Bool
    sourceAndSynthesisSeparatedIsTrue : sourceAndSynthesisSeparated ≡ true

open SemanticPrerequisiteReceipt public

cooperSemanticPrerequisite : SemanticPrerequisiteReceipt cooperReceptionJustification
cooperSemanticPrerequisite = semanticPrerequisiteReceipt
  ColonialWrong.cooperSettledColonyReclassification
  (inj₁ refl)
  ⊤
  true refl

------------------------------------------------------------------------
-- WrongType adapter.
-- Candidate wrong classification identifies the protected-interest question;
-- legal applicability, violation, liability and remedy remain downstream.
------------------------------------------------------------------------

wrongTypeCandidate : Ontology.WrongType
wrongTypeCandidate = ColonialWrong.colonialAuthorityReclassificationWrongType

wrongTypeInterpretation : Ontology.WrongTypeInterpretation
wrongTypeInterpretation = ColonialWrong.colonialWrongTypeInterpretation

wrongTypeNeedsApplicabilityProducer : Wrong.RequiredReceiptKind
wrongTypeNeedsApplicabilityProducer = Wrong.requiredReceipt Wrong.needsApplicability

wrongTypeNeedsViolationProducer : Wrong.RequiredReceiptKind
wrongTypeNeedsViolationProducer = Wrong.requiredReceipt Wrong.needsViolation

record WrongTypePrerequisiteBoundary : Set where
  constructor wrongTypePrerequisiteBoundary
  field
    structuralPrerequisiteEqualsRecognisedCauseOfAction : Bool
    structuralPrerequisiteEqualsRecognisedCauseOfActionIsFalse : structuralPrerequisiteEqualsRecognisedCauseOfAction ≡ false
    candidateWrongTypeAutomaticallyApplicable : Bool
    candidateWrongTypeAutomaticallyApplicableIsFalse : candidateWrongTypeAutomaticallyApplicable ≡ false
    applicabilityAutomaticallyViolation : Bool
    applicabilityAutomaticallyViolationIsFalse : applicabilityAutomaticallyViolation ≡ false
    historicalConstitutiveMechanismAutomaticallyModernPoliceMotive : Bool
    historicalConstitutiveMechanismAutomaticallyModernPoliceMotiveIsFalse : historicalConstitutiveMechanismAutomaticallyModernPoliceMotive ≡ false
    neverCededPositionErasedByCrownClassification : Bool
    neverCededPositionErasedByCrownClassificationIsFalse : neverCededPositionErasedByCrownClassification ≡ false

canonicalWrongTypePrerequisiteBoundary : WrongTypePrerequisiteBoundary
canonicalWrongTypePrerequisiteBoundary =
  wrongTypePrerequisiteBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Mabo / sovereignty pin.
------------------------------------------------------------------------

neverCededStillFirstNationsPosition : Primary.PrimarySourceRole
neverCededStillFirstNationsPosition = Primary.firstNationsPoliticalStatement

maboAuthorityVisibilityResidual : Mabo.ColonialSemanticProducer
maboAuthorityVisibilityResidual = Mabo.settledColonyLegalLogicProducer

------------------------------------------------------------------------
-- Modern security x-pollination.
-- A security classification is colonial in the relevant structural sense only
-- if the same-object lineage shows that authority/political meaning had to be
-- erased/subordinated in order to make the asserted police power or tactic
-- internally available. Similar broadening alone is insufficient.
------------------------------------------------------------------------

data ModernColonialMechanismClaim : Set where
  modernClassificationBroadensThreat : ModernColonialMechanismClaim
  modernClassificationErasesAuthority : ModernColonialMechanismClaim
  authorityErasureWasOperationalPrerequisite : ModernColonialMechanismClaim
  modernPoliceActionInstantiatesColonialSemanticMechanism : ModernColonialMechanismClaim

data ModernColonialMechanismProducer : Set where
  semanticBroadeningProducer : ModernColonialMechanismProducer
  beforeAfterAuthorityMeaningProducer : ModernColonialMechanismProducer
  powerPrerequisiteRuleProducer : ModernColonialMechanismProducer
  sameObjectProjectionPowerIncidentProducer : ModernColonialMechanismProducer

reverseModernColonialMechanism : ModernColonialMechanismClaim → ModernColonialMechanismProducer
reverseModernColonialMechanism modernClassificationBroadensThreat = semanticBroadeningProducer
reverseModernColonialMechanism modernClassificationErasesAuthority = beforeAfterAuthorityMeaningProducer
reverseModernColonialMechanism authorityErasureWasOperationalPrerequisite = powerPrerequisiteRuleProducer
reverseModernColonialMechanism modernPoliceActionInstantiatesColonialSemanticMechanism = sameObjectProjectionPowerIncidentProducer

securityBroadeningStillOnlyAuditTarget : Security.BroadeningProducer
securityBroadeningStillOnlyAuditTarget = Security.collectiveEvidenceAdequacyProducer

------------------------------------------------------------------------
-- Legal-element pin: WrongType id or label cannot manufacture element proof.
------------------------------------------------------------------------

wrongTypeIdStillDoesNotGenerateElements : Elements.WrongTypeIdAloneDeterminesAllElements → ⊥
wrongTypeIdStillDoesNotGenerateElements = Elements.wrongTypeIdDoesNotGenerateElements
