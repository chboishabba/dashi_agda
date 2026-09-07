module DASHI.Law.SecurityClassificationProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Security-classification provenance.
-- A political assembly does not intrinsically arrive as 'risk', 'threat',
-- 'hostile crowd' or 'public disorder'.  Those are classifications produced by
-- actors, sources and procedures, and may unlock distinct coercive pathways.
------------------------------------------------------------------------

data ClassificationLabel : Set where
  ordinaryPoliticalAssembly : ClassificationLabel
  publicOrderRisk : ClassificationLabel
  aggressiveCrowd : ClassificationLabel
  volatileCrowd : ClassificationLabel
  hostileCrowd : ClassificationLabel
  publicDisorder : ClassificationLabel
  protectedPersonSecurityRisk : ClassificationLabel
  counterTerrorSecurityRisk : ClassificationLabel
  prohibitedMarchRisk : ClassificationLabel
  intelligencePriority : ClassificationLabel
  classificationUnresolved : ClassificationLabel

data ClassifierRole : Set where
  policeCommand : ClassifierRole
  intelligenceUnit : ClassifierRole
  ministerOrExecutive : ClassifierRole
  protectedPersonSecurityTeam : ClassifierRole
  privateSecurityLiaison : ClassifierRole
  eventOrganiser : ClassifierRole
  operationalOfficer : ClassifierRole
  mediaOrPublicNarrative : ClassifierRole
  classifierUnknown : ClassifierRole

data ClassificationEvidenceKind : Set where
  writtenRiskAssessment : ClassificationEvidenceKind
  intelligenceProduct : ClassificationEvidenceKind
  operationalOrder : ClassificationEvidenceKind
  briefingNote : ClassificationEvidenceKind
  oralCommand : ClassificationEvidenceKind
  liaisonCommunication : ClassificationEvidenceKind
  contemporaneousObservation : ClassificationEvidenceKind
  postHocCharacterisation : ClassificationEvidenceKind
  evidenceUnknown : ClassificationEvidenceKind

record SecurityClassificationReceipt : Set where
  constructor securityClassificationReceipt
  field
    eventReference : String
    label : ClassificationLabel
    classifier : ClassifierRole
    evidenceKind : ClassificationEvidenceKind
    issuedBeforeOperationalAction : Bool
    classificationContentReference : String
    legalConsequenceReference : String
    sourceReference : String

open SecurityClassificationReceipt public

------------------------------------------------------------------------
-- Coercive consequences must be represented separately from labels.
------------------------------------------------------------------------

data CoerciveUnlock : Set where
  increasedPoliceDeployment : CoerciveUnlock
  containmentOrCordon : CoerciveUnlock
  mountedUnitDeployment : CoerciveUnlock
  pepperSprayAvailability : CoerciveUnlock
  moveOnOrDispersalDirection : CoerciveUnlock
  searchOrArrestAttention : CoerciveUnlock
  protectedPersonEscort : CoerciveUnlock
  intelligenceCollection : CoerciveUnlock
  specialistUnitDeployment : CoerciveUnlock
  noAdditionalPower : CoerciveUnlock

record ClassificationToPowerEdge : Set where
  constructor classificationToPowerEdge
  field
    classificationReceipt : SecurityClassificationReceipt
    proposedUnlock : CoerciveUnlock
    legalAuthoritySeparate : Bool
    legalAuthoritySeparateIsTrue : legalAuthoritySeparate ≡ true
    causalOperationalLinkClosed : Bool
    causalReference : String

open ClassificationToPowerEdge public

------------------------------------------------------------------------
-- BIDI claim routing.
------------------------------------------------------------------------

data SecurityClassificationClaim : Set where
  assemblyWasClassifiedAsRiskBeforeAction : SecurityClassificationClaim
  classificationWasSuppliedByNamedActor : SecurityClassificationClaim
  classificationUnlockedOperationalTactic : SecurityClassificationClaim
  classificationHadLawfulAuthorityEffect : SecurityClassificationClaim
  classificationWasIdeologicallyMotivated : SecurityClassificationClaim
  classificationWasForeignSupplied : SecurityClassificationClaim

data SecurityClassificationProducer : Set where
  preActionClassificationDocumentProducer : SecurityClassificationProducer
  classifierIdentityProducer : SecurityClassificationProducer
  commandAndDeploymentLinkProducer : SecurityClassificationProducer
  legalAuthorityProducer : SecurityClassificationProducer
  motiveProducer : SecurityClassificationProducer
  foreignLiaisonProducer : SecurityClassificationProducer

reverseSecurityClassification : SecurityClassificationClaim → SecurityClassificationProducer
reverseSecurityClassification assemblyWasClassifiedAsRiskBeforeAction = preActionClassificationDocumentProducer
reverseSecurityClassification classificationWasSuppliedByNamedActor = classifierIdentityProducer
reverseSecurityClassification classificationUnlockedOperationalTactic = commandAndDeploymentLinkProducer
reverseSecurityClassification classificationHadLawfulAuthorityEffect = legalAuthorityProducer
reverseSecurityClassification classificationWasIdeologicallyMotivated = motiveProducer
reverseSecurityClassification classificationWasForeignSupplied = foreignLiaisonProducer

record ClassificationCutset : Set where
  constructor classificationCutset
  field
    preActionDocumentClosed : Bool
    classifierClosed : Bool
    commandDeploymentLinkClosed : Bool
    legalAuthorityClosed : Bool
    motiveClosed : Bool
    foreignLiaisonClosed : Bool
    cutsetReference : String

open ClassificationCutset public

data ClassificationResidual : Set where
  preActionDocumentResidual : ClassificationResidual
  classifierResidual : ClassificationResidual
  commandDeploymentResidual : ClassificationResidual
  legalAuthorityResidual : ClassificationResidual
  motiveResidual : ClassificationResidual
  foreignLiaisonResidual : ClassificationResidual
  classificationClosed : ClassificationResidual

firstClassificationResidual : SecurityClassificationClaim → ClassificationCutset → ClassificationResidual
firstClassificationResidual assemblyWasClassifiedAsRiskBeforeAction c with preActionDocumentClosed c
... | false = preActionDocumentResidual
... | true = classificationClosed
firstClassificationResidual classificationWasSuppliedByNamedActor c with classifierClosed c
... | false = classifierResidual
... | true = classificationClosed
firstClassificationResidual classificationUnlockedOperationalTactic c with preActionDocumentClosed c
... | false = preActionDocumentResidual
... | true with commandDeploymentLinkClosed c
...   | false = commandDeploymentResidual
...   | true = classificationClosed
firstClassificationResidual classificationHadLawfulAuthorityEffect c with commandDeploymentLinkClosed c
... | false = commandDeploymentResidual
... | true with legalAuthorityClosed c
...   | false = legalAuthorityResidual
...   | true = classificationClosed
firstClassificationResidual classificationWasIdeologicallyMotivated c with motiveClosed c
... | false = motiveResidual
... | true = classificationClosed
firstClassificationResidual classificationWasForeignSupplied c with foreignLiaisonClosed c
... | false = foreignLiaisonResidual
... | true = classificationClosed

canonicalPublicNarrativeOnlyCutset : ClassificationCutset
canonicalPublicNarrativeOnlyCutset = classificationCutset false false false false false false
  "public/post-hoc crowd characterisations do not close the pre-action classification producer"

preActionClassificationCannotBeBackfilledByPostHocNarrative :
  firstClassificationResidual assemblyWasClassifiedAsRiskBeforeAction canonicalPublicNarrativeOnlyCutset
  ≡ preActionDocumentResidual
preActionClassificationCannotBeBackfilledByPostHocNarrative = refl

------------------------------------------------------------------------
-- Herzog-shaped source fixtures.  These do not claim access to the underlying
-- risk assessment; they preserve public police language as post-hoc evidence.
------------------------------------------------------------------------

policeAggressiveCrowdPostHoc : SecurityClassificationReceipt
policeAggressiveCrowdPostHoc = securityClassificationReceipt
  "Sydney Town Hall anti-Herzog protest, 9 February 2026"
  aggressiveCrowd policeCommand postHocCharacterisation false
  "Commissioner Mal Lanyon later characterised crowd as significant, aggressive and volatile"
  "does not by itself identify which pre-event powers/tactics were unlocked"
  "ABC 7.30, Police and protesters clash at Sydney rally, 10 February 2026"

protectedPersonSecurityContext : SecurityClassificationReceipt
protectedPersonSecurityContext = securityClassificationReceipt
  "Isaac Herzog visit to Sydney, February 2026"
  protectedPersonSecurityRisk protectedPersonSecurityTeam briefingNote false
  "public reporting confirms specialist officers/security guarded the visiting president; underlying briefing not yet acquired"
  "security deployment context only; classification document remains open"
  "ABC live coverage, Sydney Town Hall protest, 9 February 2026"

record ClassificationBoundary : Set where
  constructor classificationBoundary
  field
    postHocAggressiveLabelProvesPreActionClassification : Bool
    postHocAggressiveLabelProvesPreActionClassificationIsFalse : postHocAggressiveLabelProvesPreActionClassification ≡ false
    securityLabelCreatesLegalPowerByItself : Bool
    securityLabelCreatesLegalPowerByItselfIsFalse : securityLabelCreatesLegalPowerByItself ≡ false
    protectedPersonStatusMakesEveryCrowdTacticLawful : Bool
    protectedPersonStatusMakesEveryCrowdTacticLawfulIsFalse : protectedPersonStatusMakesEveryCrowdTacticLawful ≡ false
    ideologicalContextProvesPoliceMotive : Bool
    ideologicalContextProvesPoliceMotiveIsFalse : ideologicalContextProvesPoliceMotive ≡ false

canonicalClassificationBoundary : ClassificationBoundary
canonicalClassificationBoundary = classificationBoundary false refl false refl false refl false refl
