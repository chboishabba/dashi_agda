module DASHI.Law.HerzogColonialWrongTypeCrossSystemBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Wrong
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Law.HerzogUniversalLegalEvidenceBridgeExact as Herzog
import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage
import DASHI.Law.SecurityThreatSemanticBroadeningTopologyExact as Broadening
import DASHI.Law.AustralianColonialWrongTypeAuthorityReclassificationExact as ColonialWrong
import DASHI.Law.AustralianColonialPrimarySourceAttributionExact as Primary
import DASHI.Law.ColonialSemanticPrerequisiteWrongTypeCrossPollinationExact as ColonialPrereq

------------------------------------------------------------------------
-- HERZOG x COLONIAL WRONGTYPE CROSS-SYSTEM BRIDGE
--
-- This module adds no new historical allegation. It is a DASHI formal bridge
-- between two already source-bounded fibres:
--
--   * Herzog/security-classification evidence under an AU/NSW audit system;
--   * the analytical ColonialAuthorityReclassificationWrongType under
--     DASHI.ANALYTICAL.COLONIAL-AUTHORITY.
--
-- Source ownership remains with the imported modules. In particular:
--   Cooper v Stuart [1889] UKPC 16, paras 11-13;
--   Mabo v Queensland (No 2) [1992] HCA 23;
--   Uluru Statement from the Heart (2017);
--   Love v Commonwealth; Thoms v Commonwealth [2020] HCA 3.
--
-- The cross-system comparison itself is DASHI synthesis. Structural analogy is
-- not historical identity, doctrinal identity, motive evidence, or liability.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Target propositions are deliberately indexed to the COLONIAL ANALYTICAL
-- system. Herzog facts cannot inhabit them merely by sharing prose/content.
------------------------------------------------------------------------

modernAuthorityErasureObserved : Algebra.LegalProposition
modernAuthorityErasureObserved = Algebra.legal-proposition
  (Ontology.stableId "analysis:Herzog:colonial-wrongtype:authority-erasure-observed")
  Algebra.relationalFeature
  Herzog.herzogEvent Herzog.herzogEvent
  ColonialWrong.colonialAnalyticalSystemId
  "source-bounded before/after comparison establishes that Country, community authority or political meaning was erased or subordinated by the modern classification"

authorityErasureOperationalPrerequisite : Algebra.LegalProposition
authorityErasureOperationalPrerequisite = Algebra.legal-proposition
  (Ontology.stableId "analysis:Herzog:colonial-wrongtype:authority-erasure-prerequisite")
  Algebra.institutionalConstraint
  Herzog.herzogEvent Herzog.herzogEvent
  ColonialWrong.colonialAnalyticalSystemId
  "a source-backed power/prerequisite rule establishes that the authority-erasing or subordinating classification was required for the asserted public-order power or tactic to be internally available"

sameObjectProjectionPowerIncidentClosed : Algebra.LegalProposition
sameObjectProjectionPowerIncidentClosed = Algebra.legal-proposition
  (Ontology.stableId "analysis:Herzog:colonial-wrongtype:same-object-projection-power-incident")
  Algebra.relationalFeature
  Herzog.herzogEvent Herzog.herzogEvent
  ColonialWrong.colonialAnalyticalSystemId
  "the same source-bounded classification projection is welded through power/order lineage into the specific incident relied upon by the analytical comparison"

modernColonialMechanismEstablished : Algebra.LegalProposition
modernColonialMechanismEstablished = Algebra.legal-proposition
  (Ontology.stableId "analysis:Herzog:colonial-wrongtype:mechanism-established")
  Algebra.wrongElementPredicate
  Herzog.herzogEvent Herzog.herzogEvent
  ColonialWrong.colonialAnalyticalSystemId
  "the modern event satisfies the declared analytical authority-reclassification mechanism coordinates; this is not a recognised cause of action"

------------------------------------------------------------------------
-- Cross-system translation is an explicit receipt.
------------------------------------------------------------------------

data TranslationStatus : Set where
  translationOpen : TranslationStatus
  translationClosed : TranslationStatus
  translationConflict : TranslationStatus

data TranslationProducer : Set where
  sourceClassificationLineageProducer : TranslationProducer
  beforeAfterAuthorityMeaningProducer : TranslationProducer
  operationalPowerPrerequisiteProducer : TranslationProducer
  sameObjectIncidentWeldProducer : TranslationProducer
  analyticalElementProducer : TranslationProducer
  applicabilityAndJurisdictionProducer : TranslationProducer
  liabilityAndRemedyProducer : TranslationProducer


record CrossSystemInterpretiveTranslation : Set where
  constructor cross-system-interpretive-translation
  field
    sourceProposition : Algebra.LegalProposition
    targetProposition : Algebra.LegalProposition
    sourceSystem : Ontology.StableId
    targetSystem : Ontology.StableId
    sameLegalSystemClaimed : Bool
    sameLegalSystemClaimedIsFalse : sameLegalSystemClaimed ≡ false
    requiredProducer : TranslationProducer
    sourceAttributionPreserved : Bool
    sourceAttributionPreservedIsTrue : sourceAttributionPreserved ≡ true
    translationStatus : TranslationStatus
    translationReference : String
    translationCreatesLegalAuthority : Bool
    translationCreatesLegalAuthorityIsFalse : translationCreatesLegalAuthority ≡ false

open CrossSystemInterpretiveTranslation public

currentHerzogAuthorityErasureTranslation : CrossSystemInterpretiveTranslation
currentHerzogAuthorityErasureTranslation = cross-system-interpretive-translation
  Herzog.preActionClassificationContentEstablished
  modernAuthorityErasureObserved
  Herzog.herzogSystem
  ColonialWrong.colonialAnalyticalSystemId
  false refl
  beforeAfterAuthorityMeaningProducer
  true refl
  translationOpen
  "Current Herzog source surface does not yet close the pre-action before/after authority-meaning comparison required by the colonial analytical fibre."
  false refl

currentHerzogPrerequisiteTranslation : CrossSystemInterpretiveTranslation
currentHerzogPrerequisiteTranslation = cross-system-interpretive-translation
  Herzog.classificationProducedOperationalOrder
  authorityErasureOperationalPrerequisite
  Herzog.herzogSystem
  ColonialWrong.colonialAnalyticalSystemId
  false refl
  operationalPowerPrerequisiteProducer
  true refl
  translationOpen
  "A classification-to-order lineage does not itself prove that authority erasure/subordination was a necessary legal or operational prerequisite of the asserted power."
  false refl

currentHerzogIncidentTranslation : CrossSystemInterpretiveTranslation
currentHerzogIncidentTranslation = cross-system-interpretive-translation
  Herzog.operationalOrderProducedFieldTactic
  sameObjectProjectionPowerIncidentClosed
  Herzog.herzogSystem
  ColonialWrong.colonialAnalyticalSystemId
  false refl
  sameObjectIncidentWeldProducer
  true refl
  translationOpen
  "The current Herzog incident lineage remains documentary-open; same operation is not the same-object projection/power/incident weld."
  false refl

------------------------------------------------------------------------
-- Reverse routing. The stronger claim determines the producer that must close.
------------------------------------------------------------------------

data HerzogColonialClaim : Set where
  classificationBroadeningObserved : HerzogColonialClaim
  authorityErasureObserved : HerzogColonialClaim
  authorityErasureWasOperationalPrerequisite : HerzogColonialClaim
  sameObjectModernColonialMechanism : HerzogColonialClaim
  analyticalWrongTypeApplicable : HerzogColonialClaim
  analyticalWrongTypeViolated : HerzogColonialClaim
  analyticalWrongTypeCreatesLiability : HerzogColonialClaim


reverseHerzogColonial : HerzogColonialClaim → TranslationProducer
reverseHerzogColonial classificationBroadeningObserved = sourceClassificationLineageProducer
reverseHerzogColonial authorityErasureObserved = beforeAfterAuthorityMeaningProducer
reverseHerzogColonial authorityErasureWasOperationalPrerequisite = operationalPowerPrerequisiteProducer
reverseHerzogColonial sameObjectModernColonialMechanism = sameObjectIncidentWeldProducer
reverseHerzogColonial analyticalWrongTypeApplicable = applicabilityAndJurisdictionProducer
reverseHerzogColonial analyticalWrongTypeViolated = analyticalElementProducer
reverseHerzogColonial analyticalWrongTypeCreatesLiability = liabilityAndRemedyProducer

------------------------------------------------------------------------
-- Generic legal residual routing is retained at the translation boundary.
------------------------------------------------------------------------

authorityMeaningResidual : Residual.LegalResidualKind
authorityMeaningResidual = Residual.missingRelationalFeature

powerPrerequisiteResidual : Residual.LegalResidualKind
powerPrerequisiteResidual = Residual.missingInstitutionalConstraint

incidentWeldResidual : Residual.LegalResidualKind
incidentWeldResidual = Residual.missingFactualFeature

authorityMeaningRequestsEvidence :
  Residual.preferredRoute authorityMeaningResidual ≡ Residual.obtainFactualEvidence
authorityMeaningRequestsEvidence = refl

powerPrerequisiteRequestsReasons :
  Residual.preferredRoute powerPrerequisiteResidual ≡ Residual.inspectJudicialReasons
powerPrerequisiteRequestsReasons = refl

------------------------------------------------------------------------
-- Existing source-role pins remain explicit.
------------------------------------------------------------------------

cooperSourceRole : Primary.PrimarySourceRole
cooperSourceRole = Primary.privyCouncilHolding

neverCededSourceRole : Primary.PrimarySourceRole
neverCededSourceRole = Primary.firstNationsPoliticalStatement

modernSecurityBroadeningProducer : Broadening.BroadeningProducer
modernSecurityBroadeningProducer = Broadening.collectiveEvidenceAdequacyProducer

colonialCandidateWrong : Ontology.WrongType
colonialCandidateWrong = ColonialWrong.colonialAuthorityReclassificationWrongType

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data HerzogFactAutomaticallyIsColonialWrongElement : Set where
data SecurityClassificationAutomaticallyInstantiatesColonialMechanism : Set where
data StructuralSimilarityProvesHistoricalIdentity : Set where
data ColonialMechanismProvesSubjectiveMotive : Set where
data AnalyticalWrongTypeIsRecognisedCauseOfAction : Set where
data TranslationCreatesMunicipalLegalAuthority : Set where

aHerzogFactNeedsTranslation : HerzogFactAutomaticallyIsColonialWrongElement → ⊥
aHerzogFactNeedsTranslation ()

classificationNeedsMechanismProof :
  SecurityClassificationAutomaticallyInstantiatesColonialMechanism → ⊥
classificationNeedsMechanismProof ()

structuralSimilarityDoesNotCreateIdentity : StructuralSimilarityProvesHistoricalIdentity → ⊥
structuralSimilarityDoesNotCreateIdentity ()

mechanismDoesNotMindRead : ColonialMechanismProvesSubjectiveMotive → ⊥
mechanismDoesNotMindRead ()

analyticalWrongDoesNotBecomeCauseOfAction : AnalyticalWrongTypeIsRecognisedCauseOfAction → ⊥
analyticalWrongDoesNotBecomeCauseOfAction ()

translationDoesNotCreateMunicipalAuthority : TranslationCreatesMunicipalLegalAuthority → ⊥
translationDoesNotCreateMunicipalAuthority ()

wrongTypeInterpretationStillDoesNotApplyItself :
  Wrong.WrongTypeInterpretationAutomaticallyApplicable → ⊥
wrongTypeInterpretationStillDoesNotApplyItself = Wrong.wrongTypeInterpretationDoesNotAutoApply

elementDerivationStillDoesNotCreateLiability :
  Elements.ElementDerivationAutomaticallyCreatesLiability → ⊥
elementDerivationStillDoesNotCreateLiability = Elements.elementProofDoesNotAutoCreateLiability

historicalMechanismStillDoesNotBecomeModernMotive :
  ColonialPrereq.WrongTypePrerequisiteBoundary.historicalConstitutiveMechanismAutomaticallyModernPoliceMotive
    ColonialPrereq.canonicalWrongTypePrerequisiteBoundary ≡ false
historicalMechanismStillDoesNotBecomeModernMotive = refl
