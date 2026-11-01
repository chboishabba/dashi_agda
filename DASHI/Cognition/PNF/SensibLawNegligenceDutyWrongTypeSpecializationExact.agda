module DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact where

------------------------------------------------------------------------
-- NEGLIGENCE / DUTY OF CARE AS A WRONGTYPE SPECIALISATION
--
-- This module removes the conceptual isolation of Climate.DutyIssue. Negligence
-- is represented as one WrongType whose elements include duty, breach,
-- causation and damage. Duty is itself a derived legal proposition over reusable
-- factual, relational, doctrinal and institutional predicates.
--
-- Calibration sources:
--   * Donoghue v Stevenson [1932] AC 562.
--   * Woolcock Street Investments Pty Ltd v CDG Pty Ltd [2004] HCA 16.
--   * Mallonland Pty Ltd v Advanta Seeds Pty Ltd [2024] HCA 25.
--   * Pabai v Commonwealth of Australia (No 2) [2025] FCA 796.
--
-- The universal decomposition below is DASHI formal structure; it is not
-- attributed as a verbatim test to any one court.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceBridge

------------------------------------------------------------------------
-- Australian negligence WrongType fixture. It is a theorem-bearing legal
-- ontology specimen, not a claim that this exhausts every negligence variant.
------------------------------------------------------------------------

auCommonLawSystem : Ontology.StableId
auCommonLawSystem = Ontology.stableId "legal-system:AU.common-law.negligence"

bodilyIntegrityInterest : Ontology.StableId
bodilyIntegrityInterest = Ontology.stableId "interest:bodily-integrity"

negligenceWrongType : Ontology.WrongType
negligenceWrongType = Ontology.wrongTypeRecord
  (Ontology.stableId "wrong:AU:negligence")
  auCommonLawSystem
  ((Ontology.stableId "source:Donoghue:[1932]AC562") ∷
   (Ontology.stableId "source:Woolcock:[2004]HCA16") ∷
   (Ontology.stableId "source:Mallonland:[2024]HCA25") ∷
   (Ontology.stableId "source:Pabai:[2025]FCA796") ∷ [])
  (bodilyIntegrityInterest ∷ [])
  []
  []
  Ontology.negligent
  ((Ontology.stableId "harm:physical-injury") ∷
   (Ontology.stableId "harm:death") ∷ [])
  []
  []

------------------------------------------------------------------------
-- Core negligence elements.
------------------------------------------------------------------------

actorD : Ontology.StableId
actorD = Ontology.stableId "actor:defendant"

actorP : Ontology.StableId
actorP = Ontology.stableId "actor:plaintiff"

dutyProposition : Algebra.LegalProposition
dutyProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:negligence:duty")
  Algebra.wrongElementPredicate actorD actorP auCommonLawSystem
  "defendant owes plaintiff the legally relevant duty of care for the specified risk/harm relation"

breachProposition : Algebra.LegalProposition
breachProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:negligence:breach")
  Algebra.wrongElementPredicate actorD actorP auCommonLawSystem
  "the applicable standard of care was breached"

causationProposition : Algebra.LegalProposition
causationProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:negligence:causation")
  Algebra.wrongElementPredicate actorD actorP auCommonLawSystem
  "the legally relevant causal connection between breach and harm is established"

damageProposition : Algebra.LegalProposition
damageProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:negligence:damage")
  Algebra.wrongElementPredicate actorP bodilyIntegrityInterest auCommonLawSystem
  "legally cognisable damage is established"

dutyElement : Elements.LegalElement negligenceWrongType
dutyElement = Elements.legal-element
  (Ontology.stableId "element:negligence:duty")
  Elements.dutyElement dutyProposition refl

breachElement : Elements.LegalElement negligenceWrongType
breachElement = Elements.legal-element
  (Ontology.stableId "element:negligence:breach")
  Elements.breachElement breachProposition refl

causationElement : Elements.LegalElement negligenceWrongType
causationElement = Elements.legal-element
  (Ontology.stableId "element:negligence:causation")
  Elements.causationElement causationProposition refl

damageElement : Elements.LegalElement negligenceWrongType
damageElement = Elements.legal-element
  (Ontology.stableId "element:negligence:damage")
  Elements.damageElement damageProposition refl

------------------------------------------------------------------------
-- Duty-of-care coordinates are stratified by ontological role.
------------------------------------------------------------------------

data DutyCoordinateClass : Set where
  factualDutyFeature : DutyCoordinateClass
  relationalDutyFeature : DutyCoordinateClass
  doctrinalDutyPredicate : DutyCoordinateClass
  institutionalDutyConstraint : DutyCoordinateClass
  downstreamNegligenceElement : DutyCoordinateClass


classifyDutyIssue : Climate.DutyIssue → DutyCoordinateClass
classifyDutyIssue Climate.reasonableForeseeability = factualDutyFeature
classifyDutyIssue Climate.knowledge = factualDutyFeature
classifyDutyIssue Climate.control = factualDutyFeature
classifyDutyIssue Climate.vulnerability = relationalDutyFeature
classifyDutyIssue Climate.assumptionOfResponsibility = relationalDutyFeature
classifyDutyIssue Climate.plaintiffClassDeterminacy = doctrinalDutyPredicate
classifyDutyIssue Climate.harmTypeDeterminacy = doctrinalDutyPredicate
classifyDutyIssue Climate.temporalScope = doctrinalDutyPredicate
classifyDutyIssue Climate.causation = downstreamNegligenceElement
classifyDutyIssue Climate.scopeOfDuty = doctrinalDutyPredicate
classifyDutyIssue Climate.statutoryCoherence = doctrinalDutyPredicate
classifyDutyIssue Climate.coreGovernmentPolicy = institutionalDutyConstraint
classifyDutyIssue Climate.institutionalCompetence = institutionalDutyConstraint
classifyDutyIssue Climate.publicAuthorityFunction = institutionalDutyConstraint
classifyDutyIssue Climate.compensability = downstreamNegligenceElement

classToPropositionKind : DutyCoordinateClass → Algebra.PropositionKind
classToPropositionKind factualDutyFeature = Algebra.factualFeature
classToPropositionKind relationalDutyFeature = Algebra.relationalFeature
classToPropositionKind doctrinalDutyPredicate = Algebra.doctrinalPredicate
classToPropositionKind institutionalDutyConstraint = Algebra.institutionalConstraint
classToPropositionKind downstreamNegligenceElement = Algebra.wrongElementPredicate

issueLabel : Climate.DutyIssue → String
issueLabel Climate.reasonableForeseeability = "reasonable foreseeability"
issueLabel Climate.knowledge = "knowledge"
issueLabel Climate.control = "control"
issueLabel Climate.vulnerability = "vulnerability"
issueLabel Climate.assumptionOfResponsibility = "assumption of responsibility"
issueLabel Climate.plaintiffClassDeterminacy = "plaintiff-class determinacy"
issueLabel Climate.harmTypeDeterminacy = "harm-type determinacy"
issueLabel Climate.temporalScope = "temporal scope"
issueLabel Climate.causation = "causation"
issueLabel Climate.scopeOfDuty = "scope of duty"
issueLabel Climate.statutoryCoherence = "statutory coherence"
issueLabel Climate.coreGovernmentPolicy = "core government policy"
issueLabel Climate.institutionalCompetence = "institutional competence"
issueLabel Climate.publicAuthorityFunction = "public-authority function"
issueLabel Climate.compensability = "compensability"

compileDutyIssue : Climate.DutyIssue → Algebra.LegalProposition
compileDutyIssue issue = Algebra.legal-proposition
  (Ontology.stableId (issueLabel issue))
  (classToPropositionKind (classifyDutyIssue issue))
  actorD actorP auCommonLawSystem
  (issueLabel issue)

------------------------------------------------------------------------
-- Existing source identities compile to the universal source container while
-- preserving proposition-level authority separately.
------------------------------------------------------------------------

edgeSourceRef : Edge.SourceIdentity → Algebra.LegalSourceRef
edgeSourceRef source = Algebra.legal-source-ref
  (Ontology.legalSource
    (Ontology.stableId (Edge.stableIdentifier source))
    auCommonLawSystem
    (SourceBridge.authorityContainerForm (Edge.kind source))
    (Edge.stableIdentifier source)
    "source-effective-date"
    "source-dependent")
  (Edge.authorOrInstitution source)
  (Edge.title source)
  (Edge.stableIdentifier source)

------------------------------------------------------------------------
-- Gate-force adapter. A factor, blocker and evidential requirement are not the
-- same rule shape.
------------------------------------------------------------------------

data DutyContribution : Set where
  contributesForDuty : DutyContribution
  contributesAgainstDuty : DutyContribution
  blocksDutyWhenEstablished : DutyContribution
  constrainsInterpretation : DutyContribution
  requiresEvidenceBeforeDutyResolution : DutyContribution


contribution : Edge.GateForce → DutyContribution
contribution Edge.hardBlocker = blocksDutyWhenEstablished
contribution Edge.factorFor = contributesForDuty
contribution Edge.factorAgainst = contributesAgainstDuty
contribution Edge.interpretiveConstraint = constrainsInterpretation
contribution Edge.evidentialRequirement = requiresEvidenceBeforeDutyResolution

record DutyIssueRuleFragment (receipt : Climate.DutyIssueReceipt) : Set where
  constructor duty-issue-rule-fragment
  field
    proposition : Algebra.LegalProposition
    propositionIsCompiledIssue :
      proposition ≡ compileDutyIssue (Climate.issue receipt)
    source : Algebra.LegalSourceRef
    sourcePreservesReceiptAuthority : String
    role : Algebra.AuthorityRole
    effect : DutyContribution
    dutyTarget : Algebra.LegalProposition
    dutyTargetIsNegligenceDuty : dutyTarget ≡ dutyProposition

open DutyIssueRuleFragment public

compileDutyIssueReceipt :
  (receipt : Climate.DutyIssueReceipt) → DutyIssueRuleFragment receipt
compileDutyIssueReceipt receipt = duty-issue-rule-fragment
  (compileDutyIssue (Climate.issue receipt))
  refl
  (edgeSourceRef (Climate.authority receipt))
  (Edge.stableIdentifier (Climate.authority receipt))
  Algebra.dashReconstructionRole
  (contribution (Climate.gateForce receipt))
  dutyProposition
  refl

------------------------------------------------------------------------
-- Climate duty is therefore a specialisation/query over the generic negligence
-- duty element; it is not a separate legal algebra.
------------------------------------------------------------------------

record ClimateDutySpecialisation (candidate : Climate.CandidateClimateDuty) : Set where
  constructor climate-duty-specialisation
  field
    wrongType : Ontology.WrongType
    wrongTypeIsNegligence : wrongType ≡ negligenceWrongType
    targetElement : Elements.LegalElement negligenceWrongType
    targetIsDuty : targetElement ≡ dutyElement
    candidateReference : String

open ClimateDutySpecialisation public

australiaPhysicalInjuryDutySpecialisation :
  ClimateDutySpecialisation Climate.australiaPhysicalInjuryCandidate
australiaPhysicalInjuryDutySpecialisation = climate-duty-specialisation
  negligenceWrongType refl dutyElement refl
  "Commonwealth / persons present in Australia / climate-attributed physical injury"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DutyIssueIsUniversalLegalOntology : Set where
data EveryDutyCoordinateIsSameOntologicalKind : Set where
data ClimateDutyIsSeparateWrongTypeAlgebra : Set where
data ForeseeabilityAloneDerivesDuty : Set where

climateDutyIssueIsSpecialisationNotUniverse : DutyIssueIsUniversalLegalOntology → ⊥
climateDutyIssueIsSpecialisationNotUniverse ()

dutyCoordinatesStayStratified : EveryDutyCoordinateIsSameOntologicalKind → ⊥
dutyCoordinatesStayStratified ()

climateDutyReusesNegligenceWrongType : ClimateDutyIsSeparateWrongTypeAlgebra → ⊥
climateDutyReusesNegligenceWrongType ()

foreseeabilityDoesNotByItselfDeriveDuty : ForeseeabilityAloneDerivesDuty → ⊥
foreseeabilityDoesNotByItselfDeriveDuty ()
