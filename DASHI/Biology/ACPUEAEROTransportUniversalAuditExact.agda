module DASHI.Biology.ACPUEAEROTransportUniversalAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Biology.ACPUEAEROClaimAuditProtocolExact as Protocol

------------------------------------------------------------------------
-- UNIVERSAL TRANSPORT AUDIT
--
-- AERO 2023 states, immediately after the Gonsalkorale (2022) sentence:
--   "This evidence is relevant to all school-aged learners and to all
--    classrooms."
--
-- This is audited as its own assertion.  The antecedent "this evidence" is
-- source-linked to the preceding Gonsalkorale/context evidence surface, but the
-- universal transport strength is a new proof obligation.
------------------------------------------------------------------------

universalScope : PNF.AssertionScope
universalScope =
  PNF.assertionScope
    "all school-aged learners"
    "all classrooms"
    "the evidence base invoked in the preceding Gonsalkorale/context sentence"
    "not applicable"
    "relevance/applicability of the evidence"
    "unspecified"

universalPredicates : List PNF.PredicateAtom
universalPredicates =
  PNF.predicateAtom
    "all-school-aged-learners"
    PNF.transportPredicate
    "reviewed learner populations × every school-aged learner"
    "the reviewed evidence transports to every school-aged learner"
  ∷ PNF.predicateAtom
    "all-classrooms"
    PNF.transportPredicate
    "reviewed classroom contexts × every classroom"
    "the reviewed evidence transports to every classroom"
  ∷ []

universalAssertion : PNF.PredicateNormalAssertion
universalAssertion =
  PNF.predicateNormalAssertion
    "AERO-HSLB-PURPOSE-UNIVERSAL-001"
    "This evidence is relevant to all school-aged learners and to all classrooms."
    PNF.universalQ
    PNF.descriptiveF
    universalScope
    universalPredicates
    "AERO, How students learn best (2023), Purpose and approach; antecedent evidence source-linked to Gonsalkorale 2022"

learnerTransportObligation : PNF.AssertionObligation
learnerTransportObligation =
  PNF.assertionObligation
    "AERO-HSLB-PURPOSE-UNIVERSAL-001"
    PNF.transportObligation
    "Does the cited/referred evidence establish transport to every school-aged learner?"

classroomTransportObligation : PNF.AssertionObligation
classroomTransportObligation =
  PNF.assertionObligation
    "AERO-HSLB-PURPOSE-UNIVERSAL-001"
    PNF.contextScopeObligation
    "Does the cited/referred evidence establish transport to every classroom context?"

quantifierObligation : PNF.AssertionObligation
quantifierObligation =
  PNF.assertionObligation
    "AERO-HSLB-PURPOSE-UNIVERSAL-001"
    PNF.quantifierObligation
    "Is the universal quantifier all warranted rather than variety/broad relevance?"

universalAudits : List PNF.ObligationAudit
universalAudits =
  PNF.obligationAudit
    learnerTransportObligation
    PNF.partiallyDischarged
    "Gonsalkorale/AERO context synthesis reports primary and secondary students and multiple subgroups"
    "broad subgroup coverage supports relevance beyond one narrow population, but does not itself enumerate or prove every school-aged learner"
  ∷ PNF.obligationAudit
    classroomTransportObligation
    PNF.partiallyDischarged
    "Gonsalkorale/AERO context synthesis reports varied subjects, locations and classroom contexts"
    "varied represented contexts support broad relevance, but variety is not definitionally all classrooms"
  ∷ PNF.obligationAudit
    quantifierObligation
    PNF.unresolved
    "available source wording supports variety/broad relevance; later AERO methodology disclosure explicitly retains context limitations"
    "the all-quantifier needs an additional transport receipt rather than inheriting the weaker reviewed-context claim"
  ∷ []

safeScope : PNF.AssertionScope
safeScope =
  PNF.assertionScope
    "school-aged learners represented by the reviewed evidence"
    "the range of classroom contexts represented by the reviewed evidence"
    "formative assessment, explicit instruction and mastery learning evidence reviewed by AERO"
    "not applicable"
    "broad relevance/applicability"
    "as represented in the reviewed evidence"

safePredicates : List PNF.PredicateAtom
safePredicates =
  PNF.predicateAtom
    "broad-reviewed-relevance"
    PNF.transportPredicate
    "reviewed populations × reviewed contexts"
    "the reviewed evidence supports relevance across varied represented school-aged populations and classroom contexts"
  ∷ []

backwardSafeAssertion : PNF.PredicateNormalAssertion
backwardSafeAssertion =
  PNF.predicateNormalAssertion
    "AERO-HSLB-PURPOSE-UNIVERSAL-001-SAFE"
    "The reviewed evidence supports broad relevance across varied school-aged populations and classroom contexts represented in the synthesis."
    PNF.studyPopulationQ
    PNF.descriptiveF
    safeScope
    safePredicates
    "DASHI backward-safe reconstruction; not an AERO or ACPUE quotation"

sourceChain : List Manifest.SourceChainCoordinate
sourceChain =
  Manifest.sourceChainCoordinate
    Manifest.publishedSurface
    "AERO How students learn best (2023), Purpose and approach"
    true
    "universal sentence recovered"
  ∷ Manifest.sourceChainCoordinate
    Manifest.citedSecondarySource
    "Gonsalkorale 2022 AERO context article via antecedent 'this evidence'"
    true
    "article reports varied contexts/subgroups and three reviewed practices"
  ∷ Manifest.sourceChainCoordinate
    Manifest.citedPrimaryStudy
    "meta-analyses and primary studies behind the context synthesis"
    false
    "not yet fully traced at claim level"
  ∷ []

receipts : List Manifest.TypedClaimReceipt
receipts =
  Manifest.typedClaimReceipt
    Manifest.transportReceipt
    Manifest.partiallyInstalled
    "Gonsalkorale 2022 broad cross-context synthesis"
    "supports varied contexts/subgroups, not an unrestricted all-context theorem"
  ∷ Manifest.typedClaimReceipt
    Manifest.predicateContentReceipt
    Manifest.installed
    "AERO/Gonsalkorale evidence surface"
    "broad relevance predicate retained"
  ∷ []

manifest : Manifest.ManifestClaim
manifest =
  Manifest.manifestClaim
    "AERO-HSLB-PURPOSE-UNIVERSAL-001"
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    (PNF.naturalLanguage universalAssertion)
    universalAssertion
    (Manifest.universalScopeConsequence ∷ Manifest.downstreamPolicyRelevant ∷ [])
    sourceChain
    receipts
    universalAudits
    Manifest.independentUnresolved
    Manifest.independentPartiallyAdmissible
    Manifest.citationCompared
    backwardSafeAssertion
    "Broad relevance is preserved while the universal all-learners/all-classrooms transport strength remains an independent unresolved obligation."

protocolCandidate : Protocol.AuditCandidate
protocolCandidate =
  Protocol.auditCandidate
    "AERO-HSLB-PURPOSE-UNIVERSAL-001"
    (PNF.naturalLanguage universalAssertion)
    "AERO 2023 Purpose and approach, immediately following Gonsalkorale 2022 sentence"
    Protocol.acpueCodeNotYetRecovered
    Protocol.practitionerOrAgencySynthesis
    (Protocol.transportClaim ∷ Protocol.universalClaim ∷ [])
    (Manifest.universalScopeConsequence ∷ Manifest.downstreamPolicyRelevant ∷ [])
    Protocol.highConsequencePriority
    "tests whether broad cross-context evidence has been silently strengthened to universal transport"

record UniversalTransportBoundary : Set where
  constructor universalTransportBoundary
  field
    variedContextsEqualsAllClassrooms : Bool
    representedSubgroupsEqualsEveryLearner : Bool
    antecedentCitationAutomaticallyDischargesUniversal : Bool
    broadRelevanceRetained : Bool
    universalQuantifierNeedsSeparateReceipt : Bool

canonicalUniversalTransportBoundary : UniversalTransportBoundary
canonicalUniversalTransportBoundary =
  universalTransportBoundary false false false true true
