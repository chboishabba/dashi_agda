module DASHI.Biology.ACPUEAEROClaimAuditCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Biology.ACPUEAEROClaimAuditProtocolExact as Protocol

------------------------------------------------------------------------
-- POSITIVE/CALIBRATION CLAIM SPECIMEN
--
-- AERO 2023 working-memory section cites Nelson Cowan (2008),
-- "What are the differences between long-term, short-term, and working
-- memory?", Progress in Brain Research 169:323-338,
-- DOI 10.1016/S0079-6123(07)00020-9.
--
-- Cowan's embedded-processes account treats working memory as involving an
-- activated portion of long-term memory with a smaller capacity-limited focus
-- of attention.  This is a useful calibration because important structural
-- predicates in AERO's sentence have genuine source support.  The audit still
-- leaves AERO-specific pedagogical/temporal wording as separate obligations.
------------------------------------------------------------------------

cowanScope : PNF.AssertionScope
cowanScope =
  PNF.assertionScope
    "human learners"
    "working-memory processing"
    "attention to currently active information, including information activated from long-term memory"
    "not a pedagogical comparator"
    "information available for current cognitive processing"
    "while information remains in the relevant activated/focal state"

cowanPredicates : List PNF.PredicateAtom
cowanPredicates =
  PNF.predicateAtom
    "long-term-memory-activation"
    PNF.populationPredicate
    "long-term memory × activated information"
    "working-memory processing can involve information represented within an activated portion of long-term memory"
  ∷ PNF.predicateAtom
    "focus-of-attention"
    PNF.contextPredicate
    "activated information × selective attention"
    "a capacity-limited subset of activated information is within the focus of attention"
  ∷ PNF.predicateAtom
    "current-processing-depends-on-focus"
    PNF.temporalPredicate
    "information × current cognitive episode"
    "the immediately available processing state is related to what is activated/attended at the relevant time"
  ∷ []

cowanAEROAssertion : PNF.PredicateNormalAssertion
cowanAEROAssertion =
  PNF.predicateNormalAssertion
    "AERO-HSLB-WM-COWAN-001"
    "Working memory can use both new information and prior knowledge retrieved from long-term memory during the learning process, but it can only process information while it is being thought about and focused on (Cowan, 2008)."
    PNF.boundedUniversalQ
    PNF.descriptiveF
    cowanScope
    cowanPredicates
    "AERO, How students learn best (2023), working-memory section; Cowan 2008"

activationObligation : PNF.AssertionObligation
activationObligation =
  PNF.assertionObligation
    "AERO-HSLB-WM-COWAN-001"
    PNF.predicateContentObligation
    "Does Cowan's model support working-memory access to an activated portion of long-term memory?"

attentionObligation : PNF.AssertionObligation
attentionObligation =
  PNF.assertionObligation
    "AERO-HSLB-WM-COWAN-001"
    PNF.contextScopeObligation
    "Does Cowan support a distinct focus-of-attention component within activated memory?"

temporalOnlyObligation : PNF.AssertionObligation
temporalOnlyObligation =
  PNF.assertionObligation
    "AERO-HSLB-WM-COWAN-001"
    PNF.temporalObligation
    "Does the exact strong wording 'can only process information while it is being thought about and focused on' follow from Cowan 2008 at the same scope?"

cowanDesign : Design.StudyDesignReceipt
cowanDesign =
  Design.studyDesignReceipt
    "Cowan-2008-memory-model-review"
    Design.scholarlyReview
    "review/theoretical synthesis of long-term, short-term and working-memory literatures"
    "not a single randomised allocation"
    "compares theoretical distinctions/models rather than one intervention comparator"
    "review draws on behavioural/cognitive evidence and model distinctions"
    "not a single participant-flow experiment"
    "review-level synthesis"
    "not an implementation-fidelity trial"
    "not one multiplicity-controlled intervention analysis"
    "not one common intervention effect size"
    "uncertainty is theoretical/evidential rather than a single confidence interval"
    "human memory architecture; educational transport requires separate pedagogical interpretation"
    Design.informant
    Design.validityModerate
    Design.validityModerate
    "Nelson Cowan (2008), Progress in Brain Research 169:323-338, DOI 10.1016/S0079-6123(07)00020-9"

cowanEvidence : Design.EvidenceReceipt
cowanEvidence =
  Design.evidenceReceipt
    "Cowan-2008-recovered-model-surface"
    cowanDesign
    "Nelson Cowan (2008), DOI 10.1016/S0079-6123(07)00020-9"
    "Cowan's embedded-processes model distinguishes long-term memory, an activated portion, and a smaller capacity-limited focus of attention; later literature explicitly describes Cowan 2008 in these terms."
    "source/abstract and independent model-description triangulation"
    "AERO sentence -> Cowan citation -> Cowan embedded-processes model; exact clause-level wording remains independently audited"
    "DASHI audit interpretation"
    "source architecture supports activation/focus predicates more directly than the exact pedagogical temporal paraphrase"

cowanAudits : List PNF.ObligationAudit
cowanAudits =
  PNF.obligationAudit
    activationObligation
    PNF.discharged
    "Cowan model: activated portion of long-term memory"
    "the activated-LTM structural predicate is source-concordant"
  ∷ PNF.obligationAudit
    attentionObligation
    PNF.discharged
    "Cowan model: capacity-limited focus of attention within activated memory"
    "the focus-of-attention predicate is source-concordant"
  ∷ PNF.obligationAudit
    temporalOnlyObligation
    PNF.partiallyDischarged
    "attention/current accessibility is central to the model"
    "the strong 'only process while being thought about and focused on' prose is a pedagogical compression whose exact modal/temporal force should not be inferred merely from the diagrammatic architecture"
  ∷ []

cowanSafeAssertion : PNF.PredicateNormalAssertion
cowanSafeAssertion =
  PNF.predicateNormalAssertion
    "AERO-HSLB-WM-COWAN-001-SAFE"
    "Cowan's embedded-processes account places a capacity-limited focus of attention within an activated portion of long-term memory, allowing currently activated prior information to contribute to working-memory processing."
    PNF.studyPopulationQ
    PNF.descriptiveF
    cowanScope
    cowanPredicates
    "DASHI backward-safe reconstruction; not a quotation from Cowan or ACPUE"

cowanSourceChain : List Manifest.SourceChainCoordinate
cowanSourceChain =
  Manifest.sourceChainCoordinate
    Manifest.publishedSurface
    "AERO How students learn best (2023), working-memory section"
    true
    "AERO citation-bearing sentence recovered"
  ∷ Manifest.sourceChainCoordinate
    Manifest.citedPrimaryStudy
    "Cowan 2008, DOI 10.1016/S0079-6123(07)00020-9"
    true
    "source identity and embedded-processes memory architecture recovered"
  ∷ Manifest.sourceChainCoordinate
    Manifest.underlyingDatasetOrArtifact
    "individual empirical studies synthesised by Cowan 2008"
    false
    "not required for first-level citation concordance; needed for deeper evidence-strength audit"
  ∷ []

cowanReceipts : List Manifest.TypedClaimReceipt
cowanReceipts =
  Manifest.typedClaimReceipt
    Manifest.predicateContentReceipt
    Manifest.installed
    "Cowan 2008 embedded-processes architecture"
    "activated-LTM and focus-of-attention predicates"
  ∷ Manifest.typedClaimReceipt
    Manifest.transportReceipt
    Manifest.unresolved
    "memory architecture does not itself establish every pedagogical consequence"
    "education-practice transport remains separate"
  ∷ []

cowanManifest : Manifest.ManifestClaim
cowanManifest =
  Manifest.manifestClaim
    "AERO-HSLB-WM-COWAN-001"
    ""
    (PNF.naturalLanguage cowanAEROAssertion)
    cowanAEROAssertion
    (Manifest.ordinaryConsequence ∷ Manifest.frameworkCentral ∷ [])
    cowanSourceChain
    cowanReceipts
    cowanAudits
    Manifest.independentUnresolved
    Manifest.independentPartiallyAdmissible
    Manifest.citationCompared
    cowanSafeAssertion
    "Calibration specimen: two important structural predicates are independently supported. The exact strong temporal/modal paraphrase and pedagogical transport remain separately scoped rather than forcing an all-or-nothing verdict."

cowanProtocolCandidate : Protocol.AuditCandidate
cowanProtocolCandidate =
  Protocol.auditCandidate
    "AERO-HSLB-WM-COWAN-001"
    (PNF.naturalLanguage cowanAEROAssertion)
    "AERO 2023 working-memory section"
    Protocol.acpueCodeNotYetRecovered
    Protocol.scholarlyReview
    (Protocol.boundedDescriptive ∷ [])
    (Manifest.ordinaryConsequence ∷ Manifest.frameworkCentral ∷ [])
    Protocol.calibrationPriority
    "positive-control case: audit architecture must preserve supported predicates and not structurally manufacture mismatch"

record CowanCalibrationBoundary : Set where
  constructor cowanCalibrationBoundary
  field
    sourceSupportsNoPredicates : Bool
    activatedLTMAndAttentionSupported : Bool
    exactAEROParaphraseEqualsCowanModelDefinitionally : Bool
    memoryModelAloneProvesPedagogicalPolicy : Bool
    calibrationCaseCanReturnPositiveSupport : Bool

canonicalCowanCalibrationBoundary : CowanCalibrationBoundary
canonicalCowanCalibrationBoundary =
  cowanCalibrationBoundary false true false false true
