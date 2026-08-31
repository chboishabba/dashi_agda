module DASHI.Biology.ACPUEAEROEducationAssertionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Dialectic
import DASHI.Biology.EducationCorpusSourceRegistry as BrownSources

------------------------------------------------------------------------
-- SOURCE-BOUNDED ACPUE <-> AERO EDUCATION ASSERTION AUDIT
--
-- Public-source facts are retained as source surfaces.  DASHI's richer PNF,
-- admissibility, dialectical and promotion machinery is a repository-native
-- extension and is NOT attributed to ACPUE, AERO or Alice Brown.
------------------------------------------------------------------------

record ACPUEAuditSourceSurface : Set where
  constructor acpueAuditSourceSurface
  field
    projectTitle : String
    auditedAERODocument : String
    statedReferenceCount : Nat
    statedClaimCount : Nat
    sourceCoding : List String
    multiCitationClaimsCheckedPerSource : Bool
    unclearCasesFavouredAERO : Bool
    firstLevelOnlyChecksCitationMatch : Bool
    deeperPrimaryStudyAnalysisAnnounced : Bool
    sourceURL : String

open ACPUEAuditSourceSurface public

canonicalACPUEAuditSourceSurface : ACPUEAuditSourceSurface
canonicalACPUEAuditSourceSurface =
  acpueAuditSourceSurface
    "Evaluating AERO's evidence claims"
    "AERO (2023), How students learn best: an overview of the learning process and the most effective teaching practices"
    61
    106
    ("Matches" ∷ "Does not match" ∷ "Plausible" ∷ [])
    true
    true
    true
    true
    "https://acpue.org/projects/aero/"

record AEROEvidenceGovernanceSourceSurface : Set where
  constructor aeroEvidenceGovernanceSourceSurface
  field
    standardsPrioritiseRigourAndRelevance : Bool
    synthesisUsesStandardsForEvidenceSelection : Bool
    qualityProcessMethodsFitQuestion : Bool
    qualityProcessChecksLimitationsAndAlternatives : Bool
    qualityProcessFindingsSupportedByEvidence : Bool
    qualityProcessConclusionsTransparent : Bool
    standardsURL : String
    qualityURL : String
    responsibleResearchCode : String

open AEROEvidenceGovernanceSourceSurface public

canonicalAEROEvidenceGovernanceSourceSurface : AEROEvidenceGovernanceSourceSurface
canonicalAEROEvidenceGovernanceSourceSurface =
  aeroEvidenceGovernanceSourceSurface
    true true true true true true
    "https://www.edresearch.edu.au/other/agency-publications/evidence/standards-evidence"
    "https://www.edresearch.edu.au/about-us/how-aero-works/quality-research"
    "AERO Code for the responsible conduct of research and evaluation, Version 01, June 2025"

record TeachingLearningCommissionSourceSurface : Set where
  constructor teachingLearningCommissionSourceSurface
  field
    agreementStatus : String
    proposedBodies : List String
    coordinationPurpose : String
    stakeholderConsultationDirected : Bool
    workingGroupPurpose : String
    sourceReference : String

open TeachingLearningCommissionSourceSurface public

canonicalTeachingLearningCommissionSourceSurface : TeachingLearningCommissionSourceSurface
canonicalTeachingLearningCommissionSourceSurface =
  teachingLearningCommissionSourceSurface
    "Education Ministers reached in-principle agreement in October 2025"
    ("ACARA" ∷ "AITSL" ∷ "AERO" ∷ "ESA" ∷ [])
    "greater coordination between curriculum, teaching, assessment, research and reporting"
    true
    "design, governance, implementation, stakeholder engagement and consultation"
    "Education Ministers Meeting Communique, October 2025"

------------------------------------------------------------------------
-- ACPUE's source coding is preserved but not mistaken for the generic audit
-- ontology.  A single "does not match" can decompose into different typed
-- failures with different policy significance.
------------------------------------------------------------------------

data ExpandedAuditFinding : Set where
  fullyAdmissibleFinding
  partiallyAdmissibleFinding
  predicateContentMismatch
  quantifierOverreach
  populationScopeOverreach
  contextScopeOverreach
  causalStrengthOverreach
  comparatorDropped
  outcomeMismatch
  designQuestionMismatch
  provenanceBreak
  sameScopeContradiction
  dialecticalCounterevidence
  unresolvedAudit : ExpandedAuditFinding

record ClaimSourceBidiAudit : Set where
  constructor claimSourceBidiAudit
  field
    publishedAssertion : PNF.PredicateNormalAssertion
    sourceEvidence : Design.EvidenceReceipt
    obligationAudits : List PNF.ObligationAudit
    expandedFinding : ExpandedAuditFinding
    backwardSafeAssertion : PNF.PredicateNormalAssertion
    backwardReading : String

open ClaimSourceBidiAudit public

------------------------------------------------------------------------
-- Situated interpretation / epistemic provenance.
------------------------------------------------------------------------

record SituatedInterpretation : Set where
  constructor situatedInterpretation
  field
    participantRole : Design.EpistemicRole
    researcherRole : String
    educationalContext : String
    method : String
    transformations : String
    uncertainty : String
    provenanceReference : String

open SituatedInterpretation public

record EpistemicProvenance : Set where
  constructor epistemicProvenance
  field
    observedEvidence : String
    selection : String
    extraction : String
    coding : String
    synthesis : String
    interpretation : SituatedInterpretation

open EpistemicProvenance public

------------------------------------------------------------------------
-- Alice Brown corpus cross-pollination.
--
-- The canonical source registry already preserves exact paper/source
-- boundaries.  Here we expose what those fibres are useful FOR in the audit;
-- those uses are DASHI interpretations, not claims that Brown et al. proposed
-- this ACPUE/AERO architecture.
------------------------------------------------------------------------

record AliceBrownAuditCrossPollination : Set where
  constructor aliceBrownAuditCrossPollination
  field
    sourceRegistry : BrownSources.EducationCorpusSourceRegistry
    sourceRegistryCanonical :
      sourceRegistry ≡ BrownSources.canonicalEducationCorpusSourceRegistry
    aiFeedbackUse : String
    humourFrameworkUse : String
    studentVoiceUse : String
    onlineSupportUse : String
    ecologyOfDataUse : String
    parentObserverUse : String
    sourceClaimsRemainDistinctFromDashiUse : Bool

open AliceBrownAuditCrossPollination public

canonicalAliceBrownAuditCrossPollination : AliceBrownAuditCrossPollination
canonicalAliceBrownAuditCrossPollination =
  aliceBrownAuditCrossPollination
    BrownSources.canonicalEducationCorpusSourceRegistry refl
    "transformation provenance: machine classification/aggregation remains a bounded proxy rather than semantic or pedagogical authority"
    "complex conditional assertion regression: humour is represented through multiple context/presenter/content/delivery/type/feedback considerations rather than one atomic intervention-effect slogan"
    "epistemic-role provenance: respondent, domain-expert, co-design and agency roles must not be collapsed"
    "scope regression: student-identified support families in a bounded context do not automatically become universal causal interventions"
    "situated interpretation and custodianship: person-place context and analytic responsibility survive downstream use"
    "multi-observer regression: parent testimony, student testimony and institutional interpretation remain distinct observer fibres"
    true

------------------------------------------------------------------------
-- Policy promotion gate.
--
-- The integrated-commission risk is amplification across research -> guidance
-- -> standards/curriculum/assessment.  A downstream assertion therefore needs
-- BOTH a PNF promotion receipt and evidence admissible for the relevant
-- obligation.  Epistemic provenance is carried rather than erased.
------------------------------------------------------------------------

record PolicyPromotionGate : Set where
  constructor policyPromotionGate
  field
    proposal : PNF.ProposedPromotion
    promotionReceipt : PNF.PromotionReceipt (PNF.delta proposal)
    evidenceAudit : Design.EvidenceForObligation
    admissibility : Design.AdmissibleForPromotion (Design.finding evidenceAudit)
    provenance : EpistemicProvenance
    gateReading : String

open PolicyPromotionGate public

policyGateHasPromotionReceipt :
  (gate : PolicyPromotionGate) →
  PNF.PromotionReceipt (PNF.delta (proposal gate))
policyGateHasPromotionReceipt = promotionReceipt

policyGateHasAdmissibility :
  (gate : PolicyPromotionGate) →
  Design.AdmissibleForPromotion (Design.finding (evidenceAudit gate))
policyGateHasAdmissibility = admissibility

------------------------------------------------------------------------
-- Submission-facing institutional requirements.  They are recommendations
-- generated by the DASHI audit architecture, not statements that the current
-- Commission proposal already contains these mechanisms.
------------------------------------------------------------------------

commissionSubmissionRecommendations : List String
commissionSubmissionRecommendations =
  "claim-level traceability: published assertion -> PNF obligations -> source -> evidence passage -> design -> audit result"
  ∷ "scope preservation: population, setting, comparator, outcome, time and transport conditions remain explicit"
  ∷ "no silent strengthening of quantifier, causal force, comparative force or normative force"
  ∷ "experimental-design receipts linked to the kinds of question each design can warrant"
  ∷ "independent/adversarial review for high-consequence synthesis and downstream policy translation"
  ∷ "public claim-level correction and version history"
  ∷ "contestability: reproducible external evidence challenges receive a substantive response"
  ∷ "research synthesis authority remains distinguishable from downstream curriculum, standards and assessment authority"
  ∷ "uncertainty and counterevidence propagate downstream rather than disappearing during translation"
  ∷ "epistemic roles and situated participant knowledge are preserved where relevant to the assertion"
  ∷ "automated extraction, coding or synthesis preserves transformation provenance and does not acquire semantic authority by automation"
  ∷ []

record ACPUEAEROBidiBoundary : Set where
  constructor acpueAeroBidiBoundary
  field
    acpueThreeWayCodingIsGenericOntology : Bool
    citationMatchProvesUnderlyingPrimaryEvidence : Bool
    citationMismatchProvesOppositePedagogy : Bool
    nullEvidenceIsLogicalNegation : Bool
    oneDesignAnswersEveryEducationQuestion : Bool
    studentVoiceAutomaticallyCreatesGoverningAuthority : Bool
    integrationMayAmplifyUpstreamClaimStrengthening : Bool
    downstreamStrengtheningNeedsExplicitReceipt : Bool
    aliceBrownSourcesRewrittenAsACPUEClaims : Bool

canonicalACPUEAEROBidiBoundary : ACPUEAEROBidiBoundary
canonicalACPUEAEROBidiBoundary =
  acpueAeroBidiBoundary false false false false false false true true false
