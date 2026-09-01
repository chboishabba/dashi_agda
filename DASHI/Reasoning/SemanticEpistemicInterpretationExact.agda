module DASHI.Reasoning.SemanticEpistemicInterpretationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SEMANTIC : EPISTEMIC INTERPRETATION
--
-- An observed proposition can matter at several explanatory scales without
-- proving any one of them.  This owner separates:
--
--   local observation
--   operational/process interpretation
--   institutional/governance interpretation
--   incentive/political-economy interpretation
--
-- The BIDI direction is:
--
--   observation -> candidate meaning fibre
--   desired meaning -> evidential demands required to support that meaning.
--
-- In particular, interpretation is not a free logical consequence of an
-- observation.  Stronger system-level readings require independently discharged
-- evidence obligations.
------------------------------------------------------------------------

data InterpretationScale : Set where
  localObservationScale
  operationalProcessScale
  institutionalGovernanceScale
  incentiveStructureScale
  politicalEconomyScale
  : InterpretationScale

data SystemEvidenceDemand : Set where
  assayValidationDemand
  recurrenceDemand
  processTraceabilityDemand
  releaseControlDemand
  regulatoryRuleDemand
  enforcementPracticeDemand
  incentiveStructureDemand
  ownershipMarketStructureDemand
  externalityAllocationDemand
  causalMediationDemand
  comparativeInstitutionalDemand
  counterfactualInstitutionalDemand
  populationTransportDemand
  : SystemEvidenceDemand

record SemanticEpistemicProblem : Set₁ where
  constructor semanticEpistemicProblem
  field
    Observation : Set
    Meaning : Set
    observedMeaning : Observation → Meaning → Set
    scale : Meaning → InterpretationScale
    requires : Meaning → SystemEvidenceDemand → Set
    observationReference : Observation → String
    meaningReference : Meaning → String
    interpretationPolicyReference : String

open SemanticEpistemicProblem public

------------------------------------------------------------------------
-- Candidate meaning and backwards evidence-demand surfaces.
------------------------------------------------------------------------

record CandidateSystemMeaning
    (problem : SemanticEpistemicProblem)
    (observation : Observation problem) : Set₁ where
  constructor candidateSystemMeaning
  field
    meaning : Meaning problem
    licensedAsCandidate : observedMeaning problem observation meaning
    candidateReference : String
    notYetSystemCauseReference : String

open CandidateSystemMeaning public

record EvidenceDemandReceipt
    (demand : SystemEvidenceDemand) : Set where
  constructor evidenceDemandReceipt
  field
    evidenceReference : String
    validationReference : String
    provenanceReference : String

open EvidenceDemandReceipt public

record SupportedSystemMeaning
    (problem : SemanticEpistemicProblem)
    (meaning : Meaning problem) : Set₁ where
  constructor supportedSystemMeaning
  field
    dischargeRequiredDemand :
      (demand : SystemEvidenceDemand) →
      requires problem meaning demand →
      EvidenceDemandReceipt demand
    supportAuditReference : String
    causalScopeReference : String
    comparisonReference : String

open SupportedSystemMeaning public

------------------------------------------------------------------------
-- BIDI package.  The forward direction may return several meanings; the
-- backward direction exposes the evidence needed for a selected reading.
------------------------------------------------------------------------

record SemanticEpistemicBidi
    (problem : SemanticEpistemicProblem) : Set₁ where
  constructor semanticEpistemicBidi
  field
    forwardCandidates :
      (observation : Observation problem) →
      List (CandidateSystemMeaning problem observation)
    backwardDemands : Meaning problem → List SystemEvidenceDemand
    forwardCompletenessReference : String
    backwardDemandCoverageReference : String
    nonInvertibilityReference : String

open SemanticEpistemicBidi public

------------------------------------------------------------------------
-- Interpretation authority remains distinct from logical consequence.
------------------------------------------------------------------------

data InterpretationAuthority : Set where
  candidateInterpretation
  evidenceQualifiedInterpretation
  supportedSystemInterpretation
  : InterpretationAuthority

candidateNotSupported :
  candidateInterpretation ≡ supportedSystemInterpretation → ⊥
candidateNotSupported ()

record SemanticEpistemicBoundary : Set where
  constructor semanticEpistemicBoundary
  field
    oneObservationUniquelyDeterminesSystemCause : Bool
    oneObservationUniquelyDeterminesSystemCauseIsFalse :
      oneObservationUniquelyDeterminesSystemCause ≡ false
    systemInterpretationMayBeAUsefulCandidate : Bool
    systemInterpretationMayBeAUsefulCandidateIsTrue :
      systemInterpretationMayBeAUsefulCandidate ≡ true
    strongerPoliticalEconomyReadingRequiresAdditionalEvidence : Bool
    strongerPoliticalEconomyReadingRequiresAdditionalEvidenceIsTrue :
      strongerPoliticalEconomyReadingRequiresAdditionalEvidence ≡ true
    backwardEvidenceDemandsAreFirstClass : Bool
    backwardEvidenceDemandsAreFirstClassIsTrue :
      backwardEvidenceDemandsAreFirstClass ≡ true
    semanticInterpretationEqualsLogicalEntailment : Bool
    semanticInterpretationEqualsLogicalEntailmentIsFalse :
      semanticInterpretationEqualsLogicalEntailment ≡ false

canonicalSemanticEpistemicBoundary : SemanticEpistemicBoundary
canonicalSemanticEpistemicBoundary =
  semanticEpistemicBoundary
    false refl
    true refl
    true refl
    true refl
    false refl
