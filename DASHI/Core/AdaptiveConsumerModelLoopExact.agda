module DASHI.Core.AdaptiveConsumerModelLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Core.AffectedDependencyClosureExact as Dependency

------------------------------------------------------------------------
-- COHERENT ADAPTIVE CONSUMER MODEL LOOP
--
-- Repository-native capstone for the recurrent architecture:
--
-- fine state
--   -> candidate consumer reduction
--   -> exact certificate | approximate decision-margin certificate | counterexample
--   -> reopenable model portfolio
--   -> live evidence/model fibre
--   -> robust intervention if available, subject to separate authority
--      OR choose discriminating information / higher fidelity
--   -> new evidence
--   -> selectively reopen only dependency-affected certificates.
--
-- This module deliberately composes existing theorem owners instead of creating
-- a second future-equivalence, fidelity, evidence, intervention, authority or
-- dependency calculus.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Three-way assessment of one candidate.
------------------------------------------------------------------------

data ConsumerAssessment
    {Fine Action Observation Decision : Set}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    (candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe) : Set₁ where
  exactCertified :
    Search.CandidateCertification candidate →
    ConsumerAssessment candidate

  approximateCertified :
    (model : Approx.ApproximateTraceReduction Fine Action Observation) →
    (decide : Observation → Decision) →
    Approx.ApproximateDecisionCertificate model decide →
    ConsumerAssessment candidate

  refutedForConsumer :
    Search.CandidateRefutation candidate →
    ConsumerAssessment candidate

exactAssessmentExcludesCounterexample :
  ∀ {Fine Action Observation Decision}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe} →
  (certificate : Search.CandidateCertification candidate) →
  (actionLabel : Action → String) →
  Search.CandidateRefutation candidate →
  ⊥
exactAssessmentExcludesCounterexample =
  Search.certificationExcludesCounterexample

approximateAssessmentPreservesDeclaredDecision :
  ∀ {Fine Action Observation Decision}
    {model : Approx.ApproximateTraceReduction Fine Action Observation}
    {decide : Observation → Decision} →
  Approx.ApproximateDecisionCertificate model decide →
  (input : Approx.TraceInput Fine Action) →
  decide
    (DASHI.Core.AdaptiveFidelityConsumerMarginExact.low
      (Approx.approximateTraceFidelityPair model) input)
  ≡
  decide
    (DASHI.Core.AdaptiveFidelityConsumerMarginExact.high
      (Approx.approximateTraceFidelityPair model) input)
approximateAssessmentPreservesDeclaredDecision =
  Approx.approximateReductionDecisionSafe

------------------------------------------------------------------------
-- 2. Reopenable portfolio.  Cost/score is search order only; candidate status
-- remains active/reopenable/refuted under the existing forest semantics.
------------------------------------------------------------------------

record ReopenableReductionPortfolio
    {Fine Action Observation : Set}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation} : Set₁ where
  constructor reopenableReductionPortfolio
  field
    candidates : List
      (Forest.HypothesisEntry
        (Search.ReductionCandidate Fine Action Observation fineStep observe)
        Nat)
    portfolioReference : String
    searchOrderReference : String
    reopeningPolicyReference : String

open ReopenableReductionPortfolio public

------------------------------------------------------------------------
-- 3. Live evidence fibre and intervention branch.
--
-- Hypotheses are fine states compatible with current evidence.  The action
-- branch is explicitly separate from authority: robust model-relative decision
-- support does not itself authorize execution.
------------------------------------------------------------------------

record LiveEvidenceFibre
    (Evidence Fine : Set) : Set₁ where
  constructor liveEvidenceFibre
  field
    compatible : Envelope.Compatible Evidence Fine
    evidence : Evidence
    evidenceReference : String

open LiveEvidenceFibre public

record AuthorityGate (Intervention : Set) : Set₁ where
  constructor authorityGate
  field
    authority : Intervention → Governed.AuthorityDecision
    authorityReference : String

open AuthorityGate public

data AdaptiveDecisionBranch
    {Hypothesis Intervention Outcome : Set}
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Declared : Hypothesis → Set)
    (authorityGate : AuthorityGate Intervention) : Set₁ where

  actSubjectToAuthority :
    (intervention : Intervention) →
    Robust.RobustlyNoWorseThanBaseline system Declared intervention →
    authority authorityGate intervention ≡ Governed.promote →
    AdaptiveDecisionBranch system Declared authorityGate

  seekDiscriminatingInformationOrFidelity :
    Robust.HypothesisActionConflict system Declared →
    (measurementReference : String) →
    (fidelityReference : String) →
    AdaptiveDecisionBranch system Declared authorityGate

------------------------------------------------------------------------
-- 4. New evidence and selective reopening.
------------------------------------------------------------------------

record EvidenceUpdate (Evidence : Set) : Set where
  constructor evidenceUpdate
  field
    before : Evidence
    after : Evidence
    updateReference : String

open EvidenceUpdate public

record SelectiveCertificateReopening
    (Artifact : Set)
    (Depends : Artifact → Artifact → Set)
    (changed : Artifact) : Set₁ where
  constructor selectiveCertificateReopening
  field
    affectedCertificate : Artifact
    dependencyPath :
      Dependency.AffectedClosure Depends changed affectedCertificate
    reopeningReference : String

open SelectiveCertificateReopening public

------------------------------------------------------------------------
-- 5. Whole loop package.  This is intentionally an architecture carrier rather
-- than an automatic controller: applications still supply the consumer,
-- evidence fibre, intervention preference relation, authority and dependencies.
------------------------------------------------------------------------

record AdaptiveConsumerModelLoop : Set₂ where
  constructor adaptiveConsumerModelLoop
  field
    Fine Action Observation Decision Evidence Intervention Outcome Artifact : Set

    fineStep : Action → Fine → Fine
    observe : Fine → Observation

    candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe
    assessment : ConsumerAssessment {Decision = Decision} candidate
    portfolio : ReopenableReductionPortfolio
      {fineStep = fineStep} {observe = observe}

    liveFibre : LiveEvidenceFibre Evidence Fine

    interventionSystem : Robust.HypothesisInterventionSystem
      Fine Intervention Outcome
    authorityGate : AuthorityGate Intervention
    decisionBranch : AdaptiveDecisionBranch
      interventionSystem
      (Envelope.Compatible._compatible_ (compatible liveFibre) (evidence liveFibre))
      authorityGate

    evidenceUpdate : EvidenceUpdate Evidence

    Depends : Artifact → Artifact → Set
    changedArtifact : Artifact
    selectiveReopening :
      SelectiveCertificateReopening Artifact Depends changedArtifact

    consumerReference : String
    experimentLanguageReference : String
    validationReference : String

------------------------------------------------------------------------
-- Since projections out of a record field are syntactically awkward for the
-- dependent fibre above, expose the live-declaration helper explicitly.
------------------------------------------------------------------------

LiveDeclared :
  ∀ {Evidence Fine} →
  LiveEvidenceFibre Evidence Fine → Fine → Set
LiveDeclared fibre = compatible fibre (evidence fibre)

------------------------------------------------------------------------
-- A less dependent application-facing capstone using LiveDeclared directly.
------------------------------------------------------------------------

record AdaptiveConsumerLoopReceipt : Set₂ where
  constructor adaptiveConsumerLoopReceipt
  field
    Fine Action Observation Decision Evidence Intervention Outcome Artifact : Set
    fineStep : Action → Fine → Fine
    observe : Fine → Observation

    candidate : Search.ReductionCandidate
      Fine Action Observation fineStep observe
    assessment : ConsumerAssessment {Decision = Decision} candidate
    portfolio : ReopenableReductionPortfolio
      {fineStep = fineStep} {observe = observe}

    liveFibre : LiveEvidenceFibre Evidence Fine
    interventionSystem : Robust.HypothesisInterventionSystem
      Fine Intervention Outcome
    authorityGate : AuthorityGate Intervention
    decisionBranch : AdaptiveDecisionBranch
      interventionSystem (LiveDeclared liveFibre) authorityGate

    newEvidence : EvidenceUpdate Evidence

    Depends : Artifact → Artifact → Set
    changedArtifact : Artifact
    selectiveReopening :
      SelectiveCertificateReopening Artifact Depends changedArtifact

    fineWorldReference : String
    reductionReference : String
    portfolioReference : String
    interventionConsumerReference : String
    measurementOrFidelityReference : String
    evidenceAssimilationReference : String
    reopeningReference : String

------------------------------------------------------------------------
-- Boundary truths for the coherent architecture.
------------------------------------------------------------------------

record AdaptiveConsumerLoopBoundary : Set where
  constructor adaptiveConsumerLoopBoundary
  field
    exactCertificateMeansFutureSafeForDeclaredConsumer : Bool
    approximateCertificateMeansDecisionSafeWithinDeclaredMargin : Bool
    counterexampleRefutesCandidateForDeclaredConsumer : Bool
    deferredPortfolioMemberIsAutomaticallyRefuted : Bool
    deferredPortfolioMemberIsAutomaticallyRefutedIsFalse :
      deferredPortfolioMemberIsAutomaticallyRefuted ≡ false
    robustInterventionRequiresPointIdentification : Bool
    robustInterventionRequiresPointIdentificationIsFalse :
      robustInterventionRequiresPointIdentification ≡ false
    robustInterventionAutomaticallyHasAuthority : Bool
    robustInterventionAutomaticallyHasAuthorityIsFalse :
      robustInterventionAutomaticallyHasAuthority ≡ false
    evidenceUpdateRequiresEveryCertificateToReopen : Bool
    evidenceUpdateRequiresEveryCertificateToReopenIsFalse :
      evidenceUpdateRequiresEveryCertificateToReopen ≡ false
    dependencyAffectedCertificatesMustBeReconsidered : Bool

canonicalAdaptiveConsumerLoopBoundary : AdaptiveConsumerLoopBoundary
canonicalAdaptiveConsumerLoopBoundary =
  adaptiveConsumerLoopBoundary
    true true true false refl false refl false refl false refl true
