module DASHI.Core.AdaptiveConsumerModelLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Core.AffectedDependencyClosureExact as Dependency

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
  decide (Fidelity.low (Approx.approximateTraceFidelityPair model) input)
  ≡
  decide (Fidelity.high (Approx.approximateTraceFidelityPair model) input)
approximateAssessmentPreservesDeclaredDecision =
  Approx.approximateReductionDecisionSafe

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

record LiveEvidenceFibre (Evidence Fine : Set) : Set₁ where
  constructor liveEvidenceFibre
  field
    compatible : Envelope.Compatible Evidence Fine
    evidence : Evidence
    evidenceReference : String
open LiveEvidenceFibre public

LiveDeclared : ∀ {Evidence Fine} → LiveEvidenceFibre Evidence Fine → Fine → Set
LiveDeclared fibre = compatible fibre (evidence fibre)

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
    dependencyPath : Dependency.AffectedClosure Depends changed affectedCertificate
    reopeningReference : String
open SelectiveCertificateReopening public

record AdaptiveConsumerLoopReceipt : Set₂ where
  constructor adaptiveConsumerLoopReceipt
  field
    Fine Action Observation Decision Evidence Intervention Outcome Artifact : Set
    fineStep : Action → Fine → Fine
    observe : Fine → Observation
    candidate : Search.ReductionCandidate Fine Action Observation fineStep observe
    assessment : ConsumerAssessment {Decision = Decision} candidate
    portfolio : ReopenableReductionPortfolio {fineStep = fineStep} {observe = observe}
    liveFibre : LiveEvidenceFibre Evidence Fine
    interventionSystem : Robust.HypothesisInterventionSystem Fine Intervention Outcome
    authorityGate : AuthorityGate Intervention
    decisionBranch : AdaptiveDecisionBranch interventionSystem (LiveDeclared liveFibre) authorityGate
    newEvidence : EvidenceUpdate Evidence
    Depends : Artifact → Artifact → Set
    changedArtifact : Artifact
    selectiveReopening : SelectiveCertificateReopening Artifact Depends changedArtifact
    fineWorldReference reductionReference portfolioReference : String
    interventionConsumerReference measurementOrFidelityReference : String
    evidenceAssimilationReference reopeningReference : String

record AdaptiveConsumerLoopBoundary : Set where
  constructor adaptiveConsumerLoopBoundary
  field
    exactCertificateMeansFutureSafeForDeclaredConsumer : Bool
    approximateCertificateMeansDecisionSafeWithinDeclaredMargin : Bool
    counterexampleRefutesCandidateForDeclaredConsumer : Bool
    deferredPortfolioMemberIsAutomaticallyRefuted : Bool
    deferredPortfolioMemberIsAutomaticallyRefutedIsFalse : deferredPortfolioMemberIsAutomaticallyRefuted ≡ false
    robustInterventionRequiresPointIdentification : Bool
    robustInterventionRequiresPointIdentificationIsFalse : robustInterventionRequiresPointIdentification ≡ false
    robustInterventionAutomaticallyHasAuthority : Bool
    robustInterventionAutomaticallyHasAuthorityIsFalse : robustInterventionAutomaticallyHasAuthority ≡ false
    evidenceUpdateRequiresEveryCertificateToReopen : Bool
    evidenceUpdateRequiresEveryCertificateToReopenIsFalse : evidenceUpdateRequiresEveryCertificateToReopen ≡ false
    dependencyAffectedCertificatesMustBeReconsidered : Bool

canonicalAdaptiveConsumerLoopBoundary : AdaptiveConsumerLoopBoundary
canonicalAdaptiveConsumerLoopBoundary =
  adaptiveConsumerLoopBoundary true true true false refl false refl false refl false refl true
