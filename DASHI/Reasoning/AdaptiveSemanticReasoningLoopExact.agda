module DASHI.Reasoning.AdaptiveSemanticReasoningLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Semantic
import DASHI.Reasoning.SemanticConsumerRelativeClosureExact as Closure
import DASHI.Reasoning.SemanticLogicalSelectiveReopeningExact as Reopen

record SemanticConsumerCollision
    {Decision : Set}
    (fibre : Candidate.CandidateSemanticFibre)
    (consumer : Candidate.CandidateSemanticFragment → Decision) : Set₁ where
  constructor semanticConsumerCollision
  field
    left right : Candidate.CandidateSemanticFragment
    leftLive : Semantic.semanticCandidateFibre fibre left
    rightLive : Semantic.semanticCandidateFibre fibre right
    consumerDiffers : consumer left ≡ consumer right → ⊥
    collisionReference : String
open SemanticConsumerCollision public

record SemanticDiscriminator
    {Decision : Set}
    {fibre : Candidate.CandidateSemanticFibre}
    {consumer : Candidate.CandidateSemanticFragment → Decision}
    (collision : SemanticConsumerCollision fibre consumer) : Set₁ where
  constructor semanticDiscriminator
  field
    probe : Discriminator.ExperimentBundle Candidate.CandidateSemanticFragment
    separatesCollision : Discriminator.BundleSeparates probe (left collision) (right collision)
    sourceOrContextAuthorityReference : String
    calibrationReference : String
    probeSelectionReference : String
open SemanticDiscriminator public

data SemanticDecisionBranch
    {Decision : Set}
    (fibre : Candidate.CandidateSemanticFibre)
    (consumer : Candidate.CandidateSemanticFragment → Decision) : Set₁ where
  consumerClosed : Closure.SemanticConsumerClosure fibre consumer → SemanticDecisionBranch fibre consumer
  seekDiscriminatingSourceOrContext :
    (collision : SemanticConsumerCollision fibre consumer) →
    SemanticDiscriminator collision →
    SemanticDecisionBranch fibre consumer

record SemanticAssimilationStep
    {Decision : Set}
    (fibre : Candidate.CandidateSemanticFibre)
    (consumer : Candidate.CandidateSemanticFragment → Decision) : Set₁ where
  constructor semanticAssimilationStep
  field
    move : Semantic.SemanticResidualInformationMove fibre
    nextBranchReference : String
    pnfReopening : Dependency.ReopeningObligation Reopen.Depends Reopen.semanticResolutionCertificate Reopen.evidentialPNFCertificate
    derivationReopening : Dependency.ReopeningObligation Reopen.Depends Reopen.semanticResolutionCertificate Reopen.logicalDerivationCertificate
    coneReopening : Dependency.ReopeningObligation Reopen.Depends Reopen.semanticResolutionCertificate Reopen.implicationConeCertificate
    reauditingReference : String
open SemanticAssimilationStep public

canonicalSemanticAssimilationStep :
  ∀ {Decision}
    (fibre : Candidate.CandidateSemanticFibre)
    (consumer : Candidate.CandidateSemanticFragment → Decision) →
  Semantic.SemanticResidualInformationMove fibre →
  String → String →
  SemanticAssimilationStep fibre consumer
canonicalSemanticAssimilationStep fibre consumer move next audit =
  semanticAssimilationStep
    move next
    Reopen.semanticToPNFReopening
    Reopen.semanticChangeReopensLogicalDerivation
    Reopen.semanticChangeReopensImplicationCone
    audit

record AdaptiveSemanticReasoningBoundary : Set where
  constructor adaptiveSemanticReasoningBoundary
  field
    consumerClosureMayStopFurtherSemanticSearch : Bool
    consumerClosureMayStopFurtherSemanticSearchIsTrue : consumerClosureMayStopFurtherSemanticSearch ≡ true
    unresolvedConsumerCollisionMayRequestProbe : Bool
    unresolvedConsumerCollisionMayRequestProbeIsTrue : unresolvedConsumerCollisionMayRequestProbe ≡ true
    probeResultAutomaticallyCreatesWorldTruth : Bool
    probeResultAutomaticallyCreatesWorldTruthIsFalse : probeResultAutomaticallyCreatesWorldTruth ≡ false
    semanticUpdateReopensDependencyAffectedDownstream : Bool
    semanticUpdateReopensDependencyAffectedDownstreamIsTrue : semanticUpdateReopensDependencyAffectedDownstream ≡ true
    consumerClosureRequiresSemanticPointIdentity : Bool
    consumerClosureRequiresSemanticPointIdentityIsFalse : consumerClosureRequiresSemanticPointIdentity ≡ false

canonicalAdaptiveSemanticReasoningBoundary : AdaptiveSemanticReasoningBoundary
canonicalAdaptiveSemanticReasoningBoundary =
  adaptiveSemanticReasoningBoundary true refl true refl false refl true refl false refl
