module DASHI.Reasoning.SelectiveImplicationCertificateReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path

------------------------------------------------------------------------
-- CHANGED DERIVATION EDGE -> AFFECTED CONSEQUENCE/CONE CERTIFICATES
------------------------------------------------------------------------

data ImplicationArtifact : Set where
  parserObservationArtifact
  semanticResolutionArtifact
  evidentialPNFArtifact
  logicalDerivationArtifact
  empiricalPromotionArtifact
  residualEnvelopeArtifact
  designDischargeArtifact
  implicationEdgeCertificate
  downstreamConeCertificate
  consumerUseCertificate
  : ImplicationArtifact

record ImplicationDependencyGraph : Set₁ where
  constructor implicationDependencyGraph
  field
    Depends : ImplicationArtifact → ImplicationArtifact → Set
    dependencyReference : String

open ImplicationDependencyGraph public

record ChangedDerivationArtifact : Set where
  constructor changedDerivationArtifact
  field
    changed : ImplicationArtifact
    derivationEdgeKind : Path.DerivationEdgeKind
    changeReference : String
    sourceOrWorldReference : String

open ChangedDerivationArtifact public

record SelectiveImplicationReopening
    (graph : ImplicationDependencyGraph)
    (change : ChangedDerivationArtifact) : Set₁ where
  constructor selectiveImplicationReopening
  field
    affectedCertificate : ImplicationArtifact
    reopeningObligation :
      Dependency.ReopeningObligation
        (Depends graph)
        (changed change)
        affectedCertificate
    reopeningReference : String

open SelectiveImplicationReopening public

selectiveReopeningToAdaptiveConsumer :
  ∀ {graph change} →
  SelectiveImplicationReopening graph change →
  Adaptive.SelectiveCertificateReopening
    ImplicationArtifact
    (Depends graph)
    (changed change)
selectiveReopeningToAdaptiveConsumer reopening =
  Adaptive.selectiveCertificateReopening
    (affectedCertificate reopening)
    (Dependency.dependencyPath (reopeningObligation reopening))
    (reopeningReference reopening)

transitiveImplicationReopening :
  ∀ {graph change target} →
  (reopening : SelectiveImplicationReopening graph change) →
  Dependency.ReopeningObligation
    (Depends graph)
    (affectedCertificate reopening)
    target →
  Dependency.ReopeningObligation
    (Depends graph)
    (changed change)
    target
transitiveImplicationReopening reopening downstream =
  Dependency.obligationsCompose
    (reopeningObligation reopening)
    downstream

------------------------------------------------------------------------
-- Exact finite dependency fixture.
------------------------------------------------------------------------

data CanonicalDepends : ImplicationArtifact → ImplicationArtifact → Set where
  semanticFeedsPNF :
    CanonicalDepends semanticResolutionArtifact evidentialPNFArtifact
  pnfFeedsLogicalDerivation :
    CanonicalDepends evidentialPNFArtifact logicalDerivationArtifact
  logicalFeedsEmpiricalPromotion :
    CanonicalDepends logicalDerivationArtifact empiricalPromotionArtifact
  promotionFeedsResidualEnvelope :
    CanonicalDepends empiricalPromotionArtifact residualEnvelopeArtifact
  residualFeedsEdgeCertificate :
    CanonicalDepends residualEnvelopeArtifact implicationEdgeCertificate
  designFeedsEdgeCertificate :
    CanonicalDepends designDischargeArtifact implicationEdgeCertificate
  edgeFeedsConeCertificate :
    CanonicalDepends implicationEdgeCertificate downstreamConeCertificate
  coneFeedsConsumerUse :
    CanonicalDepends downstreamConeCertificate consumerUseCertificate

canonicalDependencyGraph : ImplicationDependencyGraph
canonicalDependencyGraph = implicationDependencyGraph
  CanonicalDepends
  "semantic -> PNF -> logical -> empirical/residual -> edge -> cone -> consumer reverse dependency graph"

semanticChange : ChangedDerivationArtifact
semanticChange = changedDerivationArtifact
  semanticResolutionArtifact
  Path.semanticResolutionEdge
  "semantic resolution changed after new source/world evidence"
  "changed semantic candidate correspondence"

semanticToEdgeClosure :
  Dependency.AffectedClosure
    CanonicalDepends
    semanticResolutionArtifact
    implicationEdgeCertificate
semanticToEdgeClosure =
  Dependency.affectedStep semanticFeedsPNF
    (Dependency.affectedStep pnfFeedsLogicalDerivation
      (Dependency.affectedStep logicalFeedsEmpiricalPromotion
        (Dependency.affectedStep promotionFeedsResidualEnvelope
          (Dependency.affectedStep residualFeedsEdgeCertificate
            Dependency.affectedRefl))))

semanticChangeReopensEdge :
  SelectiveImplicationReopening canonicalDependencyGraph semanticChange
semanticChangeReopensEdge = selectiveImplicationReopening
  implicationEdgeCertificate
  (Dependency.reopeningObligation semanticToEdgeClosure)
  "recheck implication-edge certificate because semantic change reaches it transitively"

edgeToConeObligation :
  Dependency.ReopeningObligation
    CanonicalDepends
    implicationEdgeCertificate
    downstreamConeCertificate
edgeToConeObligation =
  Dependency.oneEdgeCreatesReopeningObligation edgeFeedsConeCertificate

semanticChangeReopensConeTransitively :
  Dependency.ReopeningObligation
    CanonicalDepends
    semanticResolutionArtifact
    downstreamConeCertificate
semanticChangeReopensConeTransitively =
  transitiveImplicationReopening
    semanticChangeReopensEdge
    edgeToConeObligation

coneToConsumerObligation :
  Dependency.ReopeningObligation
    CanonicalDepends
    downstreamConeCertificate
    consumerUseCertificate
coneToConsumerObligation =
  Dependency.oneEdgeCreatesReopeningObligation coneFeedsConsumerUse

semanticChangeReopensConsumerUseTransitively :
  Dependency.ReopeningObligation
    CanonicalDepends
    semanticResolutionArtifact
    consumerUseCertificate
semanticChangeReopensConsumerUseTransitively =
  Dependency.obligationsCompose
    semanticChangeReopensConeTransitively
    coneToConsumerObligation

------------------------------------------------------------------------
-- Staleness is reopening, not automatic refutation or global invalidation.
------------------------------------------------------------------------

data CertificateStatus : Set where
  currentCertificate reopenableCertificate refutedCertificate : CertificateStatus

reopenedNotRefuted : reopenableCertificate ≡ refutedCertificate → ⊥
reopenedNotRefuted ()

record SelectiveImplicationReopeningBoundary : Set where
  constructor selectiveImplicationReopeningBoundary
  field
    changedSemanticEdgeCanReopenDownstreamConeTransitively : Bool
    changedSemanticEdgeCanReopenDownstreamConeTransitivelyIsTrue :
      changedSemanticEdgeCanReopenDownstreamConeTransitively ≡ true
    staleCertificateEqualsRefutedClaim : Bool
    staleCertificateEqualsRefutedClaimIsFalse :
      staleCertificateEqualsRefutedClaim ≡ false
    everyConeCertificateReopensAfterAnyEvidenceChange : Bool
    everyConeCertificateReopensAfterAnyEvidenceChangeIsFalse :
      everyConeCertificateReopensAfterAnyEvidenceChange ≡ false
    selectiveReopeningCanFeedAdaptiveConsumerLoop : Bool
    selectiveReopeningCanFeedAdaptiveConsumerLoopIsTrue :
      selectiveReopeningCanFeedAdaptiveConsumerLoop ≡ true

canonicalSelectiveImplicationReopeningBoundary :
  SelectiveImplicationReopeningBoundary
canonicalSelectiveImplicationReopeningBoundary =
  selectiveImplicationReopeningBoundary
    true refl false refl false refl true refl
