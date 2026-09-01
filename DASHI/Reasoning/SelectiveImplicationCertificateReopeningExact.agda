module DASHI.Reasoning.SelectiveImplicationCertificateReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path
import DASHI.Reasoning.SemanticLogicalSelectiveReopeningExact as Canonical

------------------------------------------------------------------------
-- CHANGED DERIVATION EDGE -> AFFECTED CONSEQUENCE/CONE CERTIFICATES
--
-- The inner semantic -> PNF -> logical -> cone reopening remains owned by the
-- canonical SemanticLogicalSelectiveReopeningExact module.  This owner extends
-- that calculus with typed derivation-edge change receipts, residual/edge
-- certificates, downstream cone consumers, and the AdaptiveConsumerModelLoop
-- handoff.
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
-- Exact extended dependency fixture.
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
  "extends canonical semantic/logical reopening with empirical residual, edge, cone and consumer certificates"

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
-- Canonical-inner / extended-outer weld.
------------------------------------------------------------------------

record CanonicalExtendedReopeningReceipt : Set where
  constructor canonicalExtendedReopeningReceipt
  field
    canonicalReasoningConeReopening :
      Dependency.ReopeningObligation
        Canonical.Depends
        Canonical.semanticResolutionCertificate
        Canonical.implicationConeCertificate
    extendedConeReopening :
      Dependency.ReopeningObligation
        CanonicalDepends
        semanticResolutionArtifact
        downstreamConeCertificate
    extendedConsumerReopening :
      Dependency.ReopeningObligation
        CanonicalDepends
        semanticResolutionArtifact
        consumerUseCertificate
    weldReference : String

open CanonicalExtendedReopeningReceipt public

canonicalExtendedReopening : CanonicalExtendedReopeningReceipt
canonicalExtendedReopening = canonicalExtendedReopeningReceipt
  Canonical.semanticChangeReopensImplicationCone
  semanticChangeReopensConeTransitively
  semanticChangeReopensConsumerUseTransitively
  "canonical semantic/logical reopening retained; extended layer adds residual/edge/consumer reachability"

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
    canonicalSemanticLogicalReopeningIsReused : Bool
    canonicalSemanticLogicalReopeningIsReusedIsTrue :
      canonicalSemanticLogicalReopeningIsReused ≡ true
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
    true refl true refl false refl false refl true refl
