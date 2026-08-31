module DASHI.Reasoning.AristotleSelectiveImplicationReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.SelectiveImplicationCertificateReopeningExact as Reopen
import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Reasoning.AristotleResidualInformationSearchExact as ResidualSearch

------------------------------------------------------------------------
-- IMPLICATION CONE REOPENING -> ARISTOTLE SEARCH-POLICY REOPENING
--
-- This is a DASHI orchestration bridge.  It does not alter Aristotle's AND/OR
-- proof semantics.  A changed implication/cone dependency may make a residual
-- search-policy certificate stale; that is a reopening obligation, not a proof
-- refutation and not a new proof.
------------------------------------------------------------------------

data CrossArtifact : Set where
  implicationArtifact : Reopen.ImplicationArtifact → CrossArtifact
  aristotleSearchPolicyCertificate
  aristotleActionCertificate
  : CrossArtifact

data CrossDepends : CrossArtifact → CrossArtifact → Set where
  liftImplicationDependency :
    ∀ {source target} →
    Reopen.CanonicalDepends source target →
    CrossDepends
      (implicationArtifact source)
      (implicationArtifact target)
  coneFeedsAristotleSearchPolicy :
    CrossDepends
      (implicationArtifact Reopen.downstreamConeCertificate)
      aristotleSearchPolicyCertificate
  searchPolicyFeedsAristotleAction :
    CrossDepends
      aristotleSearchPolicyCertificate
      aristotleActionCertificate

semanticChangeToConeCrossClosure :
  Dependency.AffectedClosure
    CrossDepends
    (implicationArtifact Reopen.semanticResolutionArtifact)
    (implicationArtifact Reopen.downstreamConeCertificate)
semanticChangeToConeCrossClosure =
  Dependency.affectedStep
    (liftImplicationDependency Reopen.semanticFeedsPNF)
    (Dependency.affectedStep
      (liftImplicationDependency Reopen.pnfFeedsLogicalDerivation)
      (Dependency.affectedStep
        (liftImplicationDependency Reopen.logicalFeedsEmpiricalPromotion)
        (Dependency.affectedStep
          (liftImplicationDependency Reopen.promotionFeedsResidualEnvelope)
          (Dependency.affectedStep
            (liftImplicationDependency Reopen.residualFeedsEdgeCertificate)
            (Dependency.affectedStep
              (liftImplicationDependency Reopen.edgeFeedsConeCertificate)
              Dependency.affectedRefl)))))

semanticChangeReopensAristotleSearchPolicy :
  Dependency.ReopeningObligation
    CrossDepends
    (implicationArtifact Reopen.semanticResolutionArtifact)
    aristotleSearchPolicyCertificate
semanticChangeReopensAristotleSearchPolicy =
  Dependency.reopeningObligation
    (Dependency.appendAffected
      semanticChangeToConeCrossClosure
      (Dependency.affectedStep coneFeedsAristotleSearchPolicy Dependency.affectedRefl))

semanticChangeReopensAristotleActionTransitively :
  Dependency.ReopeningObligation
    CrossDepends
    (implicationArtifact Reopen.semanticResolutionArtifact)
    aristotleActionCertificate
semanticChangeReopensAristotleActionTransitively =
  Dependency.obligationsCompose
    semanticChangeReopensAristotleSearchPolicy
    (Dependency.oneEdgeCreatesReopeningObligation searchPolicyFeedsAristotleAction)

record AristotleReopenedResidualAction
    {G : Aristotle.SearchHypergraph}
    (candidate : ResidualSearch.AristotleResidualAction G) : Set₁ where
  constructor aristotleReopenedResidualAction
  field
    reopening :
      Dependency.ReopeningObligation
        CrossDepends
        (implicationArtifact Reopen.semanticResolutionArtifact)
        aristotleActionCertificate
    changedConeReference : String
    affectedPolicyReference : String
    actionDependencyReference : String
    resumeSearchReference : String

open AristotleReopenedResidualAction public

data ReopenedProofSearchStatus : Set where
  actionCurrent
  actionReopenable
  actionRefuted
  actionProved
  : ReopenedProofSearchStatus

reopenableNotRefuted : actionReopenable ≡ actionRefuted → ⊥
reopenableNotRefuted ()

reopenableNotProved : actionReopenable ≡ actionProved → ⊥
reopenableNotProved ()

record AristotleSelectiveReopeningBoundary : Set where
  constructor aristotleSelectiveReopeningBoundary
  field
    semanticChangeCanReachAffectedAristotleActionTransitively : Bool
    semanticChangeCanReachAffectedAristotleActionTransitivelyIsTrue :
      semanticChangeCanReachAffectedAristotleActionTransitively ≡ true
    reopenedActionIsAutomaticallyRefuted : Bool
    reopenedActionIsAutomaticallyRefutedIsFalse :
      reopenedActionIsAutomaticallyRefuted ≡ false
    reopenedActionIsAutomaticallyProved : Bool
    reopenedActionIsAutomaticallyProvedIsFalse :
      reopenedActionIsAutomaticallyProved ≡ false
    unrelatedAristotleActionsNeedReopenWithoutDependencyPath : Bool
    unrelatedAristotleActionsNeedReopenWithoutDependencyPathIsFalse :
      unrelatedAristotleActionsNeedReopenWithoutDependencyPath ≡ false
    bridgeChangesAristotleANDORSemantics : Bool
    bridgeChangesAristotleANDORSemanticsIsFalse :
      bridgeChangesAristotleANDORSemantics ≡ false

canonicalAristotleSelectiveReopeningBoundary :
  AristotleSelectiveReopeningBoundary
canonicalAristotleSelectiveReopeningBoundary =
  aristotleSelectiveReopeningBoundary
    true refl false refl false refl false refl false refl
