module DASHI.Interop.SLRLegalRuntimeCapstoneRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRLegalRuntimeCapstoneExact as Capstone
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal

------------------------------------------------------------------------
-- Production parity regression for the consolidated Rust legal runtime.
------------------------------------------------------------------------

fourWayDispositionSatisfied :
  Capstone.toGoldenElementDisposition Capstone.rustSatisfied
  ≡ Legal.elementSatisfied
fourWayDispositionSatisfied = refl

fourWayDispositionUnsatisfied :
  Capstone.toGoldenElementDisposition Capstone.rustUnsatisfied
  ≡ Legal.elementUnsatisfied
fourWayDispositionUnsatisfied = refl

fourWayDispositionContested :
  Capstone.toGoldenElementDisposition Capstone.rustContested
  ≡ Legal.elementContested
fourWayDispositionContested = refl

fourWayDispositionUnresolved :
  Capstone.toGoldenElementDisposition Capstone.rustUnresolved
  ≡ Legal.elementUnresolved
fourWayDispositionUnresolved = refl

reviewedWorldContractKeepsCandidateSeparate :
  Capstone.reviewedObservationCreatesWrongType
    Capstone.canonicalReviewedWorldToWrongTypeContract
  ≡ false
reviewedWorldContractKeepsCandidateSeparate = refl

elementsDoNotEraseExceptions :
  Capstone.allElementsEraseExceptionsDefences
    Capstone.canonicalSourceRealisedEvaluatorContract
  ≡ false
elementsDoNotEraseExceptions = refl

violationDoesNotAutoCreateLiability :
  Capstone.violationCreatesLiability
    Capstone.canonicalSourceRealisedEvaluatorContract
  ≡ false
violationDoesNotAutoCreateLiability = refl

liabilityDoesNotAutoSelectRemedy :
  Capstone.liabilitySelectsRemedy
    Capstone.canonicalSourceRealisedEvaluatorContract
  ≡ false
liabilityDoesNotAutoSelectRemedy = refl

adaptiveCampaignRecomputes :
  Capstone.currentResidualsRecomputedAfterPayment
    Capstone.canonicalAdaptiveLegalCampaignContract
  ≡ true
adaptiveCampaignRecomputes = refl

adaptiveCampaignReplays :
  Capstone.restartReplaysExactCampaignHead
    Capstone.canonicalAdaptiveLegalCampaignContract
  ≡ true
adaptiveCampaignReplays = refl

m4ProjectionIdentityStable :
  (node : Capstone.SourceAddressableMatterIssueNode) →
  Capstone.sameNodeAcrossMatterIssueProjection node Capstone.issueProjection
  ≡
  Capstone.sameNodeAcrossMatterIssueProjection node Capstone.sourceProjection
m4ProjectionIdentityStable node =
  Capstone.matterIssueProjectionPreservesSemanticIdentity
    node Capstone.issueProjection Capstone.sourceProjection

mixedReplayCannotCreateTruth :
  Capstone.MixedFamilyReplayCreatesTruth → ⊥
mixedReplayCannotCreateTruth =
  Capstone.mixedFamilyReplayDoesNotCreateTruth

matterProjectionCannotCreateTruth :
  Capstone.MatterIssueProjectionCreatesCanonicalTruth → ⊥
matterProjectionCannotCreateTruth =
  Capstone.matterIssueProjectionDoesNotCreateCanonicalTruth

capabilitySurfacePinsAllFiveGates :
  Capstone.m25MixedFamilyReplayImplemented
    Capstone.canonicalLegalRuntimeCapabilityReceipt
  ≡ true
capabilitySurfacePinsAllFiveGates = refl
