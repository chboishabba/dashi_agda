module DASHI.Core.EpistemicCompressionDeliberativeReopeningBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib
import DASHI.Core.OperationalOutcomeSelectiveReopeningBidiExact as Reopen
import DASHI.Core.BraidedRuntimeProofProvenanceBidiExact as Provenance

------------------------------------------------------------------------
-- EPISTEMIC COMPRESSION -> DELIBERATIVE / SELECTIVE REOPENING
--
-- When a collision witness shows that the current observer cannot carry the
-- consumer-relevant distinction, the response is not to relabel the old
-- observer.  The missing distinction becomes a residual that can route to an
-- ask/listen/deliberate move and, after realised failure, to selective runtime
-- reopening.  Existing provenance remains append-only.
------------------------------------------------------------------------

record CompressionResidualRouting
    {Situated Surface Outcome : Set}
    {observe : Situated → Surface}
    {target : Situated → Outcome}
    (compression : Compression.ProjectionInadequacyReceipt observe target) : Set where
  constructor compression-residual-routing
  field
    residualReference : String
    lostDistinctionReference : String
    preferredMove : Delib.ExtendedMoveKind
    preferredMoveReading : String
    requiresAddedInformation : Bool
    requiresAddedInformationIsTrue : requiresAddedInformation ≡ true
    relabellingOldSurfaceIsInsufficient : Bool
    relabellingOldSurfaceIsInsufficientIsTrue :
      relabellingOldSurfaceIsInsufficient ≡ true
    actionAuthorityStillSeparate : Bool
    actionAuthorityStillSeparateIsTrue : actionAuthorityStillSeparate ≡ true

open CompressionResidualRouting public

genericListenRouting :
  ∀ {Situated Surface Outcome : Set}
    {observe : Situated → Surface}
    {target : Situated → Outcome} →
  (compression : Compression.ProjectionInadequacyReceipt observe target) →
  CompressionResidualRouting compression
genericListenRouting compression =
  compression-residual-routing
    "consumer-relevant distinction erased by current observer"
    (Compression.lostDistinctionReference compression)
    Delib.listenMove
    "listen/ask/deliberate becomes eligible when the missing residual is held by situated participants or cannot be recovered from the old institutional observer"
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Operational failure remains selective rather than total invalidation.
------------------------------------------------------------------------

failedOutcomeDoesNotInvalidateEverything :
  Reopen.FailedOneOutcomeInvalidatesEverything → ⊥
failedOutcomeDoesNotInvalidateEverything =
  Reopen.failedOneOutcomeDoesNotInvalidateEverything

executionSuccessDoesNotCloseConsumerOutcome :
  Reopen.ExecutionSuccessClosesConsumerOutcome → ⊥
executionSuccessDoesNotCloseConsumerOutcome =
  Reopen.executionSuccessDoesNotCloseConsumerOutcome

------------------------------------------------------------------------
-- Provenance correction is append-only.
------------------------------------------------------------------------

runtimeCorrectionCannotRewritePriorProvenance :
  Provenance.RuntimeFeedbackMayRewritePriorProvenance → ⊥
runtimeCorrectionCannotRewritePriorProvenance =
  Provenance.runtimeFeedbackDoesNotRewritePriorProvenance

coarseHistoryEqualityDoesNotCreateFineHistoryEquality :
  Provenance.CoarseEventEqualityCreatesFineHistoryEquality → ⊥
coarseHistoryEqualityDoesNotCreateFineHistoryEquality =
  Provenance.coarseEventEqualityDoesNotCreateFineHistoryEquality

------------------------------------------------------------------------
-- Generic correction policy.
------------------------------------------------------------------------

record CompressionCorrectionPolicy : Set where
  constructor compression-correction-policy
  field
    collisionRequiresResidual : Bool
    collisionRequiresResidualIsTrue : collisionRequiresResidual ≡ true
    residualMayRouteToAsk : Bool
    residualMayRouteToAskIsTrue : residualMayRouteToAsk ≡ true
    residualMayRouteToListen : Bool
    residualMayRouteToListenIsTrue : residualMayRouteToListen ≡ true
    residualMayRouteToDeliberate : Bool
    residualMayRouteToDeliberateIsTrue : residualMayRouteToDeliberate ≡ true
    observerRelabellingAloneCountsAsRepair : Bool
    observerRelabellingAloneCountsAsRepairIsFalse :
      observerRelabellingAloneCountsAsRepair ≡ false
    failedRealisedOutcomeMaySelectivelyReopen : Bool
    failedRealisedOutcomeMaySelectivelyReopenIsTrue :
      failedRealisedOutcomeMaySelectivelyReopen ≡ true
    correctionRewritesPriorEvidence : Bool
    correctionRewritesPriorEvidenceIsFalse : correctionRewritesPriorEvidence ≡ false

canonicalCompressionCorrectionPolicy : CompressionCorrectionPolicy
canonicalCompressionCorrectionPolicy =
  compression-correction-policy
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ListeningAutomaticallyAuthorisesAction : Set where
data CollisionRequiresTotalHistoryReset : Set where
data NewResidualMayRewriteOldSourceProvenance : Set where

listeningDoesNotAuthoriseAction : ListeningAutomaticallyAuthorisesAction → ⊥
listeningDoesNotAuthoriseAction ()

collisionDoesNotRequireTotalReset : CollisionRequiresTotalHistoryReset → ⊥
collisionDoesNotRequireTotalReset ()

newResidualDoesNotRewriteOldProvenance : NewResidualMayRewriteOldSourceProvenance → ⊥
newResidualDoesNotRewriteOldProvenance ()
