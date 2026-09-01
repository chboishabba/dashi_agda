module DASHI.Reasoning.Spacy369MultiConsumerCoverageSelectiveReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Reasoning.Spacy369MultiConsumerSharedProbeExact as Shared
import DASHI.Reasoning.Spacy369MultiConsumerCoverageFiltrationExact as Filtration

------------------------------------------------------------------------
-- LEAST-PRIVILEGE REOPENING FOR THE MULTI-CONSUMER COVERAGE FILTRATION.
--
-- Shared context supports subject-position and governed-standing consumers.
-- Closure-residual information is independent.  A change therefore propagates
-- only through the dependency paths that actually consume that coordinate.
------------------------------------------------------------------------

data CoverageArtifact : Set where
  sharedContextCoordinate
  closureResidualCoordinate
  subjectCertificate
  standingCertificate
  closureCertificate
  operationalCertificate
  parserEvidenceArtifact
  logicalEntailmentArtifact
  : CoverageArtifact

data Depends : CoverageArtifact → CoverageArtifact → Set where
  sharedFeedsSubject : Depends sharedContextCoordinate subjectCertificate
  sharedFeedsStanding : Depends sharedContextCoordinate standingCertificate
  closureFeedsClosure : Depends closureResidualCoordinate closureCertificate

sharedContextReopensSubject :
  Affected.ReopeningObligation
    Depends sharedContextCoordinate subjectCertificate
sharedContextReopensSubject =
  Affected.oneEdgeCreatesReopeningObligation sharedFeedsSubject

sharedContextReopensStanding :
  Affected.ReopeningObligation
    Depends sharedContextCoordinate standingCertificate
sharedContextReopensStanding =
  Affected.oneEdgeCreatesReopeningObligation sharedFeedsStanding

closureResidualReopensClosureOnly :
  Affected.ReopeningObligation
    Depends closureResidualCoordinate closureCertificate
closureResidualReopensClosureOnly =
  Affected.oneEdgeCreatesReopeningObligation closureFeedsClosure

------------------------------------------------------------------------
-- No-direct-dependency results.  These are exact consequences of the sparse
-- dependency graph, not claims that future repository extensions can never add
-- an explicit dependency.
------------------------------------------------------------------------

closureResidualDoesNotDirectlyReopenSubject :
  Depends closureResidualCoordinate subjectCertificate → ⊥
closureResidualDoesNotDirectlyReopenSubject ()

closureResidualDoesNotDirectlyReopenStanding :
  Depends closureResidualCoordinate standingCertificate → ⊥
closureResidualDoesNotDirectlyReopenStanding ()

sharedContextDoesNotDirectlyReopenClosure :
  Depends sharedContextCoordinate closureCertificate → ⊥
sharedContextDoesNotDirectlyReopenClosure ()

sharedContextDoesNotDirectlyRewriteParser :
  Depends sharedContextCoordinate parserEvidenceArtifact → ⊥
sharedContextDoesNotDirectlyRewriteParser ()

closureResidualDoesNotDirectlyRewriteParser :
  Depends closureResidualCoordinate parserEvidenceArtifact → ⊥
closureResidualDoesNotDirectlyRewriteParser ()

coverageAuditDoesNotDirectlyRewriteOrdinaryLogic :
  (changed : CoverageArtifact) →
  (changed ≡ sharedContextCoordinate ⊎ changed ≡ closureResidualCoordinate) →
  Depends changed logicalEntailmentArtifact → ⊥
coverageAuditDoesNotDirectlyRewriteOrdinaryLogic .sharedContextCoordinate (inj₁ refl) ()
coverageAuditDoesNotDirectlyRewriteOrdinaryLogic .closureResidualCoordinate (inj₂ refl) ()

------------------------------------------------------------------------
-- Anchors: the reason these dependencies exist is supplied by the actual shared
-- probe closure receipts and the filtration's independent closure-residual gap.
------------------------------------------------------------------------

subjectCoverageReceipt = Shared.sharedProbeClosesSubjectConsumer
standingCoverageReceipt = Shared.sharedProbeClosesStandingConsumer
closureResidualGap = Shared.sharedProbeDoesNotCloseClosureConsumer
subjectFirstClosureDepth = Filtration.subjectFirstAt1
standingFirstClosureDepth = Filtration.standingFirstAt1
closureFirstClosureDepth = Filtration.closureResidualFirstAt2

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Spacy369MultiConsumerCoverageSelectiveReopeningBoundary : Set where
  constructor spacy369MultiConsumerCoverageSelectiveReopeningBoundary
  field
    oneSharedCoordinateMayReopenSeveralDependentConsumers : Bool
    oneSharedCoordinateMayReopenSeveralDependentConsumersIsTrue :
      oneSharedCoordinateMayReopenSeveralDependentConsumers ≡ true
    closureResidualChangeAutomaticallyReopensSubjectConsumer : Bool
    closureResidualChangeAutomaticallyReopensSubjectConsumerIsFalse :
      closureResidualChangeAutomaticallyReopensSubjectConsumer ≡ false
    sharedContextChangeAutomaticallyReopensClosureResidualConsumer : Bool
    sharedContextChangeAutomaticallyReopensClosureResidualConsumerIsFalse :
      sharedContextChangeAutomaticallyReopensClosureResidualConsumer ≡ false
    auditCoordinateChangeRewritesOriginalParserEvidence : Bool
    auditCoordinateChangeRewritesOriginalParserEvidenceIsFalse :
      auditCoordinateChangeRewritesOriginalParserEvidence ≡ false
    auditCoordinateChangeInvalidatesOrdinaryLogicalEntailment : Bool
    auditCoordinateChangeInvalidatesOrdinaryLogicalEntailmentIsFalse :
      auditCoordinateChangeInvalidatesOrdinaryLogicalEntailment ≡ false
    reopeningMeansPreviouslyClosedCertificateWasFalse : Bool
    reopeningMeansPreviouslyClosedCertificateWasFalseIsFalse :
      reopeningMeansPreviouslyClosedCertificateWasFalse ≡ false

canonicalSpacy369MultiConsumerCoverageSelectiveReopeningBoundary :
  Spacy369MultiConsumerCoverageSelectiveReopeningBoundary
canonicalSpacy369MultiConsumerCoverageSelectiveReopeningBoundary =
  spacy369MultiConsumerCoverageSelectiveReopeningBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
