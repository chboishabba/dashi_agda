module DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN PAPER / RECEPTION-EVIDENCE SELECTIVE REOPENING
--
-- Authorial source attribution:
--   John Anthony Brown
--
-- This owner relates the merged John Anthony Brown H1-H5 paper manifest back to
-- the new reception-history dependency/reopening calculus.  New source or
-- instrument evidence reopens only the declared downstream claims that consume
-- it; it does not invalidate the entire paper, nor does a stale claim become
-- automatically refuted.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest
import DASHI.Governance.ReceptionEvidenceSelectiveReopeningExact as Reception

paperAuthor : String
paperAuthor = "John Anthony Brown"

------------------------------------------------------------------------
-- 1. Paper-specific audit artifacts.
------------------------------------------------------------------------

data BrownAuditArtifact : Set where
  conceptualReceptionEdge
  autonomyConceptDefinition
  exposureMeasurementEvidence
  outcomeMeasurementEvidence
  institutionalBetrayalMeasurementEvidence
  moderationMeasurementEvidence
  confoundingModelEvidence
  h1AssociationClaim
  h2OutcomeVectorClaim
  h3IncrementalBetrayalClaim
  h4ModerationClaim
  h5AdjustedAssociationClaim
  rightsPolicyInterpretation
  manuscriptRevisionSurface
  : BrownAuditArtifact

------------------------------------------------------------------------
-- 2. Declared dependency graph.
--
-- These are audit dependencies, not empirical causal claims.
------------------------------------------------------------------------

data BrownDepends : BrownAuditArtifact → BrownAuditArtifact → Set where
  receptionToAutonomyDefinition :
    BrownDepends conceptualReceptionEdge autonomyConceptDefinition
  autonomyDefinitionToH2 :
    BrownDepends autonomyConceptDefinition h2OutcomeVectorClaim

  exposureToH1 : BrownDepends exposureMeasurementEvidence h1AssociationClaim
  outcomeToH1 : BrownDepends outcomeMeasurementEvidence h1AssociationClaim

  exposureToH2 : BrownDepends exposureMeasurementEvidence h2OutcomeVectorClaim
  outcomeToH2 : BrownDepends outcomeMeasurementEvidence h2OutcomeVectorClaim

  betrayalMeasureToH3 :
    BrownDepends institutionalBetrayalMeasurementEvidence h3IncrementalBetrayalClaim
  exposureToH3 : BrownDepends exposureMeasurementEvidence h3IncrementalBetrayalClaim
  confoundingToH3 : BrownDepends confoundingModelEvidence h3IncrementalBetrayalClaim

  moderationMeasureToH4 :
    BrownDepends moderationMeasurementEvidence h4ModerationClaim
  exposureToH4 : BrownDepends exposureMeasurementEvidence h4ModerationClaim
  outcomeToH4 : BrownDepends outcomeMeasurementEvidence h4ModerationClaim

  exposureToH5 : BrownDepends exposureMeasurementEvidence h5AdjustedAssociationClaim
  outcomeToH5 : BrownDepends outcomeMeasurementEvidence h5AdjustedAssociationClaim
  confoundingToH5 : BrownDepends confoundingModelEvidence h5AdjustedAssociationClaim

  h1ToRightsPolicy : BrownDepends h1AssociationClaim rightsPolicyInterpretation
  h2ToRightsPolicy : BrownDepends h2OutcomeVectorClaim rightsPolicyInterpretation
  h3ToRightsPolicy : BrownDepends h3IncrementalBetrayalClaim rightsPolicyInterpretation
  h4ToRightsPolicy : BrownDepends h4ModerationClaim rightsPolicyInterpretation
  h5ToRightsPolicy : BrownDepends h5AdjustedAssociationClaim rightsPolicyInterpretation

  h1ToRevision : BrownDepends h1AssociationClaim manuscriptRevisionSurface
  h2ToRevision : BrownDepends h2OutcomeVectorClaim manuscriptRevisionSurface
  h3ToRevision : BrownDepends h3IncrementalBetrayalClaim manuscriptRevisionSurface
  h4ToRevision : BrownDepends h4ModerationClaim manuscriptRevisionSurface
  h5ToRevision : BrownDepends h5AdjustedAssociationClaim manuscriptRevisionSurface
  policyToRevision : BrownDepends rightsPolicyInterpretation manuscriptRevisionSurface

------------------------------------------------------------------------
-- 3. The merged H1-H5 manifest is the consumer surface.
------------------------------------------------------------------------

h1StillH1 : Manifest.key Manifest.h1Manifest ≡ Manifest.H1
h1StillH1 = refl

h2StillH2 : Manifest.key Manifest.h2Manifest ≡ Manifest.H2
h2StillH2 = refl

h3StillH3 : Manifest.key Manifest.h3Manifest ≡ Manifest.H3
h3StillH3 = refl

h4StillH4 : Manifest.key Manifest.h4Manifest ≡ Manifest.H4
h4StillH4 = refl

h5StillH5 : Manifest.key Manifest.h5Manifest ≡ Manifest.H5
h5StillH5 = refl

------------------------------------------------------------------------
-- 4. Selective paper reopenings.
------------------------------------------------------------------------

receptionChangeReopensH2Interpretation :
  Dependency.ReopeningObligation
    BrownDepends conceptualReceptionEdge h2OutcomeVectorClaim
receptionChangeReopensH2Interpretation =
  Dependency.reopeningObligation
    (Dependency.affectedStep receptionToAutonomyDefinition
      (Dependency.affectedStep autonomyDefinitionToH2 Dependency.affectedRefl))

receptionChangeReopensRightsPolicyTransitively :
  Dependency.ReopeningObligation
    BrownDepends conceptualReceptionEdge rightsPolicyInterpretation
receptionChangeReopensRightsPolicyTransitively =
  Dependency.obligationsCompose
    receptionChangeReopensH2Interpretation
    (Dependency.oneEdgeCreatesReopeningObligation h2ToRightsPolicy)

betrayalMeasureChangeReopensH3 :
  Dependency.ReopeningObligation
    BrownDepends institutionalBetrayalMeasurementEvidence h3IncrementalBetrayalClaim
betrayalMeasureChangeReopensH3 =
  Dependency.oneEdgeCreatesReopeningObligation betrayalMeasureToH3

betrayalMeasureChangeReopensPolicyTransitively :
  Dependency.ReopeningObligation
    BrownDepends institutionalBetrayalMeasurementEvidence rightsPolicyInterpretation
betrayalMeasureChangeReopensPolicyTransitively =
  Dependency.obligationsCompose
    betrayalMeasureChangeReopensH3
    (Dependency.oneEdgeCreatesReopeningObligation h3ToRightsPolicy)

exposureMeasureChangeReopensH1 :
  Dependency.ReopeningObligation
    BrownDepends exposureMeasurementEvidence h1AssociationClaim
exposureMeasureChangeReopensH1 =
  Dependency.oneEdgeCreatesReopeningObligation exposureToH1

exposureMeasureChangeReopensH5 :
  Dependency.ReopeningObligation
    BrownDepends exposureMeasurementEvidence h5AdjustedAssociationClaim
exposureMeasureChangeReopensH5 =
  Dependency.oneEdgeCreatesReopeningObligation exposureToH5

confoundingChangeReopensH5 :
  Dependency.ReopeningObligation
    BrownDepends confoundingModelEvidence h5AdjustedAssociationClaim
confoundingChangeReopensH5 =
  Dependency.oneEdgeCreatesReopeningObligation confoundingToH5

moderationMeasureChangeReopensH4 :
  Dependency.ReopeningObligation
    BrownDepends moderationMeasurementEvidence h4ModerationClaim
moderationMeasureChangeReopensH4 =
  Dependency.oneEdgeCreatesReopeningObligation moderationMeasureToH4

------------------------------------------------------------------------
-- 5. Earlier-thread BIDI return rule.
--
-- The paper-side result of a source change is revise/requalify/retest the
-- affected claim.  It is not "delete the paper" and not "the stale claim is
-- false".  Likewise, a conceptual reception-history change need not reopen an
-- unrelated quantitative claim unless an explicit dependency path is installed.
------------------------------------------------------------------------

data OneChangedSourceInvalidatesWholePaper : Set where
data StaleBrownClaimIsRefuted : Set where
data ReceptionLineageChangeAutomaticallyChangesEveryEffectEstimate : Set where

data ExternalSourceAuthorshipTransfersToJohnBrown : Set where

data JohnBrownAuthorshipTransfersToExternalSource : Set where

oneChangedSourceDoesNotInvalidateWholePaper :
  OneChangedSourceInvalidatesWholePaper → ⊥
oneChangedSourceDoesNotInvalidateWholePaper ()

staleBrownClaimIsReopenableNotRefuted : StaleBrownClaimIsRefuted → ⊥
staleBrownClaimIsReopenableNotRefuted ()

receptionLineageChangeDoesNotAutomaticallyChangeEveryEffectEstimate :
  ReceptionLineageChangeAutomaticallyChangesEveryEffectEstimate → ⊥
receptionLineageChangeDoesNotAutomaticallyChangeEveryEffectEstimate ()

externalSourceAuthorshipDoesNotTransferToJohnBrown :
  ExternalSourceAuthorshipTransfersToJohnBrown → ⊥
externalSourceAuthorshipDoesNotTransferToJohnBrown ()

johnBrownAuthorshipDoesNotTransferToExternalSources :
  JohnBrownAuthorshipTransfersToExternalSource → ⊥
johnBrownAuthorshipDoesNotTransferToExternalSources ()

------------------------------------------------------------------------
-- 6. Explicit cross-pollination with the generic reception reopening boundary.
------------------------------------------------------------------------

genericReceptionReopeningIsSelective :
  Reception.allHistoricalClaimsReopenAfterEverySourceChange
    Reception.canonicalReceptionSelectiveReopeningBoundary
  ≡ false
genericReceptionReopeningIsSelective = refl

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

record JohnBrownSelectiveReopeningBoundary : Set where
  constructor john-brown-selective-reopening-boundary
  field
    authorAttributedToJohnAnthonyBrown : Bool
    H1ToH5RemainDistinctConsumers : Bool
    changedEvidenceReopensDeclaredDependents : Bool
    conceptualReceptionChangeMayReopenH2Wording : Bool
    conceptualReceptionChangeAutomaticallyRewritesAllQuantitativeResults : Bool
    staleClaimEqualsRefutation : Bool
    wholePaperReopensAfterEveryEvidenceChange : Bool
    rightsPolicyClaimsRemainDownstream : Bool
    externalSourceAndPaperAuthorshipRemainDistinct : Bool

canonicalJohnBrownSelectiveReopeningBoundary : JohnBrownSelectiveReopeningBoundary
canonicalJohnBrownSelectiveReopeningBoundary =
  john-brown-selective-reopening-boundary
    true true true true false false false true true
