module DASHI.Cognition.PNF.SensibLawMatterAcceptanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMatterWorkspaceProjectionExact as Matter
import DASHI.Cognition.PNF.SensibLawMinimalMatterHandoffExact as Handoff

------------------------------------------------------------------------
-- M13 historical Mary/SensibLaw acceptance boundary.
--
-- This owner does NOT add a new semantic ontology.  It formalises product
-- acceptance distinctions over the already-landed Matter workspace.
------------------------------------------------------------------------

data MatterAcceptanceSemanticRole : Set where
  partyAssertion proceduralOutcome laterAnnotation :
    MatterAcceptanceSemanticRole

record MatterAcceptanceRoleCoordinate : Set where
  constructor matter-acceptance-role-coordinate
  field
    semanticRef : String
    role : MatterAcceptanceSemanticRole
    reviewRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open MatterAcceptanceRoleCoordinate public

data ChronologyAcceptanceDiagnosticKind : Set where
  missingDate undated unknownDate missingActor contradictoryChronology :
    ChronologyAcceptanceDiagnosticKind
  noEventMaterial proceduralSignificanceOpen :
    ChronologyAcceptanceDiagnosticKind

record MatterAcceptanceDiagnostic : Set where
  constructor matter-acceptance-diagnostic
  field
    diagnosticRef : String
    semanticRef : String
    kind : ChronologyAcceptanceDiagnosticKind
    sourceOrReviewRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsNegativeFinding : Bool
    createsNegativeFindingIsFalse :
      createsNegativeFinding ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open MatterAcceptanceDiagnostic public

------------------------------------------------------------------------
-- Executable product-receipt shape.
--
-- Counts/refs are populated by runtime readers over a persisted Matter.
------------------------------------------------------------------------

record MatterAcceptanceReceipt : Set where
  constructor matter-acceptance-receipt
  field
    matterRef : String

    sourceReopenableRefs : List String
    eventRefs : List String
    claimRefs : List String

    missingDateEventRefs : List String
    missingActorClaimRefs : List String
    contradictoryRelationRefs : List String
    noEventRefs : List String

    partyAssertionRefs : List String
    proceduralOutcomeRefs : List String
    laterAnnotationRefs : List String
    proceduralSignificanceReviewRefs : List String

    operationalCarryoverRefs : List String
    contextExclusionRefs : List String
    handoffPreviewRefs : List String

    sourceEventCrossNavigationAvailable : Bool
    sourceEventCrossNavigationAvailableIsTrue :
      sourceEventCrossNavigationAvailable ≡ true

    datedApproximateRelativeUndatedUnknownPreserved : Bool
    datedApproximateRelativeUndatedUnknownPreservedIsTrue :
      datedApproximateRelativeUndatedUnknownPreserved ≡ true

    automaticJoinStillRequiresReview : Bool
    automaticJoinStillRequiresReviewIsTrue :
      automaticJoinStillRequiresReview ≡ true

    operationalUnresolvedDistinctFromReviewSemanticPriority : Bool
    operationalUnresolvedDistinctFromReviewSemanticPriorityIsTrue :
      operationalUnresolvedDistinctFromReviewSemanticPriority ≡ true

    contextProjectionRetained : Bool
    contextProjectionRetainedIsTrue :
      contextProjectionRetained ≡ true

    handoffPreviewDoesNotMutateMatter : Bool
    handoffPreviewDoesNotMutateMatterIsTrue :
      handoffPreviewDoesNotMutateMatter ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

    canonicalWorldMutated : Bool
    canonicalWorldMutatedIsFalse :
      canonicalWorldMutated ≡ false

open MatterAcceptanceReceipt public

canonicalMatterAcceptanceReceiptShape : MatterAcceptanceReceipt
canonicalMatterAcceptanceReceiptShape =
  matter-acceptance-receipt
    "matter:acceptance-example"
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Historical acceptance distinctions.
------------------------------------------------------------------------

record MaryAcceptanceBoundary : Set where
  constructor mary-acceptance-boundary
  field
    missingDateMayRemainUnresolved : Bool
    missingDateMayRemainUnresolvedIsTrue :
      missingDateMayRemainUnresolved ≡ true

    missingActorMayRemainUnresolved : Bool
    missingActorMayRemainUnresolvedIsTrue :
      missingActorMayRemainUnresolved ≡ true

    contradictoryChronologyMayRemainVisible : Bool
    contradictoryChronologyMayRemainVisibleIsTrue :
      contradictoryChronologyMayRemainVisible ≡ true

    noEventMaterialMayRemainInMatter : Bool
    noEventMaterialMayRemainInMatterIsTrue :
      noEventMaterialMayRemainInMatter ≡ true

    partyAssertionDistinctFromProceduralOutcome : Bool
    partyAssertionDistinctFromProceduralOutcomeIsTrue :
      partyAssertionDistinctFromProceduralOutcome ≡ true

    proceduralOutcomeDistinctFromLaterAnnotation : Bool
    proceduralOutcomeDistinctFromLaterAnnotationIsTrue :
      proceduralOutcomeDistinctFromLaterAnnotation ≡ true

    partyAssertionDistinctFromLaterAnnotation : Bool
    partyAssertionDistinctFromLaterAnnotationIsTrue :
      partyAssertionDistinctFromLaterAnnotation ≡ true

canonicalMaryAcceptanceBoundary : MaryAcceptanceBoundary
canonicalMaryAcceptanceBoundary =
  mary-acceptance-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MissingDateMeansEventDidNotHappen : Set where
data MissingActorMeansUnknownPerson : Set where
data NoEventMeansFalse : Set where
data PartyAssertionIsProceduralOutcome : Set where
data ProceduralOutcomeIsLaterAnnotation : Set where
data PartyAssertionIsLaterAnnotation : Set where
data ContradictionForcesMergedNarrative : Set where
data AcceptanceRoleCreatesTruth : Set where
data AcceptanceDiagnosticCreatesNegativeFinding : Set where
data AcceptanceReceiptMutatesMatter : Set where

missingDateDoesNotMeanEventDidNotHappen :
  MissingDateMeansEventDidNotHappen → ⊥
missingDateDoesNotMeanEventDidNotHappen ()

missingActorDoesNotMeanUnknownPerson :
  MissingActorMeansUnknownPerson → ⊥
missingActorDoesNotMeanUnknownPerson ()

noEventDoesNotMeanFalse : NoEventMeansFalse → ⊥
noEventDoesNotMeanFalse ()

partyAssertionIsNotProceduralOutcome :
  PartyAssertionIsProceduralOutcome → ⊥
partyAssertionIsNotProceduralOutcome ()

proceduralOutcomeIsNotLaterAnnotation :
  ProceduralOutcomeIsLaterAnnotation → ⊥
proceduralOutcomeIsNotLaterAnnotation ()

partyAssertionIsNotLaterAnnotation :
  PartyAssertionIsLaterAnnotation → ⊥
partyAssertionIsNotLaterAnnotation ()

contradictionDoesNotForceMergedNarrative :
  ContradictionForcesMergedNarrative → ⊥
contradictionDoesNotForceMergedNarrative ()

acceptanceRoleDoesNotCreateTruth :
  AcceptanceRoleCreatesTruth → ⊥
acceptanceRoleDoesNotCreateTruth ()

acceptanceDiagnosticDoesNotCreateNegativeFinding :
  AcceptanceDiagnosticCreatesNegativeFinding → ⊥
acceptanceDiagnosticDoesNotCreateNegativeFinding ()

acceptanceReceiptDoesNotMutateMatter :
  AcceptanceReceiptMutatesMatter → ⊥
acceptanceReceiptDoesNotMutateMatter ()
