module DASHI.Culture.ChildReligiousHistoryQualifiedReopeningExact where

------------------------------------------------------------------------
-- CHILD RELIGIOUS FORMATION: HISTORY-QUALIFIED / ADMISSIBLE REOPENING
--
-- This owner cross-pollinates John Anthony Brown's child-formation/autonomy
-- lane with TWO already-merged generic owners:
--
--   DASHI.Core.HistoryConditionedChoiceExact
--   DASHI.Core.AdmissibleTransitionHyperfabricExact
--
-- It deliberately does NOT import live draft PRs #658, #659 or #662.  Their
-- newer action-feedback / governed-lineage / history-qualified-selection work
-- is retained below only as cross-PR design provenance until merged.
--
-- Central distinction:
--
--   same present religious participation
--   != same formation history
--   != same currently reachable revision cone
--   != same admissible next action.
--
-- A reopening opportunity is proof-relevant.  It is not merely a probability
-- or a narrative label: the relevant alternative/refusal/revision/exit
-- conditions must actually enable the move in the situated state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation
import DASHI.Culture.ChildReligiousEpistemicReopeningBidiExact as Reopening
import DASHI.Culture.JohnAnthonyBrownRetrospectiveExposureProvenanceExact as Retrospective

------------------------------------------------------------------------
-- 1. Same present participation can hide different formation histories.
------------------------------------------------------------------------

data FormationHistory : Set where
  inheritedClosedHistory revisablyEndorsedHistory : FormationHistory

data PresentParticipation : Set where
  sameReligiousParticipation : PresentParticipation

data FormationPattern : Set where
  closedAuthorityPattern reopenedRevisionPattern : FormationPattern

data PresentChoice : Set where
  continueWithoutRevision reviseOrReendorse : PresentChoice

data ReachableRevisionCone : Set where
  constrainedRevisionCone openRevisionCone : ReachableRevisionCone

presentParticipation : FormationHistory -> PresentParticipation
presentParticipation _ = sameReligiousParticipation

formationPattern : FormationHistory -> FormationPattern
formationPattern inheritedClosedHistory = closedAuthorityPattern
formationPattern revisablyEndorsedHistory = reopenedRevisionPattern

historyQualifiedChoice : FormationHistory -> PresentChoice
historyQualifiedChoice inheritedClosedHistory = continueWithoutRevision
historyQualifiedChoice revisablyEndorsedHistory = reviseOrReendorse

revisionCone : FormationHistory -> ReachableRevisionCone
revisionCone inheritedClosedHistory = constrainedRevisionCone
revisionCone revisablyEndorsedHistory = openRevisionCone

religiousHistoryChoiceSurface : History.HistoryConditionedChoiceSurface
religiousHistoryChoiceSurface = record
  { History.History = FormationHistory
  ; History.Observation = PresentParticipation
  ; History.Pattern = FormationPattern
  ; History.Choice = PresentChoice
  ; History.observe = presentParticipation
  ; History.patternOf = formationPattern
  ; History.choose = historyQualifiedChoice
  ; History.historyReading =
      "Same present religious participation may arise from an inherited closed route or a later revisably endorsed route; present participation alone does not recover the history-sensitive revision choice."
  }

religiousHistoryChoiceWitness :
  History.DistinctHistoriesSameObservationDifferentChoice religiousHistoryChoiceSurface
religiousHistoryChoiceWitness = record
  { History.leftHistory = inheritedClosedHistory
  ; History.rightHistory = revisablyEndorsedHistory
  ; History.historiesDistinct = λ ()
  ; History.samePresentObservation = refl
  ; History.choicesDiffer = λ ()
  }

presentParticipationCannotRecoverHistoryQualifiedChoice :
  INF.FactorsThrough presentParticipation historyQualifiedChoice -> ⊥
presentParticipationCannotRecoverHistoryQualifiedChoice =
  History.historySensitiveChoiceCannotDescendThroughPresentObservation
    religiousHistoryChoiceWitness

religiousFutureConeSurface : History.HistoryConditionedFutureConeSurface
religiousFutureConeSurface = record
  { History.FutureHistory = FormationHistory
  ; History.FutureObservation = PresentParticipation
  ; History.FutureConeCode = ReachableRevisionCone
  ; History.observeFutureHistory = presentParticipation
  ; History.futureCone = revisionCone
  ; History.futureReading =
      "The same outward participation surface can coexist with different reachable revision/exit cones."
  }

religiousFutureConeWitness :
  History.SameObservationDifferentFutureCone religiousFutureConeSurface
religiousFutureConeWitness = record
  { History.futureLeftHistory = inheritedClosedHistory
  ; History.futureRightHistory = revisablyEndorsedHistory
  ; History.futureSameObservation = refl
  ; History.futureConesDiffer = λ ()
  }

presentParticipationCannotRecoverRevisionCone :
  INF.FactorsThrough presentParticipation revisionCone -> ⊥
presentParticipationCannotRecoverRevisionCone =
  History.futureConeCannotDescendThroughPresentObservation religiousFutureConeWitness

------------------------------------------------------------------------
-- 2. Proof-relevant reopening transition.
------------------------------------------------------------------------

data ReopeningState : Set where
  closedSituatedState reopenedSituatedState : ReopeningState

data ReopeningParameter : Set where
  noReopeningSupport reopeningSupport : ReopeningParameter

data ReopeningMove : Set where
  reviseCommitment : ReopeningMove

data Never : Set where

Enabled : ReopeningMove -> ReopeningParameter -> ReopeningState -> Set
Enabled reviseCommitment noReopeningSupport closedSituatedState = Never
Enabled reviseCommitment reopeningSupport closedSituatedState = ⊤
Enabled reviseCommitment noReopeningSupport reopenedSituatedState = ⊤
Enabled reviseCommitment reopeningSupport reopenedSituatedState = ⊤

step : ReopeningMove -> ReopeningParameter -> ReopeningState -> ReopeningState
step reviseCommitment noReopeningSupport closedSituatedState = closedSituatedState
step reviseCommitment reopeningSupport closedSituatedState = reopenedSituatedState
step reviseCommitment noReopeningSupport reopenedSituatedState = reopenedSituatedState
step reviseCommitment reopeningSupport reopenedSituatedState = reopenedSituatedState

InvariantRegion : ReopeningState -> Set
InvariantRegion _ = ⊤

preservesInvariant :
  (move : ReopeningMove) ->
  (parameter : ReopeningParameter) ->
  (state : ReopeningState) ->
  Enabled move parameter state ->
  InvariantRegion state ->
  InvariantRegion (step move parameter state)
preservesInvariant move parameter state enabled invariant = tt

religiousReopeningTransitionSystem : Transition.AdmissibleTransitionSystem
religiousReopeningTransitionSystem =
  Transition.admissibleTransitionSystem
    ReopeningState
    ReopeningParameter
    ReopeningMove
    Enabled
    step
    InvariantRegion
    preservesInvariant
    "Finite DASHI religious-formation reopening adapter over merged AdmissibleTransitionHyperfabricExact; not an empirical claim that all religious formation follows this transition."

closedWithoutSupportNotEnabled :
  Transition.Enabled religiousReopeningTransitionSystem
    reviseCommitment noReopeningSupport closedSituatedState -> ⊥
closedWithoutSupportNotEnabled ()

closedWithSupportEnabled :
  Transition.Enabled religiousReopeningTransitionSystem
    reviseCommitment reopeningSupport closedSituatedState
closedWithSupportEnabled = tt

supportedRevisionAdmitted :
  Transition.AdmittedStep religiousReopeningTransitionSystem
    reviseCommitment reopeningSupport closedSituatedState
supportedRevisionAdmitted = Transition.admittedStep tt tt

unsupportedRevisionCannotBeAdmitted :
  Transition.AdmittedStep religiousReopeningTransitionSystem
    reviseCommitment noReopeningSupport closedSituatedState -> ⊥
unsupportedRevisionCannotBeAdmitted =
  Transition.disabledExcludesAdmittedStep closedWithoutSupportNotEnabled

supportedRevisionReachesReopenedState :
  Transition.step religiousReopeningTransitionSystem
    reviseCommitment reopeningSupport closedSituatedState
  ≡ reopenedSituatedState
supportedRevisionReachesReopenedState = refl

------------------------------------------------------------------------
-- 3. Weld reopening support to the existing multidimensional formation owner.
------------------------------------------------------------------------

record ReopeningEnablementReceipt : Set where
  constructor reopening-enablement-receipt
  field
    formationReceipt : Formation.ReopeningReceipt
    epistemicReceipt : Reopening.EpistemicReopeningReceipt
    alternativesAccessible :
      Formation.alternativesLaterAccessible formationReceipt ≡ true
    refusalPermitted :
      Formation.refusalLaterPermitted formationReceipt ≡ true
    revisionPossible :
      Formation.revisionLaterPossible formationReceipt ≡ true
    practicalExitAvailable :
      Formation.exitLaterPracticable formationReceipt ≡ true
    supportParameter : ReopeningParameter
    supportParameterIsEnabled : supportParameter ≡ reopeningSupport

open ReopeningEnablementReceipt public

canonicalReopeningEnablementReceipt : ReopeningEnablementReceipt
canonicalReopeningEnablementReceipt =
  reopening-enablement-receipt
    Formation.canonicalOpenReopening
    Reopening.canonicalReopeningReceipt
    refl refl refl refl
    reopeningSupport refl

------------------------------------------------------------------------
-- 4. Retrospective evidence remains evidence about history, not a time machine.
------------------------------------------------------------------------

retrospectiveBoundaryRetained : Retrospective.RetrospectiveExposureBoundary
retrospectiveBoundaryRetained = Retrospective.canonicalRetrospectiveExposureBoundary

record HistoryEvidenceWeld : Set where
  constructor history-evidence-weld
  field
    presentSurfaceDoesNotRecoverFormationHistory : Bool
    retrospectiveParticipantEvidenceMayInformHistory : Bool
    retrospectiveReportBecomesContemporaneousRecord : Bool
    prospectiveAdultFollowupRepairsChildhoodProvenance : Bool
    historySensitiveChoiceNeedsHistoryEvidenceRatherThanSurfaceGuess : Bool

canonicalHistoryEvidenceWeld : HistoryEvidenceWeld
canonicalHistoryEvidenceWeld =
  history-evidence-weld true true false false true

------------------------------------------------------------------------
-- 5. Draft cross-pollination provenance without draft-on-draft imports.
------------------------------------------------------------------------

record CrossPRDesignProvenance : Set where
  constructor cross-pr-design-provenance
  field
    sourcePR658 : String
    sourcePR659 : String
    sourcePR662 : String
    reusedMergedHistoryOwner : Bool
    reusedMergedAdmissibleTransitionOwner : Bool
    importsDraftBranches : Bool
    boundedReading : String

canonicalCrossPRDesignProvenance : CrossPRDesignProvenance
canonicalCrossPRDesignProvenance = cross-pr-design-provenance
  "PR #658: conceived/effective/enacted choice and action-feedback historical hyperfabric"
  "PR #659: governed observation provenance and coordinate-lineage transport"
  "PR #662: history-qualified selection and situated dissent/deception assays"
  true true false
  "Draft PRs motivate comparison surfaces only. This owner imports only merged generic core plus owners already local to #656."

------------------------------------------------------------------------
-- 6. No-promotion boundary.
------------------------------------------------------------------------

data SameParticipationPromotesSameHistory : Set where

data FormalAlternativePromotesEffectiveReopening : Set where

data ReopeningSupportPromotesBeliefChange : Set where

data AdmittedRevisionPromotesReligionRejection : Set where

data RetrospectiveReportPromotesUniqueFormationHistory : Set where

sameParticipationDoesNotPromoteSameHistory : SameParticipationPromotesSameHistory -> ⊥
sameParticipationDoesNotPromoteSameHistory ()

formalAlternativeDoesNotPromoteEffectiveReopening :
  FormalAlternativePromotesEffectiveReopening -> ⊥
formalAlternativeDoesNotPromoteEffectiveReopening ()

reopeningSupportDoesNotPromoteBeliefChange : ReopeningSupportPromotesBeliefChange -> ⊥
reopeningSupportDoesNotPromoteBeliefChange ()

admittedRevisionDoesNotPromoteReligionRejection :
  AdmittedRevisionPromotesReligionRejection -> ⊥
admittedRevisionDoesNotPromoteReligionRejection ()

retrospectiveReportDoesNotPromoteUniqueHistory :
  RetrospectiveReportPromotesUniqueFormationHistory -> ⊥
retrospectiveReportDoesNotPromoteUniqueHistory ()

record ChildReligiousHistoryQualifiedReopeningBoundary : Set where
  constructor child-religious-history-qualified-reopening-boundary
  field
    sameParticipationDeterminesFormationHistory : Bool
    sameParticipationDeterminesRevisionCone : Bool
    reopeningIsProofRelevant : Bool
    disabledRevisionIsMerelyLowProbability : Bool
    alternativesRefusalRevisionAndExitMatter : Bool
    reopeningForcesBeliefChange : Bool
    reopeningForcesReligiousExit : Bool
    retrospectiveEvidenceCanInformHistory : Bool
    retrospectiveEvidenceUniquelyRecoversHistory : Bool
    draftCrossPollinationImportedDirectly : Bool

canonicalChildReligiousHistoryQualifiedReopeningBoundary :
  ChildReligiousHistoryQualifiedReopeningBoundary
canonicalChildReligiousHistoryQualifiedReopeningBoundary =
  child-religious-history-qualified-reopening-boundary
    false false true false true false false true false false
