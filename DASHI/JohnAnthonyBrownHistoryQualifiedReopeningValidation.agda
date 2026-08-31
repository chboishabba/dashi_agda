module DASHI.JohnAnthonyBrownHistoryQualifiedReopeningValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Culture.ChildReligiousHistoryQualifiedReopeningExact as H

presentParticipationDoesNotRecoverChoice :
  INF.FactorsThrough H.presentParticipation H.historyQualifiedChoice -> ⊥
presentParticipationDoesNotRecoverChoice =
  H.presentParticipationCannotRecoverHistoryQualifiedChoice

presentParticipationDoesNotRecoverCone :
  INF.FactorsThrough H.presentParticipation H.revisionCone -> ⊥
presentParticipationDoesNotRecoverCone =
  H.presentParticipationCannotRecoverRevisionCone

unsupportedRevisionNotAdmitted :
  Transition.AdmittedStep H.religiousReopeningTransitionSystem
    H.reviseCommitment H.noReopeningSupport H.closedSituatedState -> ⊥
unsupportedRevisionNotAdmitted = H.unsupportedRevisionCannotBeAdmitted

supportedRevisionReachesReopened :
  Transition.step H.religiousReopeningTransitionSystem
    H.reviseCommitment H.reopeningSupport H.closedSituatedState
  ≡ H.reopenedSituatedState
supportedRevisionReachesReopened = H.supportedRevisionReachesReopenedState

sameParticipationNotSameHistory : H.SameParticipationPromotesSameHistory -> ⊥
sameParticipationNotSameHistory = H.sameParticipationDoesNotPromoteSameHistory

formalAlternativeNotEffectiveReopening :
  H.FormalAlternativePromotesEffectiveReopening -> ⊥
formalAlternativeNotEffectiveReopening = H.formalAlternativeDoesNotPromoteEffectiveReopening

reopeningDoesNotForceBeliefChange : H.ReopeningSupportPromotesBeliefChange -> ⊥
reopeningDoesNotForceBeliefChange = H.reopeningSupportDoesNotPromoteBeliefChange

admittedRevisionDoesNotForceReligiousExit :
  H.AdmittedRevisionPromotesReligionRejection -> ⊥
admittedRevisionDoesNotForceReligiousExit = H.admittedRevisionDoesNotPromoteReligionRejection

retrospectiveReportDoesNotRecoverUniqueHistory :
  H.RetrospectiveReportPromotesUniqueFormationHistory -> ⊥
retrospectiveReportDoesNotRecoverUniqueHistory =
  H.retrospectiveReportDoesNotPromoteUniqueHistory

noDraftOnDraftImport :
  H.CrossPRDesignProvenance.importsDraftBranches H.canonicalCrossPRDesignProvenance
  ≡ false
noDraftOnDraftImport = refl
