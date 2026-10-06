module DASHI.Governance.OccupyLibraryLongitudinalIncidenceRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Longitudinal

nov20EdgeCountPinned :
  Longitudinal.edgeCount Longitudinal.nov20Edges ≡ 9
nov20EdgeCountPinned = refl

nov28EdgeCountPinned :
  Longitudinal.edgeCount Longitudinal.nov28Edges ≡ 7
nov28EdgeCountPinned = refl

dec11EdgeCountPinned :
  Longitudinal.edgeCount Longitudinal.dec11Edges ≡ 11
dec11EdgeCountPinned = refl

jan08EdgeCountPinned :
  Longitudinal.edgeCount Longitudinal.jan08Edges ≡ 7
jan08EdgeCountPinned = refl

meetingFamilyTotalPinned :
  Longitudinal.edgeCount Longitudinal.longitudinalObservedEdges ≡ 52
meetingFamilyTotalPinned = refl

dec04MediationBurdenObserved :
  Longitudinal.ProcessBurdenObserved Longitudinal.dec04Meeting Longitudinal.majorityMeetingTimeSpentInMediation
ndec04MediationBurdenObserved = Longitudinal.dec04MajorityMediation

nov28DiscussionBreakdownObserved :
  Longitudinal.ProcessBurdenObserved Longitudinal.nov28Meeting Longitudinal.discussionBreakdown
nov28DiscussionBreakdownObserved = Longitudinal.nov28Breakdown

incidenceDoesNotCauseBurdenByDefinition :
  Longitudinal.incidenceCountCausallyExplainsBurden Longitudinal.canonicalLongitudinalBoundary ≡ false
incidenceDoesNotCauseBurdenByDefinition = refl

burdenObservationsAreNotCostFunctional :
  Longitudinal.processObservationIsCoordinationCost Longitudinal.canonicalLongitudinalBoundary ≡ false
burdenObservationsAreNotCostFunctional = refl
