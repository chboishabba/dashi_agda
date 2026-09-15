module DASHI.Physics.Foundations.PhasedArrayRFSensingRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RFSensingThroughWallExact as RF

------------------------------------------------------------------------
-- RED contract for the follow-on to the goniometer/DF tranche.
-- The production owners imported above intentionally do not exist at the
-- point this regression is introduced.
------------------------------------------------------------------------

arraySeparatesPhysicalAndBeamCoordinates : Set
arraySeparatesPhysicalAndBeamCoordinates =
  Array.ArrayObservationCoordinate

arrayBearingRemainsCoarse : Set
arrayBearingRemainsCoarse =
  ¬ Array.ArrayBearingDeterminesExactEmitterWorld

throughWallObservationRemainsCoarse : Set
throughWallObservationRemainsCoarse =
  ¬ RF.RFObservationDeterminesExactHumanWorld

communityLeadDoesNotPayTechnicalFact : Set
communityLeadDoesNotPayTechnicalFact =
  RF.CommunityLeadAuthorityFirewall

canonicalArrayCollisionRequired : Array.SameArrayBearingCollision
canonicalArrayCollisionRequired = Array.canonicalSameArrayBearingCollision

canonicalRFBoundaryRequired : RF.RFSensingBoundary
canonicalRFBoundaryRequired = RF.canonicalRFSensingBoundary
