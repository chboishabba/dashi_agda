{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFrontierRouteAdmissionRound147Exact where

------------------------------------------------------------------------
-- ROUND147: LEAST-PRIVILEGE ADMISSION FOR BALABAN FRONTIER SEARCH
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146

-- Search/experiment modalities remain distinct.  In particular, a simulation is
-- not retyped as a theorem proof merely because it is useful for search.
data FrontierMoveKind : Set where
  repositoryProofReuse
  sourceReconstruction
  symbolicDerivation
  numericalExperiment
  physicalMeasurement
  : FrontierMoveKind

record AdmittedBalabanFrontierRoute : Set₁ where
  field
    route : R146.BalabanFrontierRoute
    kind : FrontierMoveKind
    admission : Least.RouteAdmission

open AdmittedBalabanFrontierRoute public

liveProofSearch : AdmittedBalabanFrontierRoute → Least.LiveProofSearch
liveProofSearch dataSet = Least.elaborateRoute (admission dataSet)

-- Evidence authority is deliberately typed independently of move kind.  A
-- numerical experiment can guide route choice without thereby owning a closed
-- theorem leaf.
moveDefaultAuthority : FrontierMoveKind → Least.TheoremAuthority
moveDefaultAuthority repositoryProofReuse = Least.derivedRepositoryTheorem
moveDefaultAuthority sourceReconstruction = Least.sourceTheoremMatched
moveDefaultAuthority symbolicDerivation = Least.conditionalInterface
moveDefaultAuthority numericalExperiment = Least.analogyOnly
moveDefaultAuthority physicalMeasurement = Least.conditionalInterface

-- Only theorem authorities accepted by the generic least-privilege owner can
-- directly close a proof leaf.  We expose that capability rather than inventing
-- an ad-hoc Balaban success Boolean.
record DirectLeafClosureCapability (move : FrontierMoveKind) : Set where
  field
    closedLeaf : Least.ClosedLeafCapability (moveDefaultAuthority move)

open DirectLeafClosureCapability public

-- Constructor-level regressions: numerical experiments and mere conditional
-- interfaces cannot directly inhabit a closed theorem capability.
numericalExperimentDoesNotDirectlyCloseLeaf :
  DirectLeafClosureCapability numericalExperiment →
  Least.ClosedLeafCapability Least.analogyOnly
numericalExperimentDoesNotDirectlyCloseLeaf = closedLeaf

symbolicConditionalInterfaceDoesNotDirectlyCloseLeaf :
  DirectLeafClosureCapability symbolicDerivation →
  Least.ClosedLeafCapability Least.conditionalInterface
symbolicConditionalInterfaceDoesNotDirectlyCloseLeaf = closedLeaf

record BalabanFrontierRouteBoundary : Set where
  constructor balabanFrontierRouteBoundary
  field
    simulationOutputIsAutomaticallySourceProof : Bool
    simulationOutputIsAutomaticallySourceProofIsFalse :
      simulationOutputIsAutomaticallySourceProof ≡ false
    physicalMeasurementIsAutomaticallyFormalProof : Bool
    physicalMeasurementIsAutomaticallyFormalProofIsFalse :
      physicalMeasurementIsAutomaticallyFormalProof ≡ false
    routeNeedsSameObjectAdmissionBeforeLiveSearch : Bool
    routeNeedsSameObjectAdmissionBeforeLiveSearchIsTrue :
      routeNeedsSameObjectAdmissionBeforeLiveSearch ≡ true

canonicalBalabanFrontierRouteBoundary : BalabanFrontierRouteBoundary
canonicalBalabanFrontierRouteBoundary =
  balabanFrontierRouteBoundary false refl false refl true refl

balabanFrontierRouteAdmissionLevel : ProofLevel
balabanFrontierRouteAdmissionLevel = machineChecked
