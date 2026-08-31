{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFrontierRouteAdmissionRound147Exact where

------------------------------------------------------------------------
-- ROUND147: LEAST-PRIVILEGE ADMISSION FOR BALABAN FRONTIER SEARCH
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146

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

moveDefaultAuthority : FrontierMoveKind → Least.TheoremAuthority
moveDefaultAuthority repositoryProofReuse = Least.derivedRepositoryTheorem
moveDefaultAuthority sourceReconstruction = Least.sourceTheoremMatched
moveDefaultAuthority symbolicDerivation = Least.conditionalInterface
moveDefaultAuthority numericalExperiment = Least.analogyOnly
moveDefaultAuthority physicalMeasurement = Least.conditionalInterface

record DirectLeafClosureCapability (move : FrontierMoveKind) : Set where
  field
    closedLeaf : Least.ClosedLeafCapability (moveDefaultAuthority move)

open DirectLeafClosureCapability public

-- Generic least-privilege authority makes this an actual impossibility theorem.
numericalExperimentCannotDirectlyCloseLeaf :
  DirectLeafClosureCapability numericalExperiment → ⊥
numericalExperimentCannotDirectlyCloseLeaf capability =
  Least.analogyCannotCloseLeaf (closedLeaf capability)

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
