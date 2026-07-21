module DASHI.Physics.Closure.NSPeriodicConcreteGalerkinFalsificationReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Exact status mirror of the deterministic finite Galerkin tests.
------------------------------------------------------------------------

trajectorySeedCount trajectoryStepsPerSeed : Nat
trajectorySeedCount = 3
trajectoryStepsPerSeed = 8

allTrajectoryEnergiesNonincreasing : Bool
allTrajectoryEnergiesNonincreasing = true

allFiniteTrajectoryIntegralsFinite : Bool
allFiniteTrajectoryIntegralsFinite = true

gammaFaceNonpositiveCount packetFaceNonpositiveCount : Nat
gammaFaceNonpositiveCount = 0
packetFaceNonpositiveCount = 16

offPacketFaceNonpositiveCount sizeFaceNonpositiveCount : Nat
offPacketFaceNonpositiveCount = 0
sizeFaceNonpositiveCount = 0

packetFloorFailsEveryFiniteSample :
  packetFaceNonpositiveCount ≡ 16
packetFloorFailsEveryFiniteSample = refl

allFourFacesStrictOnFiniteSample : Bool
allFourFacesStrictOnFiniteSample = false

absolutePacketFloorInvariantCandidateSurvives : Bool
absolutePacketFloorInvariantCandidateSurvives = false

finiteTrajectoryImpliesCutoffUniformControl : Bool
finiteTrajectoryImpliesCutoffUniformControl = false

finiteFaceSearchProvesDiniInwardness : Bool
finiteFaceSearchProvesDiniInwardness = false
