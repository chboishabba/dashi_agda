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

gammaFaceNonpositiveCount absolutePacketFaceNonpositiveCount : Nat
gammaFaceNonpositiveCount = 0
absolutePacketFaceNonpositiveCount = 16

normalizedPacketFaceNonpositiveCount : Nat
normalizedPacketFaceNonpositiveCount = 0

offPacketFaceNonpositiveCount sizeFaceNonpositiveCount : Nat
offPacketFaceNonpositiveCount = 0
sizeFaceNonpositiveCount = 0

absolutePacketFloorFailsEveryFiniteSample :
  absolutePacketFaceNonpositiveCount ≡ 16
absolutePacketFloorFailsEveryFiniteSample = refl

normalizedPacketFloorHasNoFiniteCounterexample :
  normalizedPacketFaceNonpositiveCount ≡ 0
normalizedPacketFloorHasNoFiniteCounterexample = refl

originalAbsoluteFloorRouteStrictOnFiniteSample : Bool
originalAbsoluteFloorRouteStrictOnFiniteSample = false

correctedNormalizedRouteStrictOnFiniteSample : Bool
correctedNormalizedRouteStrictOnFiniteSample = true

absolutePacketFloorInvariantCandidateSurvives : Bool
absolutePacketFloorInvariantCandidateSurvives = false

finiteTrajectoryImpliesCutoffUniformControl : Bool
finiteTrajectoryImpliesCutoffUniformControl = false

finiteFaceSearchProvesDiniInwardness : Bool
finiteFaceSearchProvesDiniInwardness = false
