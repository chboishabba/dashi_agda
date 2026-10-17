module DASHI.Physics.Plasma.Phase243PlasmaConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- PHASE-243 -> PHYSICAL MAGNET REALIZATION
--
-- The finite Core243 state chooses a discrete rook-incidence / phase sector.
-- Continuous amplitudes, surface geometry and current-potential data remain a
-- fibre over that base state.  The physical realization is accepted only when
-- it preserves the already-owned hard plasma consumers.
------------------------------------------------------------------------

record Phase243PhysicalRealization
    (PhysicalState : Set)
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor phase243-physical-realization
  field
    baseState : Rook.Core243
    physicalState : PhysicalState
    discreteStateSelectsRookIncidenceReceipt : Set
    continuousAmplitudeFibreReceipt : Set
    samePhaseActionReceipt : Set
    nonAxisymmetricAmplitudeReceipt : Set
    divergenceFreeReceipt : Set
    nestedToroidalSurfaceReceipt : Set
    constantMagnitudeOrControlledDefectReceipt : Set
    zeroBounceReceipt : ZeroBounce.ZeroBounceReceipt population
    finiteBetaReceipt : Set
    flowAnisotropyABCReceipt : Set
    realizationReference : String

open Phase243PhysicalRealization public

record Phase243EngineeringConsumer
    {PhysicalState : Set}
    {population : ZeroBounce.DeclaredParticlePopulation}
    (r : Phase243PhysicalRealization PhysicalState population) : Set₁ where
  constructor phase243-engineering-consumer
  field
    windingSurfaceReceipt : Set
    currentPotentialInverseReceipt : Set
    coilRegularizationReceipt : Set
    coilPlasmaSameObjectReceipt : Set
    freeBoundaryEquilibriumReceipt : Set
    actuatorBandwidthReceipt : Set
    engineeringReference : String

open Phase243EngineeringConsumer public

record Phase243OrbitConsumer
    {PhysicalState : Set}
    {population : ZeroBounce.DeclaredParticlePopulation}
    (r : Phase243PhysicalRealization PhysicalState population) : Set₁ where
  constructor phase243-orbit-consumer
  field
    guidingCentreReplayReceipt : Set
    finiteOrbitWidthReceipt : Set
    curvatureDriftReceipt : Set
    gradBDriftReceipt : Set
    energeticParticleReceipt : Set
    collisionTurbulenceReceipt : Set
    sameBestKnownReferenceChartReceipt : Set
    sameOrBetterBestKnownReferenceReceipt : Set
    orbitReference : String

open Phase243OrbitConsumer public

record AcceptedPhase243Candidate
    {PhysicalState : Set}
    {population : ZeroBounce.DeclaredParticlePopulation}
    (r : Phase243PhysicalRealization PhysicalState population) : Set₁ where
  constructor accepted-phase243-candidate
  field
    engineering : Phase243EngineeringConsumer r
    orbit : Phase243OrbitConsumer r
    admissibleConeReceipt : Set
    sparseSupportReceipt : Set
    consumerAdequacyReceipt : Set
    acceptanceReference : String

open AcceptedPhase243Candidate public

record Phase243ConsumerBoundary : Set where
  constructor phase243-consumer-boundary
  field
    finite243CarrierAloneProvesGoodMagnet : Bool
    finite243CarrierAloneProvesGoodMagnetIsFalse :
      finite243CarrierAloneProvesGoodMagnet ≡ false
    continuousFibreMayCollapseToAxisymmetricLaneSilently : Bool
    continuousFibreMayCollapseToAxisymmetricLaneSilentlyIsFalse :
      continuousFibreMayCollapseToAxisymmetricLaneSilently ≡ false
    nonAxisymmetricExternalTransformGateRequired : Bool
    nonAxisymmetricExternalTransformGateRequiredIsTrue :
      nonAxisymmetricExternalTransformGateRequired ≡ true
    coilAndOrbitConsumersRemainMandatory : Bool
    coilAndOrbitConsumersRemainMandatoryIsTrue :
      coilAndOrbitConsumersRemainMandatory ≡ true

canonicalPhase243ConsumerBoundary : Phase243ConsumerBoundary
canonicalPhase243ConsumerBoundary =
  phase243-consumer-boundary false refl false refl true refl true refl

pythonPhysicalReplayReference : String
pythonPhysicalReplayReference =
  "Local 243-state two-amplitude replay: unconstrained best states collapse the non-axisymmetric amplitude toward zero; external-transform use therefore requires an explicit non-axisymmetric-amplitude gate before acceptance."
