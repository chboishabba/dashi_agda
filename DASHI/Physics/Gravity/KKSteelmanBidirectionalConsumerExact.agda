module DASHI.Physics.Gravity.KKSteelmanBidirectionalConsumerExact where

-- Consumer-indexed BIDI for KK/EM/Higgs/torque cross-pollination.
-- The theorem-bearing part reuses canonical transport and non-descent.
-- Finite probes certify information loss, NOT a real Earth solution.

open import DASHI.Core.Prelude

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

------------------------------------------------------------------------
-- Backward, physical steelman: obligations cannot be inferred from
-- the mere existence of a metric or a sourced linear scalar fixture.
------------------------------------------------------------------------

record KKEarthSteelman (Model : Set) : Set₁ where
  field
    sameFiveDimensionalAction : Model → Set
    compactCircleAndBoundaryConditions : Model → Set
    matterCouplingDerivedFromAction : Model → Set
    conservedPhysicalSource : Model → Set
    regularInteriorExteriorMatching : Model → Set
    scalarAndGaugeStability : Model → Set
    knownGravityTestsSatisfied : Model → Set
    physicalOrbitalObservable : Model → Set

open KKEarthSteelman public

record SteelmanEligible {Model : Set}
    (requirements : KKEarthSteelman Model)
    (candidate : Model) : Set where
  field
    action : sameFiveDimensionalAction requirements candidate
    circle : compactCircleAndBoundaryConditions requirements candidate
    coupling : matterCouplingDerivedFromAction requirements candidate
    source : conservedPhysicalSource requirements candidate
    matching : regularInteriorExteriorMatching requirements candidate
    stability : scalarAndGaugeStability requirements candidate
    knownTests : knownGravityTestsSatisfied requirements candidate
    orbit : physicalOrbitalObservable requirements candidate

open SteelmanEligible public

-- Conditional only: an observable cannot fabricate eligibility.
record AdmissibleKKPrediction {Model Observation : Set}
    (requirements : KKEarthSteelman Model)
    (predict : Model → Observation) : Set₁ where
  field
    candidate : Model
    eligibility : SteelmanEligible requirements candidate
    prediction : Observation
    predictionIsFromCandidate : prediction ≡ predict candidate

------------------------------------------------------------------------
-- Finite probes: local gauge data does not determine radion data;
-- orbital agreement does not certify a regular source or stability.
------------------------------------------------------------------------

record ProbeState : Set where
  constructor probe
  field
    gaugeSector : Bool
    radionSector : Bool
    sourceCompatible : Bool
    nodalSignature : Bool
    azimuthalMetricData : Bool

open ProbeState public

gaugeOnly : ProbeState → Bool
gaugeOnly = gaugeSector

orbitOnly : ProbeState → Bool
orbitOnly = nodalSignature

radionQuestion : ProbeState → Bool
radionQuestion = radionSector

steelmanQuestion : ProbeState → Bool × Bool
steelmanQuestion state = radionSector state , sourceCompatible state

-- This repaired surface is sufficient ONLY for the two-bit probe.
repairedObservation : ProbeState → Bool × (Bool × Bool)
repairedObservation state =
  orbitOnly state , steelmanQuestion state

steelmanFromRepair :
  Transport.ClaimTransport repairedObservation steelmanQuestion
steelmanFromRepair =
  Transport.claimTransport proj₂ (λ state → refl)

orbitFromRepair :
  Transport.ClaimTransport repairedObservation orbitOnly
orbitFromRepair =
  Transport.claimTransport proj₁ (λ state → refl)

probeGaugeLeft : ProbeState
probeGaugeLeft = probe false false false true false

probeGaugeRight : ProbeState
probeGaugeRight = probe false true false true false

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

gaugeCannotAnswerRadion :
  Transport.ClaimNonTransportWitness gaugeOnly radionQuestion
gaugeCannotAnswerRadion =
  Descent.consumerNonDescentWitness
    probeGaugeLeft probeGaugeRight refl falseNotTrue

noRadionClaimFromGaugeOnly :
  Transport.ClaimTransport gaugeOnly radionQuestion → ⊥
noRadionClaimFromGaugeOnly =
  Transport.claimNonTransportWitnessBlocksTransport
    gaugeCannotAnswerRadion

probeOrbitLeft : ProbeState
probeOrbitLeft = probe false false false true false

probeOrbitRight : ProbeState
probeOrbitRight = probe false false true true false

steelmanPairUnequal :
  (false , false) ≡ (false , true) → ⊥
steelmanPairUnequal ()

orbitDoesNotDetermineSteelman :
  Transport.ClaimNonTransportWitness orbitOnly steelmanQuestion
orbitDoesNotDetermineSteelman =
  Descent.consumerNonDescentWitness
    probeOrbitLeft probeOrbitRight refl steelmanPairUnequal

noSteelmanClaimFromOrbitOnly :
  Transport.ClaimTransport orbitOnly steelmanQuestion → ⊥
noSteelmanClaimFromOrbitOnly =
  Transport.claimNonTransportWitnessBlocksTransport
    orbitDoesNotDetermineSteelman

-- Any successful refinement for the shown collision must separate it.
steelmanRepairMustSeparate :
  (refine : ProbeState → Bool) →
  Repair.RefinementRepairs orbitOnly refine steelmanQuestion →
  refine probeOrbitLeft ≡ refine probeOrbitRight → ⊥
steelmanRepairMustSeparate refine repaired same =
  Repair.refinementRepairSeparatesWitness
    orbitDoesNotDetermineSteelman repaired same

-- Neither negative result invalidates the smaller consumer.
orbitAnswersOrbit : Transport.ClaimTransport orbitOnly orbitOnly
orbitAnswersOrbit = Transport.identityClaimTransport orbitOnly

gaugeAnswersGauge : Transport.ClaimTransport gaugeOnly gaugeOnly
gaugeAnswersGauge = Transport.identityClaimTransport gaugeOnly
