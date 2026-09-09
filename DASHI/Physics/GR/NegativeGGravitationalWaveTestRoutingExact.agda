module DASHI.Physics.GR.NegativeGGravitationalWaveTestRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact as WaveTest
import DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact as SignedWave

------------------------------------------------------------------------
-- NEGATIVE-G RELEVANCE ACROSS EXISTING GW TEST FAMILIES
--
-- A gravitational-wave test can constrain a negative-G model only through the
-- physical coordinates it actually consumes.  Vacuum propagation is not by
-- itself a matter-coupling-sign measurement.  Source-dynamics tests require a
-- self-consistent source model re-solved under the candidate sign.
------------------------------------------------------------------------

data NegativeGWaveTestRole : Set where
  requiresReSolvedSourceDynamics : NegativeGWaveTestRole
  propagationAloneDoesNotIdentifyGSign : NegativeGWaveTestRole
  populationAndSourceModelRequired : NegativeGWaveTestRole

negativeGRoleFor : WaveTest.WaveTestFamily → NegativeGWaveTestRole
negativeGRoleFor WaveTest.inspiralPhaseConsistency = requiresReSolvedSourceDynamics
negativeGRoleFor WaveTest.mergerRingdownConsistency = requiresReSolvedSourceDynamics
negativeGRoleFor WaveTest.dispersionPropagation = propagationAloneDoesNotIdentifyGSign
negativeGRoleFor WaveTest.polarizationContent = propagationAloneDoesNotIdentifyGSign
negativeGRoleFor WaveTest.remnantConsistency = requiresReSolvedSourceDynamics
negativeGRoleFor WaveTest.stochasticCorrelationShape = populationAndSourceModelRequired
negativeGRoleFor WaveTest.cosmologicalPropagation = propagationAloneDoesNotIdentifyGSign

record NegativeGWaveTestDemand : Set where
  constructor negative-g-wave-test-demand
  field
    testFamily : WaveTest.WaveTestFamily
    role : NegativeGWaveTestRole
    roleMatches : negativeGRoleFor testFamily ≡ role
    sourceDynamicsCarrierRequired : Bool
    propagationModelCarrierRequired : Bool
    populationModelCarrierRequired : Bool

open NegativeGWaveTestDemand public

demandFor : WaveTest.WaveTestFamily → NegativeGWaveTestDemand
demandFor WaveTest.inspiralPhaseConsistency =
  negative-g-wave-test-demand WaveTest.inspiralPhaseConsistency
    requiresReSolvedSourceDynamics refl true true false
demandFor WaveTest.mergerRingdownConsistency =
  negative-g-wave-test-demand WaveTest.mergerRingdownConsistency
    requiresReSolvedSourceDynamics refl true true false
demandFor WaveTest.dispersionPropagation =
  negative-g-wave-test-demand WaveTest.dispersionPropagation
    propagationAloneDoesNotIdentifyGSign refl false true false
demandFor WaveTest.polarizationContent =
  negative-g-wave-test-demand WaveTest.polarizationContent
    propagationAloneDoesNotIdentifyGSign refl false true false
demandFor WaveTest.remnantConsistency =
  negative-g-wave-test-demand WaveTest.remnantConsistency
    requiresReSolvedSourceDynamics refl true true false
demandFor WaveTest.stochasticCorrelationShape =
  negative-g-wave-test-demand WaveTest.stochasticCorrelationShape
    populationAndSourceModelRequired refl true true true
demandFor WaveTest.cosmologicalPropagation =
  negative-g-wave-test-demand WaveTest.cosmologicalPropagation
    propagationAloneDoesNotIdentifyGSign refl false true false

------------------------------------------------------------------------
-- Finite observer collision: a coarse "GW test" label does not determine
-- whether source re-solving or propagation-only comparison is the live task.
------------------------------------------------------------------------

data WaveRoutingFixture : Set where
  inspiralFixture dispersionFixture : WaveRoutingFixture

data CoarseGWLabel : Set where
  gravitationalWaveTest : CoarseGWLabel

coarseWaveLabel : WaveRoutingFixture → CoarseGWLabel
coarseWaveLabel _ = gravitationalWaveTest

fixtureRole : WaveRoutingFixture → NegativeGWaveTestRole
fixtureRole inspiralFixture = requiresReSolvedSourceDynamics
fixtureRole dispersionFixture = propagationAloneDoesNotIdentifyGSign

coarseGWCollision :
  coarseWaveLabel inspiralFixture ≡ coarseWaveLabel dispersionFixture
coarseGWCollision = refl

coarseGWLabelDoesNotFixNegativeGProofTask :
  fixtureRole inspiralFixture ≡ fixtureRole dispersionFixture → ⊥
coarseGWLabelDoesNotFixNegativeGProofTask ()

record NegativeGWaveTestBoundary : Set where
  constructor negative-g-wave-test-boundary
  field
    everyGWTestDirectlyMeasuresMatterCouplingSign : Bool
    inspiralNegativeGTestRequiresReSolvedSourceDynamics : Bool
    vacuumDispersionTestAloneDeterminesGSign : Bool
    polarizationTestAloneDeterminesGSign : Bool
    stochasticCorrelationNeedsPopulationAndSourceModel : Bool
    currentGWAgreementAutomaticallyRulesOutEveryNegativeGConstruction : Bool
    currentGWAgreementConstrainsSelfConsistentNegativeGModels : Bool
    waveTestMustRespectGenerationPropagationSeparation : Bool

canonicalNegativeGWaveTestBoundary : NegativeGWaveTestBoundary
canonicalNegativeGWaveTestBoundary =
  negative-g-wave-test-boundary false true false false true false true true

existingSignedWaveBoundary : SignedWave.SignedGravitationalWaveBoundary
existingSignedWaveBoundary = SignedWave.canonicalSignedGravitationalWaveBoundary
