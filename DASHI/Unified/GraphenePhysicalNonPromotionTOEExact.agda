module DASHI.Unified.GraphenePhysicalNonPromotionTOEExact where

-- TOE bridge. Reuse exact owners. Keep physical objects and sources distinct.
-- Original graphene theory: Bistritzer--MacDonald and Cao et al.
-- Original Fe5GeTe2 observation: Gao et al.
-- DASHI owns this import weld, not the cited physical claims.
-- Existing numerical replays are not experimental measurements.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)\nopen import Data.Empty using (⊥-elim)

import DASHI.Physics.CondensedMatter.FlatBandTwistronicsFe5GeTe2CrossPollinationExact as Graphene
import DASHI.Physics.CondensedMatter.FlatBandObservableFibreExact as Fibre
import DASHI.Physics.Foundations.FieldGeometryMatterTerminalExecutionAddendumExact as Physical
import DASHI.Physics.Foundations.FieldGeometryMatterTerminalExecutionAddendumValidation as PhysicalProof

-- A genuine theorem is reused by its proof term, not by a Boolean receipt.
flatBandConsumerCannotDescendThroughCoarseEnergy :
  {Momentum Energy Order : Set} →
  (band : Fibre.BandSystem Momentum Energy) →
  (order : Momentum → Order) →
  Fibre.FlatBandPhaseSplitWitness band order →
  Fibre.PhaseDescendsThroughEnergy band order →
  Agda.Builtin.Equality._≡_ false true
flatBandConsumerCannotDescendThroughCoarseEnergy band order witness descent =
  ⊥-elim (Graphene.flatPairSplitByOrderRequiresMoreThanEnergy band order witness descent)

-- The existing physical validation theorems are the proof owners.
syntheticQTMRemainsNonPromoting :
  Physical.qtmSyntheticForwardObserverCountsAsExperimentalFit
    Physical.currentTerminalExecutionAddendum ≡ false
syntheticQTMRemainsNonPromoting =
  PhysicalProof.synthetic-qtm-forward-observer-is-not-experimental-fit

syntheticMaxwellRemainsNonPromoting :
  Physical.entropyMaxwellSyntheticFixtureCountsAsMeasuredReplay
    Physical.currentTerminalExecutionAddendum ≡ false
syntheticMaxwellRemainsNonPromoting =
  PhysicalProof.synthetic-maxwell-is-not-measured-replay

positiveEulerianRemainsNonPromoting :
  Physical.positiveEulerianEnergyCountsAsFullWEC
    Physical.currentTerminalExecutionAddendum ≡ false
positiveEulerianRemainsNonPromoting =
  PhysicalProof.positive-eulerian-energy-is-not-full-wec

grapheneIsSamePhysicalObjectAsIron : Bool
grapheneIsSamePhysicalObjectAsIron =
  Graphene.grapheneFlatBandIdentifiedWithFeFlatBandSameObject
    Graphene.canonicalGrapheneFe5GeTe2CrossPollinationBoundary

syntheticQTMCountsAsMeasuredFit : Bool
syntheticQTMCountsAsMeasuredFit =
  Physical.qtmSyntheticForwardObserverCountsAsExperimentalFit
    Physical.currentTerminalExecutionAddendum

syntheticMaxwellCountsAsMeasuredEntropy : Bool
syntheticMaxwellCountsAsMeasuredEntropy =
  Physical.entropyMaxwellSyntheticFixtureCountsAsMeasuredReplay
    Physical.currentTerminalExecutionAddendum

positiveEulerianCountsAsFullWEC : Bool
positiveEulerianCountsAsFullWEC =
  Physical.positiveEulerianEnergyCountsAsFullWEC
    Physical.currentTerminalExecutionAddendum

grapheneSourceAttributionRetained : Bool
grapheneSourceAttributionRetained =
  Graphene.bistritzerMacDonaldMagicAngleSourceRetained
    Graphene.canonicalGrapheneFe5GeTe2CrossPollinationBoundary
