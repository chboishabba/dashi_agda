module DASHI.Biology.LogisticAgenticPrebioticCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.LogisticPopulationDirectionalEvidenceExact as Logistic
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Biology.AgenticMaterialsControlCore as Agentic
import DASHI.Biology.Physical.PhysicalOriginsLadderExact as Origins
import DASHI.Biology.Physical.AbiogenesisInevitabilityBoundaryExact as Abiogenesis
import DASHI.Biology.PrebioticChemistryLifeInevitabilityBidiExact as Prebiotic

------------------------------------------------------------------------
-- LOGISTIC / AGENTIC-MATERIAL / PREBIOTIC-CHEMISTRY CROSS-POLLINATION
--
-- The shared structure is deliberately limited:
--   * a population or replicator abundance can change under resource pressure;
--   * chemistry supplies reaction-network / material-throughput coordinates;
--   * self-amplification can occur before corrective agency;
--   * a coarse growth trit never supplies the missing agency/abiogenesis
--     coordinates.
--
-- No claim is made that the logistic map is a universal law of autocatalytic
-- chemistry, protocells, agentic materials, or abiogenesis.
------------------------------------------------------------------------

record ReplicationEnvironmentState : Set where
  constructor replication-environment-state
  field
    population : Natural.LogisticPopulationState
    chemicalStage : Prebiotic.ChemicalOrganisationStage
    originStage : Agentic.OriginStage
    availableMaterial : Nat
    environmentReference : String

open ReplicationEnvironmentState public

populationDirection : ReplicationEnvironmentState → DASHI.Algebra.Trit.Trit
populationDirection state = Logistic.growthDirection (population state)

------------------------------------------------------------------------
-- Existing theorem-bearing receipts reused directly.
------------------------------------------------------------------------

replicationCanPrecedeAgency :
  Origins.selfAmplification
    (Origins.capabilities Agentic.autocatalyticNetwork)
  ≡ true
replicationCanPrecedeAgency = Origins.replicationAppearsBeforeAgency

autocatalysisNeedNotHaveCorrectiveFeedback :
  Origins.correctiveFeedback
    (Origins.capabilities Agentic.autocatalyticNetwork)
  ≡ false
autocatalysisNeedNotHaveCorrectiveFeedback =
  Origins.autocatalysisLacksCorrectiveTarget

replicationAndVariationDoNotForceAgency :
  Abiogenesis.selfAmplifying Abiogenesis.replicatorWithoutAgency ≡ true
  × Abiogenesis.heritableVariation Abiogenesis.replicatorWithoutAgency ≡ true
  × Abiogenesis.correctiveFeedback Abiogenesis.replicatorWithoutAgency ≡ false
replicationAndVariationDoNotForceAgency =
  Abiogenesis.replicationAndVariationDoNotForceAgency

------------------------------------------------------------------------
-- Chemistry/resource coupling fixture.
-- NaturalSystemsHyperfabricExact already owns a finite reaction state in which
-- one reaction step increases activator/inhibitor counts while consuming one
-- unit of available material.  We reuse that exact state transition instead of
-- inventing a parallel resource model.
------------------------------------------------------------------------

canonicalResourceLimitedReaction :
  Natural.reactionStep (Natural.activatorInhibitorState 0 0 3)
  ≡ Natural.activatorInhibitorState 1 1 2
canonicalResourceLimitedReaction = Natural.canonicalReactionStep

record LogisticReplicationResourceBridge : Set₁ where
  constructor logistic-replication-resource-bridge
  field
    populationState : Natural.LogisticPopulationState
    reactionState : Natural.ActivatorInhibitorState
    growthResidual : Logistic.LogisticGrowthResidual

    reactionNetworkReference : String
    resourceLimitationReference : String
    replicationReference : String
    statisticalEvidenceReference : String

    logisticGrowthIsOnlyPopulationCoordinate : Bool
    logisticGrowthIsOnlyPopulationCoordinateIsTrue :
      logisticGrowthIsOnlyPopulationCoordinate ≡ true

    chemicalResourceStateRemainsExplicit : Bool
    chemicalResourceStateRemainsExplicitIsTrue :
      chemicalResourceStateRemainsExplicit ≡ true

    agencyRequiresAdditionalClosedLoopReceipt : Bool
    agencyRequiresAdditionalClosedLoopReceiptIsTrue :
      agencyRequiresAdditionalClosedLoopReceipt ≡ true

    abiogenesisRequiresAdditionalPathEnvironmentReceipts : Bool
    abiogenesisRequiresAdditionalPathEnvironmentReceiptsIsTrue :
      abiogenesisRequiresAdditionalPathEnvironmentReceipts ≡ true

open LogisticReplicationResourceBridge public

------------------------------------------------------------------------
-- Origins-of-life / agentic-material firewalls.
------------------------------------------------------------------------

data PositiveLogisticGrowthMeansAutocatalysisPermission : Set where

data PositiveLogisticGrowthMeansAgencyPermission : Set where

data PositiveLogisticGrowthMeansAbiogenesisPermission : Set where

data ResourceConsumptionMeansMetabolismPermission : Set where

data AutocatalysisMeansLifePermission : Set where

data ReplicationMeansOpenEndedEvolutionPermission : Set where

positiveLogisticGrowthDoesNotProveAutocatalysis :
  PositiveLogisticGrowthMeansAutocatalysisPermission → ⊥
positiveLogisticGrowthDoesNotProveAutocatalysis ()

positiveLogisticGrowthDoesNotProveAgency :
  PositiveLogisticGrowthMeansAgencyPermission → ⊥
positiveLogisticGrowthDoesNotProveAgency ()

positiveLogisticGrowthDoesNotProveAbiogenesis :
  PositiveLogisticGrowthMeansAbiogenesisPermission → ⊥
positiveLogisticGrowthDoesNotProveAbiogenesis ()

resourceConsumptionDoesNotByItselfProveMetabolism :
  ResourceConsumptionMeansMetabolismPermission → ⊥
resourceConsumptionDoesNotByItselfProveMetabolism ()

autocatalysisDoesNotByItselfProveLife :
  AutocatalysisMeansLifePermission → ⊥
autocatalysisDoesNotByItselfProveLife ()

replicationDoesNotByItselfProveOpenEndedEvolution :
  ReplicationMeansOpenEndedEvolutionPermission → ⊥
replicationDoesNotByItselfProveOpenEndedEvolution ()

------------------------------------------------------------------------
-- Shared residual law across the three domains.
------------------------------------------------------------------------

record ReplicationResidualCoordinates : Set₁ where
  constructor replication-residual-coordinates
  field
    PopulationState : Set
    ChemicalState : Set
    AgencyState : Set
    HistoricalPath : Set

    populationResidualReference : String
    chemicalResidualReference : String
    agencyResidualReference : String
    historicalPathReference : String

open ReplicationResidualCoordinates public

record LogisticAgenticPrebioticBoundary : Set where
  constructor logistic-agentic-prebiotic-boundary
  field
    logisticGrowthMayModelReplicationPressure : Bool
    logisticGrowthUniversallyModelsPrebioticChemistry : Bool
    replicationCanPrecedeCorrectiveAgency : Bool
    resourceStateMustRemainExplicit : Bool
    agencyStateMustRemainExplicit : Bool
    historicalPathMustRemainExplicit : Bool
    positiveGrowthProvesAbiogenesis : Bool
    autocatalysisProvesLife : Bool

canonicalLogisticAgenticPrebioticBoundary :
  LogisticAgenticPrebioticBoundary
canonicalLogisticAgenticPrebioticBoundary =
  logistic-agentic-prebiotic-boundary
    true false true true true true false false
