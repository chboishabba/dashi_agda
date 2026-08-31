module DASHI.Biology.ClimateRateRecoveryIrreversibilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Ecology.EcologicalInteractionDynamics as Ecology
import DASHI.Biology.BiologicalRecoveryBoundary as Recovery
import DASHI.Biology.Evolution.EvolutionaryGenomeTopologyIrreversibilityExact as EvolutionaryIrreversibility
import DASHI.Chemistry.CarbonForcingRateBidiExact as Rate
import DASHI.Chemistry.DeepTimeCarbonPathResidualBidiExact as CarbonPath
import DASHI.Planning.IrreversibleActionConsentReopeningGateExact as IrreversiblePlanning
import DASHI.Core.TrajectoryResidueExact as Residue

------------------------------------------------------------------------
-- CLIMATE RATE / ECOLOGICAL RECOVERY / IRREVERSIBILITY BIDI
--
-- Restoring one coarse environmental coordinate or reservoir endpoint does not
-- definitionally restore an earlier ecosystem. Recovery is separately witnessed
-- and can fail because history-dependent residues, lost populations, altered
-- niches or non-reversible transitions remain. This is a finite structural
-- fixture; real ecological recovery claims require empirical calibration.
------------------------------------------------------------------------

data EcosystemRecoveryState : Set where
  baselineSystem
  perturbedRecoverableSystem
  restoredClimateButAlteredSystem
  : EcosystemRecoveryState

data ClimateShadow : Set where
  baselineLikeClimate : ClimateShadow

climateShadow : EcosystemRecoveryState → ClimateShadow
climateShadow _ = baselineLikeClimate

data EcologicalHistoryResidue : Set where
  noDamageResidue damageHistoryRetained : EcologicalHistoryResidue

historyResidue : EcosystemRecoveryState → EcologicalHistoryResidue
historyResidue baselineSystem = noDamageResidue
historyResidue perturbedRecoverableSystem = damageHistoryRetained
historyResidue restoredClimateButAlteredSystem = damageHistoryRetained

baselineAndRestoredShareCoarseClimate :
  climateShadow baselineSystem ≡ climateShadow restoredClimateButAlteredSystem
baselineAndRestoredShareCoarseClimate = refl

baselineAndRestoredRetainDifferentHistory :
  historyResidue baselineSystem ≡ historyResidue restoredClimateButAlteredSystem → ⊥
baselineAndRestoredRetainDifferentHistory ()

data RecoveryStatus : Set where
  recoveredToPriorSystem notRecoveredToPriorSystem : RecoveryStatus

recoveryStatus : EcosystemRecoveryState → RecoveryStatus
recoveryStatus baselineSystem = recoveredToPriorSystem
recoveryStatus perturbedRecoverableSystem = notRecoveredToPriorSystem
recoveryStatus restoredClimateButAlteredSystem = notRecoveredToPriorSystem

restoredClimateShadowDoesNotProveEcologicalRecovery :
  recoveryStatus baselineSystem ≡ recoveryStatus restoredClimateButAlteredSystem → ⊥
restoredClimateShadowDoesNotProveEcologicalRecovery ()

record EcologicalRecoveryReceipt : Set where
  constructor ecological-recovery-receipt
  field
    ecosystemReference : String
    prePerturbationReference : String
    perturbationReference : String
    forcingRateReference : String
    recoveryTargetReference : String
    populationReference : String
    communityCompositionReference : String
    habitatNicheReference : String
    functionalReference : String
    trajectoryHistoryReference : String
    recoveryTimescaleReference : String
    validationReference : String

rateBoundary : Rate.CarbonForcingRateBoundary
rateBoundary = Rate.canonicalCarbonForcingRateBoundary

carbonPathBoundary : CarbonPath.DeepTimeCarbonPathResidualBoundary
carbonPathBoundary = CarbonPath.canonicalDeepTimeCarbonPathResidualBoundary

irreversiblePlanningBoundary : IrreversiblePlanning.IrreversibleActionBoundary
irreversiblePlanningBoundary = IrreversiblePlanning.canonicalIrreversibleActionBoundary

record ClimateRateRecoveryIrreversibilityBoundary : Set where
  constructor climate-rate-recovery-irreversibility-boundary
  field
    restoredClimateCoordinateImpliesRestoredEcosystem : Bool
    restoredClimateCoordinateImpliesRestoredEcosystemIsFalse :
      restoredClimateCoordinateImpliesRestoredEcosystem ≡ false
    equalFinalCarbonLedgerImpliesEqualRecoveryState : Bool
    equalFinalCarbonLedgerImpliesEqualRecoveryStateIsFalse :
      equalFinalCarbonLedgerImpliesEqualRecoveryState ≡ false
    forcingRateCanMatterEvenAtEqualCumulativeTransfer : Bool
    forcingRateCanMatterEvenAtEqualCumulativeTransferIsTrue :
      forcingRateCanMatterEvenAtEqualCumulativeTransfer ≡ true
    ecologicalRecoveryNeedsIndependentWitness : Bool
    ecologicalRecoveryNeedsIndependentWitnessIsTrue :
      ecologicalRecoveryNeedsIndependentWitness ≡ true
    historyResidueCanBlockNaiveReverseInference : Bool
    historyResidueCanBlockNaiveReverseInferenceIsTrue :
      historyResidueCanBlockNaiveReverseInference ≡ true
    irreversibleOrNonSubstitutableImpactNeedsReopeningOnMaterialEvidenceChange : Bool
    irreversibleOrNonSubstitutableImpactNeedsReopeningOnMaterialEvidenceChangeIsTrue :
      irreversibleOrNonSubstitutableImpactNeedsReopeningOnMaterialEvidenceChange ≡ true
    reading : String

canonicalClimateRateRecoveryIrreversibilityBoundary :
  ClimateRateRecoveryIrreversibilityBoundary
canonicalClimateRateRecoveryIrreversibilityBoundary =
  climate-rate-recovery-irreversibility-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    "Climate/ecological recovery is not the inverse of perturbation by definition. Equal cumulative forcing or restored coarse climate coordinates may coexist with different exposure histories, population/community states and reachable futures. Recovery therefore requires a separate ecological witness, while materially changed evidence reopens decisions involving irreversible or non-substitutable impacts."
