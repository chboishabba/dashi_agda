module DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.StoichiometricConservation as Conservation
import DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact as DeepTime
import DASHI.Core.TrajectoryResidueExact as Residue

------------------------------------------------------------------------
-- DEEP-TIME CARBON RESERVOIR / FLUX BALANCE
--
-- The deep-time lineage is supplemented here by an explicit finite reservoir
-- ledger.  Internal Earth-system redistribution is distinguished from the
-- open-balance view of a chosen subsystem: combustion does not create carbon
-- in the larger ledger, even though it can be an external positive flux for
-- the atmospheric subsystem.
------------------------------------------------------------------------

data CarbonReservoir : Set where
  atmosphericReservoir
  oceanReservoir
  biosphereReservoir
  sedimentReservoir
  fossilReservoir
  : CarbonReservoir

record CarbonLedger : Set where
  constructor carbon-ledger
  field
    atmosphericCarbon : Nat
    oceanCarbon : Nat
    biosphereCarbon : Nat
    sedimentCarbon : Nat
    fossilCarbon : Nat

open CarbonLedger public

totalCarbon : CarbonLedger → Nat
totalCarbon ledger =
  atmosphericCarbon ledger +
  oceanCarbon ledger +
  biosphereCarbon ledger +
  sedimentCarbon ledger +
  fossilCarbon ledger

------------------------------------------------------------------------
-- Finite exact trajectory.  Values are dimensionless bookkeeping units only;
-- they do not claim measured global reservoir sizes.
------------------------------------------------------------------------

deepStoredState : CarbonLedger
deepStoredState = carbon-ledger 0 0 1 1 3

afterOneCombustionTransfer : CarbonLedger
afterOneCombustionTransfer = carbon-ledger 1 0 1 1 2

afterOneOceanUptakeTransfer : CarbonLedger
afterOneOceanUptakeTransfer = carbon-ledger 0 1 1 1 2

afterOneBiosphereUptakeTransfer : CarbonLedger
afterOneBiosphereUptakeTransfer = carbon-ledger 0 0 2 1 2

combustionFixtureConservesTotal :
  totalCarbon deepStoredState ≡ totalCarbon afterOneCombustionTransfer
combustionFixtureConservesTotal = refl

oceanUptakeFixtureConservesTotal :
  totalCarbon afterOneCombustionTransfer ≡ totalCarbon afterOneOceanUptakeTransfer
oceanUptakeFixtureConservesTotal = refl

biosphereUptakeFixtureConservesTotal :
  totalCarbon afterOneCombustionTransfer ≡ totalCarbon afterOneBiosphereUptakeTransfer
biosphereUptakeFixtureConservesTotal = refl

------------------------------------------------------------------------
-- Application-level transfer receipts.  A real quantified application must
-- provide a conservation equation for its stated system boundary rather than
-- assuming one from a source/sink label.
------------------------------------------------------------------------

record CarbonTransferReceipt : Set where
  constructor carbon-transfer-receipt
  field
    source : CarbonReservoir
    sink : CarbonReservoir
    before : CarbonLedger
    after : CarbonLedger
    transferAmountReference : String
    processReference : String
    systemBoundaryReference : String
    conservation : totalCarbon before ≡ totalCarbon after
    provenanceReference : String
    validationReference : String

record ResidenceTimeReceipt : Set where
  constructor residence-time-receipt
  field
    reservoir : CarbonReservoir
    stockReference : String
    outflowReference : String
    averagingWindowReference : String
    steadyStateAssumptionReference : String
    residenceTimeCalculationReference : String
    provenanceReference : String
    validationReference : String

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

deepTimeBoundary : DeepTime.DeepTimeCarbonBiosphereFossilFuelBoundary
deepTimeBoundary = DeepTime.canonicalDeepTimeCarbonBiosphereFossilFuelBoundary

record DeepTimeCarbonReservoirFluxBoundary : Set where
  constructor deep-time-carbon-reservoir-flux-boundary
  field
    combustionCreatesCarbonInClosedLedger : Bool
    combustionCreatesCarbonInClosedLedgerIsFalse :
      combustionCreatesCarbonInClosedLedger ≡ false
    combustionCanBePositiveAtmosphericSubsystemFlux : Bool
    combustionCanBePositiveAtmosphericSubsystemFluxIsTrue :
      combustionCanBePositiveAtmosphericSubsystemFlux ≡ true
    atmosphericIncreaseDeterminesUniqueSourceReservoir : Bool
    atmosphericIncreaseDeterminesUniqueSourceReservoirIsFalse :
      atmosphericIncreaseDeterminesUniqueSourceReservoir ≡ false
    equalTotalCarbonImpliesEqualReservoirDistribution : Bool
    equalTotalCarbonImpliesEqualReservoirDistributionIsFalse :
      equalTotalCarbonImpliesEqualReservoirDistribution ≡ false
    reservoirInventoryAloneDeterminesResidenceTime : Bool
    reservoirInventoryAloneDeterminesResidenceTimeIsFalse :
      reservoirInventoryAloneDeterminesResidenceTime ≡ false
    residenceTimeNeedsStockFlowAndBoundaryReceipts : Bool
    residenceTimeNeedsStockFlowAndBoundaryReceiptsIsTrue :
      residenceTimeNeedsStockFlowAndBoundaryReceipts ≡ true
    trajectoryHistoryMayMatterDespiteEqualPresentTotals : Bool
    trajectoryHistoryMayMatterDespiteEqualPresentTotalsIsTrue :
      trajectoryHistoryMayMatterDespiteEqualPresentTotals ≡ true
    reading : String

canonicalDeepTimeCarbonReservoirFluxBoundary :
  DeepTimeCarbonReservoirFluxBoundary
canonicalDeepTimeCarbonReservoirFluxBoundary =
  deep-time-carbon-reservoir-flux-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    "Carbon-cycle bookkeeping distinguishes redistribution inside a declared closed ledger from flux into or out of a selected subsystem. Equal conserved totals need not imply equal reservoir distributions, provenance, residence times or ecological consequences. Residence-time claims require explicit stock, outflow, averaging-window and system-boundary receipts."
