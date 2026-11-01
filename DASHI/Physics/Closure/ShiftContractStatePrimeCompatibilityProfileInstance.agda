module DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (canonicalShiftHeckeState; shiftPrimeEmbedding)
open import DASHI.Physics.Closure.TransportedPrimeCompatibilityProfile as TPCP
open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW
open import Ontology.Hecke.FactorVecDefectHistograms as FDH using (illegalCount)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FDOS
  using (DefectOrbitSummary; profileSummaryAt)
open import Ontology.Hecke.ForcedStableTransferBridge as FSTB

------------------------------------------------------------------------
-- Broader concrete carrier beyond ShiftGeoV:
-- use the full execution-contract state family for the shift contract, then
-- transport into ShiftGeoV through the existing canonical bridge.

ShiftContractState : Set
ShiftContractState =
  EC.Contract.State (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})

shiftContractStatePrimeImage : ShiftContractState → FactorVec
shiftContractStatePrimeImage x =
  shiftPrimeEmbedding (canonicalShiftHeckeState x)

shiftContractStatePrimeCompatibilityProfile :
  PCP.PrimeCompatibilityProfile ShiftContractState
shiftContractStatePrimeCompatibilityProfile =
  TPCP.transportedPrimeCompatibilityProfile shiftContractStatePrimeImage

shiftContractStateTransportedPrimeEmbedding : ShiftContractState → FactorVec
shiftContractStateTransportedPrimeEmbedding =
  PCP.PrimeCompatibilityProfile.primeEmbedding
    shiftContractStatePrimeCompatibilityProfile

shiftContractStateIllegalMask : ShiftContractState → SSP → SSP → Bool
shiftContractStateIllegalMask =
  PCP.PrimeCompatibilityProfile.illegalMask
    shiftContractStatePrimeCompatibilityProfile

shiftContractStateShiftWitness : ShiftContractState → SSP → CTSW.ShiftWitness
shiftContractStateShiftWitness =
  PCP.PrimeCompatibilityProfile.witness
    shiftContractStatePrimeCompatibilityProfile

shiftContractStateChamberToShiftWitnessBridge :
  CTSW.ChamberToShiftWitnessBridge ShiftContractState
shiftContractStateChamberToShiftWitnessBridge =
  PCP.PrimeCompatibilityProfile.witnessBridge
    shiftContractStatePrimeCompatibilityProfile

shiftContractStateIllegalCount≤forcedStableCountHist :
  ∀ x p →
  CTSW.illegalCount-chamber shiftContractStateChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist shiftContractStateChamberToShiftWitnessBridge x p
shiftContractStateIllegalCount≤forcedStableCountHist =
  CTSW.forcedStableTransfer shiftContractStateChamberToShiftWitnessBridge

shiftContractStateForcedStableTransferBridge :
  FSTB.ForcedStableTransferBridge ShiftContractState
shiftContractStateForcedStableTransferBridge =
  record
    { shiftImage = shiftContractStatePrimeImage
    ; illegalCountChamber = λ p x → FDH.illegalCount p (shiftContractStatePrimeImage x)
    ; illegalCount≤forcedStableCountHist = λ _ _ → ≤-refl
    }

shiftContractStateIllegalCount≤forcedStableCountOrbit :
  ∀ x p →
  FSTB.ForcedStableTransferBridge.illegalCountChamber
      shiftContractStateForcedStableTransferBridge p x
    ≤
  DefectOrbitSummary.forcedStableCount
    (profileSummaryAt p
      (FSTB.ForcedStableTransferBridge.shiftImage
        shiftContractStateForcedStableTransferBridge x))
shiftContractStateIllegalCount≤forcedStableCountOrbit x p =
  FSTB.ForcedStableTransferBridge.illegalCount≤forcedStableCountOrbit
    shiftContractStateForcedStableTransferBridge
    p
    x
