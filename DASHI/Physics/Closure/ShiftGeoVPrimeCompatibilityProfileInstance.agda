module DASHI.Physics.Closure.ShiftGeoVPrimeCompatibilityProfileInstance where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW
open import Ontology.Hecke.ForcedStableTransferBridge as FSTB
open import Ontology.Hecke.FactorVecDefectHistograms as FDH using (illegalCount)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FDOS
  using (DefectOrbitSummary; profileSummaryAt)

open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.TransportedPrimeCompatibilityProfile as TPCP
open import DASHI.Physics.Closure.ShiftExecutionInvariantCore as SEIC
  using (ShiftGeoV; shiftPrimeEmbedding)

------------------------------------------------------------------------
-- First broader concrete carrier beyond the tiny canonical CR/CP/CC case:
-- use the full shift geometry carrier directly, together with its existing
-- prime-address embedding.

shiftGeoVPrimeCompatibilityProfile : PCP.PrimeCompatibilityProfile ShiftGeoV
shiftGeoVPrimeCompatibilityProfile =
  TPCP.transportedPrimeCompatibilityProfile shiftPrimeEmbedding

shiftGeoVTransportedPrimeEmbedding : ShiftGeoV → FactorVec
shiftGeoVTransportedPrimeEmbedding =
  PCP.PrimeCompatibilityProfile.primeEmbedding
    shiftGeoVPrimeCompatibilityProfile

shiftGeoVIllegalMask : ShiftGeoV → SSP → SSP → Bool
shiftGeoVIllegalMask =
  PCP.PrimeCompatibilityProfile.illegalMask
    shiftGeoVPrimeCompatibilityProfile

shiftGeoVShiftWitness : ShiftGeoV → SSP → CTSW.ShiftWitness
shiftGeoVShiftWitness =
  PCP.PrimeCompatibilityProfile.witness
    shiftGeoVPrimeCompatibilityProfile

shiftGeoVChamberToShiftWitnessBridge :
  CTSW.ChamberToShiftWitnessBridge ShiftGeoV
shiftGeoVChamberToShiftWitnessBridge =
  PCP.PrimeCompatibilityProfile.witnessBridge
    shiftGeoVPrimeCompatibilityProfile

shiftGeoVIllegalCount≤forcedStableCountHist :
  ∀ x p →
  CTSW.illegalCount-chamber shiftGeoVChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist shiftGeoVChamberToShiftWitnessBridge x p
shiftGeoVIllegalCount≤forcedStableCountHist =
  CTSW.forcedStableTransfer shiftGeoVChamberToShiftWitnessBridge

shiftGeoVForcedStableTransferBridge :
  FSTB.ForcedStableTransferBridge ShiftGeoV
shiftGeoVForcedStableTransferBridge =
  record
    { shiftImage = shiftPrimeEmbedding
    ; illegalCountChamber = λ p x → FDH.illegalCount p (shiftPrimeEmbedding x)
    ; illegalCount≤forcedStableCountHist = λ _ _ → ≤-refl
    }

shiftGeoVIllegalCount≤forcedStableCountOrbit :
  ∀ x p →
  FSTB.ForcedStableTransferBridge.illegalCountChamber
      shiftGeoVForcedStableTransferBridge p x
    ≤
  DefectOrbitSummary.forcedStableCount
    (profileSummaryAt p
      (FSTB.ForcedStableTransferBridge.shiftImage
        shiftGeoVForcedStableTransferBridge x))
shiftGeoVIllegalCount≤forcedStableCountOrbit x p =
  FSTB.ForcedStableTransferBridge.illegalCount≤forcedStableCountOrbit
    shiftGeoVForcedStableTransferBridge
    p
    x
