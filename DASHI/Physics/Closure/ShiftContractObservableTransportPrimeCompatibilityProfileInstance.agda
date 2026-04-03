module DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Product using (_,_; _×_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.ObservableTransportPrimeCompatibilityProfile as OTPCP
open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using
    ( ShiftBasin
    ; ShiftMotif
    ; ShiftCanonicalInBasin
    ; canonicalBasin
    ; canonicalShiftHeckeState
    ; shiftPipeline
    ; shiftPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    ; shiftContractStateIllegalCount≤forcedStableCountHist
    )
open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

------------------------------------------------------------------------
-- Noncanonical replay of the observable-transport/prime-compatibility stack:
-- use the full shift execution-contract state carrier, then transport to
-- ShiftGeoV and lift back through ObservableTransportPrimeCompatibilityProfile.

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

ShiftContractObservable : Set
ShiftContractObservable = GGC.Gauge × RGOI.RGObservable ShiftBasin ShiftMotif

signatureOnGeo : SLEI.ShiftGeoV → HS.Sig15
signatureOnGeo x =
  HS.scanOn
    (PHEM.PrimeHeckeEigenMotifPipelineOn.hecke shiftPipeline)
    x

eigenOnGeo : SLEI.ShiftGeoV → PHEM.EigenProfile
eigenOnGeo x =
  PHEM.PrimeHeckeEigenMotifPipelineOn.signatureEigenProfile
    shiftPipeline
    (signatureOnGeo x)

motifOnGeo : SLEI.ShiftGeoV → ShiftMotif
motifOnGeo x =
  PHEM.PrimeHeckeEigenMotifPipelineOn.motifOf
    shiftPipeline
    (eigenOnGeo x)

observeOnGeo : SLEI.ShiftGeoV → RGOI.RGObservable ShiftBasin ShiftMotif
observeOnGeo x =
  RGOI.rgObservable
    zero
    canonicalBasin
    (signatureOnGeo x)
    (eigenOnGeo x)
    (motifOnGeo x)

shiftContractObservableBundle : AGMB.AbstractGaugeMatterBundle
shiftContractObservableBundle =
  record
    { Carrier = ShiftContractState
    ; GaugeFiber = GGC.Gauge
    ; MatterField = ShiftContractObservable
    ; Observable = ShiftContractObservable
    ; ContinuumField = ShiftContractObservable
    ; evolve = EC.Contract.step ShiftC
    ; coarse = SRGOI.shiftCoarse
    ; offset = SRGOI.shiftCoarseAlt
    ; admissible = λ _ → true
    ; coneWitness = SRGOI.ShiftCanonicalInBasin
    ; mdlLevel = λ _ → zero
    ; gaugeAction = λ _ x → x
    ; matterOf = λ x → GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState x)
    ; observableOf = λ x → GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState x)
    ; continuumLift = λ x → GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState x)
    ; pickGauge = λ _ → GGC.SU3×SU2×U1
    }

shiftContractObservableTransportWitness :
  AGMB.ObservableTransportWitness shiftContractObservableBundle
shiftContractObservableTransportWitness =
  record
    { TargetCarrier = SLEI.ShiftGeoV
    ; observeTarget = λ x → GGC.SU3×SU2×U1 , observeOnGeo x
    ; transport = canonicalShiftHeckeState
    ; transport-sound = λ _ _ → refl
    }

shiftContractObservablePrimeCompatibilityProfile :
  PCP.PrimeCompatibilityProfile ShiftContractState
shiftContractObservablePrimeCompatibilityProfile =
  OTPCP.observableTransportPrimeCompatibilityProfile
    shiftContractObservableBundle
    shiftContractObservableTransportWitness
    shiftPrimeEmbedding

shiftContractObservablePrimeEmbedding : ShiftContractState → FactorVec
shiftContractObservablePrimeEmbedding =
  PCP.PrimeCompatibilityProfile.primeEmbedding
    shiftContractObservablePrimeCompatibilityProfile

shiftContractObservablePrimeEmbedding≡transported :
  ∀ x →
  shiftContractObservablePrimeEmbedding x
    ≡
  shiftContractStateTransportedPrimeEmbedding x
shiftContractObservablePrimeEmbedding≡transported _ = refl

shiftContractObservableIllegalMask : ShiftContractState → SSP → SSP → Bool
shiftContractObservableIllegalMask =
  PCP.PrimeCompatibilityProfile.illegalMask
    shiftContractObservablePrimeCompatibilityProfile

shiftContractObservableShiftWitness :
  ShiftContractState → SSP → CTSW.ShiftWitness
shiftContractObservableShiftWitness =
  PCP.PrimeCompatibilityProfile.witness
    shiftContractObservablePrimeCompatibilityProfile

shiftContractObservableChamberToShiftWitnessBridge :
  CTSW.ChamberToShiftWitnessBridge ShiftContractState
shiftContractObservableChamberToShiftWitnessBridge =
  PCP.PrimeCompatibilityProfile.witnessBridge
    shiftContractObservablePrimeCompatibilityProfile

shiftContractObservableIllegalCount≤forcedStableCountHist :
  ∀ x p →
  CTSW.illegalCount-chamber
    shiftContractObservableChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist
    shiftContractObservableChamberToShiftWitnessBridge x p
shiftContractObservableIllegalCount≤forcedStableCountHist =
  CTSW.forcedStableTransfer
    shiftContractObservableChamberToShiftWitnessBridge

shiftContractObservableIllegalCount≤transported :
  ∀ x p →
  CTSW.illegalCount-chamber
    shiftContractObservableChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist
    shiftContractObservableChamberToShiftWitnessBridge x p
shiftContractObservableIllegalCount≤transported x p
  rewrite shiftContractObservablePrimeEmbedding≡transported x =
  shiftContractStateIllegalCount≤forcedStableCountHist x p
