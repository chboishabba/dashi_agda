module DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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
    ; ShiftConeCompatible
    ; ShiftMotif
    ; ShiftCanonicalInBasin
    ; canonicalBasin
    ; canonicalShiftHeckeState
    ; shiftCoarse
    ; shiftCoarseAlt
    ; shiftCoarseAlt≡shiftCoarse
    ; shiftConePreservedLeft
    ; shiftConeTransportCoarseAlt
    ; shiftRGAdmissible
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

ShiftContractContinuumCarrier : Set
ShiftContractContinuumCarrier = GGC.Gauge × ShiftBasin × ShiftMotif

ShiftContractMdlRefinedContinuumCarrier : Set
ShiftContractMdlRefinedContinuumCarrier = GGC.Gauge × ShiftBasin × Nat × ShiftMotif

projectObservableMotif :
  ShiftContractObservable → ShiftContractContinuumCarrier
projectObservableMotif (g , o) =
  ( g
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.motifClass o
  )

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

shiftContractScheduledObservable :
  ShiftContractState → ShiftContractObservable
shiftContractScheduledObservable x =
  GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState (shiftCoarseAlt x))

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
    ; continuumLift = shiftContractScheduledObservable
    ; pickGauge = λ _ → GGC.SU3×SU2×U1
    }

shiftCoarseAlt-preserve-evolve :
  ∀ x →
  shiftCoarseAlt (EC.Contract.step ShiftC x) ≡ shiftCoarseAlt x
shiftCoarseAlt-preserve-evolve x =
  trans
    (SRGOI.shiftCoarseAltStep-commute x)
    (cong (EC.Contract.step ShiftC) (SRGOI.shiftCoarseFixed x))

shiftCoarseAlt-preserve-coarse :
  ∀ x →
  shiftCoarseAlt (shiftCoarse x) ≡ shiftCoarseAlt x
shiftCoarseAlt-preserve-coarse x =
  cong (EC.Contract.step ShiftC) (SRGOI.shiftCoarse-idem x)

shiftCoarseAlt-preserve-offset :
  ∀ x →
  shiftCoarseAlt (shiftCoarseAlt x) ≡ shiftCoarseAlt x
shiftCoarseAlt-preserve-offset x =
  trans
    (shiftCoarseAlt-preserve-evolve (shiftCoarse x))
    (shiftCoarseAlt-preserve-coarse x)

shiftContractObservableContinuumScale :
  ShiftContractState → ShiftContractContinuumCarrier
shiftContractObservableContinuumScale x =
  projectObservableMotif (shiftContractScheduledObservable x)

shiftContractObservableMdlRefinedContinuumScale :
  ShiftContractState → ShiftContractMdlRefinedContinuumCarrier
shiftContractObservableMdlRefinedContinuumScale x =
  ( GGC.SU3×SU2×U1
  , RGOI.RGObservable.basinLabel
      (observeOnGeo (canonicalShiftHeckeState (shiftCoarseAlt x)))
  , RGOI.RGObservable.mdlLevel
      (observeOnGeo (canonicalShiftHeckeState (shiftCoarseAlt x)))
  , RGOI.RGObservable.motifClass
      (observeOnGeo (canonicalShiftHeckeState (shiftCoarseAlt x)))
  )

shiftContractObservableContinuumWitness :
  AGMB.ContinuumWitness shiftContractObservableBundle
shiftContractObservableContinuumWitness =
  record
    { LimitCarrier = ShiftContractContinuumCarrier
    ; LimitObservable = ⊤
    ; scaleToLimit = projectObservableMotif
    ; limitObservable = λ _ → tt
    ; observableProjection = λ _ → tt
    ; limitCone = λ _ → ⊤
    ; limitMdl = λ _ → zero
    ; scaleFromCarrier = shiftContractObservableContinuumScale
    ; continuum-compatible = λ _ → refl
    ; continuum-cone-compatible = λ _ _ → tt
    ; continuum-mdl-compatible = λ _ → refl
    ; scale-lift-compatible = λ _ → refl
    ; scale-preserve-evolve =
        λ x →
          cong
            (λ s →
              projectObservableMotif
                (GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState s)))
            (shiftCoarseAlt-preserve-evolve x)
    ; scale-preserve-coarse =
        λ x →
          cong
            (λ s →
              projectObservableMotif
                (GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState s)))
            (shiftCoarseAlt-preserve-coarse x)
    ; scale-preserve-offset =
        λ x →
          cong
            (λ s →
              projectObservableMotif
                (GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState s)))
            (shiftCoarseAlt-preserve-offset x)
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

shiftContractObservableReplayTransportWitness :
  AGMB.ObservableTransportWitness shiftContractObservableBundle
shiftContractObservableReplayTransportWitness =
  record
    { TargetCarrier = ShiftContractState
    ; observeTarget = AGMB.observableOf shiftContractObservableBundle
    ; transport = λ x → x
    ; transport-sound = λ _ _ → refl
    }

shiftContractTransportedProjectionDeltaWitness :
  AGMB.TransportedProjectionDeltaWitness shiftContractObservableBundle
shiftContractTransportedProjectionDeltaWitness =
  record
    { transportW = shiftContractObservableReplayTransportWitness
    ; admissibleT = shiftRGAdmissible
    ; projectAT = λ x → shiftCoarse (EC.Contract.step ShiftC x)
    ; projectBT = shiftCoarseAlt
    ; coneT = ShiftConeCompatible
    ; cone-projectAT = shiftConePreservedLeft
    ; cone-projectBT = λ x _ cx → shiftConeTransportCoarseAlt x cx
    ; universalityT =
        λ x _ →
          cong
            (AGMB.observableOf shiftContractObservableBundle)
            (sym (shiftCoarseAlt≡shiftCoarse x))
    }

shiftContractTransportedProjectionDeltaCompatibility :
  RGOI.ProjectionDeltaCompatibility
    ShiftContractState
    ShiftContractObservable
    _≡_
shiftContractTransportedProjectionDeltaCompatibility =
  AGMB.toTransportedProjectionDeltaCompatibility
    shiftContractObservableBundle
    shiftContractTransportedProjectionDeltaWitness

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
