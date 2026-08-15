module DASHI.Physics.YangMills.BalabanClayGate4LightweightPolymerRGHandoffExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- PURPOSE
--
-- Lightweight Gate-4 handoff for the Agda 2.9 audit.  This module does not
-- import BalabanPolymerDiameterEntropy, StepVAssemblyLemmaQueue, SFGC, or the
-- graph-combinatorics implementation which caused the host-memory failure.
--
-- The theorem-surface side uses BalabanPolymerDiameterEntropyLight to retain
-- the canonical P06/P07/P08/P09 audit and fail-closed Clay flag.  The RG side
-- consumes only the exact physical one-step/iteration API.  Thus checking this
-- module tests the polymer-audit -> RG packaging handoff without reopening the
-- heavyweight polymer graph.
--
-- No analytic input is promoted here.  PhysicalOneStepClosure still requires
-- physical coupling-domain preservation, boundary reinjection admissibility,
-- and strict combined polymer-norm closure.  Once those are supplied, the
-- all-scale admissibility and partition-function induction below are exact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropyLight as Light
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalOneStepClosureExact as Physical

record LightweightPolymerRGHandoff
    (State Bound : Set) : Set₁ where
  field
    polymerAudit : Light.LightweightPolymerAuditSurface
    closure : Physical.PhysicalOneStepClosure State Bound

    p06Canonical :
      Light.LightweightPolymerAuditSurface.p06AnimalCounting polymerAudit
      ≡ Light.LightweightPolymerAuditSurface.p06AnimalCounting
          Light.canonicalLightweightPolymerAuditSurface
    p07Canonical :
      Light.LightweightPolymerAuditSurface.p07KPSummability polymerAudit
      ≡ Light.LightweightPolymerAuditSurface.p07KPSummability
          Light.canonicalLightweightPolymerAuditSurface
    p08Canonical :
      Light.LightweightPolymerAuditSurface.p08PZeroPositive polymerAudit
      ≡ Light.LightweightPolymerAuditSurface.p08PZeroPositive
          Light.canonicalLightweightPolymerAuditSurface
    p09Canonical :
      Light.LightweightPolymerAuditSurface.p09FullDecay polymerAudit
      ≡ Light.LightweightPolymerAuditSurface.p09FullDecay
          Light.canonicalLightweightPolymerAuditSurface

    noPromotion : clayYangMillsPromoted ≡ false

open LightweightPolymerRGHandoff public

canonicalLightweightPolymerRGHandoff :
  ∀ {State Bound} →
  Physical.PhysicalOneStepClosure State Bound →
  LightweightPolymerRGHandoff State Bound
canonicalLightweightPolymerRGHandoff closure = record
  { polymerAudit = Light.canonicalLightweightPolymerAuditSurface
  ; closure = closure
  ; p06Canonical = refl
  ; p07Canonical = refl
  ; p08Canonical = refl
  ; p09Canonical = refl
  ; noPromotion = refl
  }

------------------------------------------------------------------------
-- Exact RG handoff.  No heavyweight polymer object occurs in these types.
------------------------------------------------------------------------

lightweightPhysicalAdmissibility :
  ∀ {State Bound} (handoff : LightweightPolymerRGHandoff State Bound) →
  UV.CombinedRGAdmissibility (Physical.normData (closure handoff))
lightweightPhysicalAdmissibility handoff =
  Physical.physicalAdmissibility (closure handoff)

lightweightStepPreservesAdmissibility :
  ∀ {State Bound}
    (handoff : LightweightPolymerRGHandoff State Bound)
    (state : State) →
  UV.AdmissibleRGState (lightweightPhysicalAdmissibility handoff) state →
  UV.AdmissibleRGState
    (lightweightPhysicalAdmissibility handoff)
    (UV.next (Physical.normData (closure handoff)) state)
lightweightStepPreservesAdmissibility handoff state evidence =
  UV.combinedStepPreservesAdmissibility
    (lightweightPhysicalAdmissibility handoff)
    state
    evidence

lightweightPackageAllScaleAdmissible :
  ∀ {State Bound}
    {closure : Physical.PhysicalOneStepClosure State Bound}
    (initialData : Physical.PhysicalUVInitialData closure)
    (scale : Nat) →
  UV.AdmissibleRGState
    (UV.admissibility (Physical.physicalGate4UVPackage initialData))
    (UV.stateAt
      (UV.normData (Physical.physicalGate4UVPackage initialData))
      (UV.initial (Physical.physicalGate4UVPackage initialData))
      scale)
lightweightPackageAllScaleAdmissible initialData scale =
  UV.packageAllScaleAdmissible
    (Physical.physicalGate4UVPackage initialData)
    scale

lightweightPackagePartitionBound :
  ∀ {State Bound}
    {closure : Physical.PhysicalOneStepClosure State Bound}
    (initialData : Physical.PhysicalUVInitialData closure)
    (scale : Nat) →
  UV.PartitionFunctionUniformlyBounded
    (UV.consequences (Physical.physicalGate4UVPackage initialData))
    (UV.stateAt
      (UV.normData (Physical.physicalGate4UVPackage initialData))
      (UV.initial (Physical.physicalGate4UVPackage initialData))
      scale)
lightweightPackagePartitionBound initialData scale =
  UV.packagePartitionFunctionUniformBound
    (Physical.physicalGate4UVPackage initialData)
    scale

lightweightPolymerAuditRGHandoffLevel : ProofLevel
lightweightPolymerAuditRGHandoffLevel = machineChecked

lightweightOneStepRGAssemblyLevel : ProofLevel
lightweightOneStepRGAssemblyLevel = machineChecked

lightweightAllScaleRGAssemblyLevel : ProofLevel
lightweightAllScaleRGAssemblyLevel = machineChecked

physicalOneStepAnalyticInputsLevel : ProofLevel
physicalOneStepAnalyticInputsLevel = conditional

physicalInitialUVStabilityInputsLevel : ProofLevel
physicalInitialUVStabilityInputsLevel = conditional
