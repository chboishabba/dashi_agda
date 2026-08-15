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
-- This is the lightweight Gate-4 handoff requested by the local Agda 2.9
-- audit.  It deliberately does not import BalabanPolymerDiameterEntropy,
-- StepVAssemblyLemmaQueue, SFGC, or the graph-combinatorics implementation.
--
-- The theorem-surface side uses BalabanPolymerDiameterEntropyLight to retain
-- the canonical P06/P07/P08/P09 audit and the fail-closed Clay flag.  The RG
-- side consumes only the already-small exact Gate-4 one-step/iteration API.
-- Hence an Agda check of this module tests the actual polymer-audit -> RG
-- packaging handoff without reopening the OOM import graph.
--
-- This does NOT manufacture the missing analytic estimates.  In particular,
-- PhysicalOneStepClosure still requires the physical coupling-domain,
-- boundary, and strict polymer-norm preservation proofs.  What is proved here
-- is that once those physical one-step estimates are supplied, the lightweight
-- polymer audit and the exact all-scale RG induction compose on one carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
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

    -- Keep the audit on exactly the canonical source surfaces, rather than a
    -- parallel lightweight vocabulary.
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
-- Actual RG handoff: no polymer implementation details occur below.
------------------------------------------------------------------------

lightweightPhysicalAdmissibility :
  ∀ {State Bound} →
  LightweightPolymerRGHandoff State Bound →
  UV.CombinedRGAdmissibility
    (Physical.normData ∘ closure)
lightweightPhysicalAdmissibility handoff =
  Physical.physicalAdmissibility (closure handoff)
  where
  _∘_ :
    ∀ {A B : Set} {C : B → Set} →
    ((b : B) → C b) → A → ((a : A) → B) → Set
  _∘_ f a g = C (g a)

-- The previous helper type is intentionally not exported as a separate API;
-- the concrete all-scale theorem below uses the exact Physical/UV types and
-- therefore catches any future drift in that handoff.

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

lightweightAllScaleRGAssemblyLevel : ProofLevel
lightweightAllScaleRGAssemblyLevel = machineChecked

-- These are still the actual mathematical frontier.  Keeping them named here
-- makes the lightweight check useful rather than promotional.
physicalOneStepAnalyticInputsLevel : ProofLevel
physicalOneStepAnalyticInputsLevel = conditional

physicalInitialUVStabilityInputsLevel : ProofLevel
physicalInitialUVStabilityInputsLevel = conditional
