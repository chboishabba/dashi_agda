module DASHI.Physics.YangMills.BalabanClayGate4LightweightOneStepRegionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions",
-- Communications in Mathematical Physics 116 (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
--
-- Couple the new lightweight P06--P09 audit to the repository's actual
-- rational invariant-region arithmetic.  This is not another abstract
-- all-scale record: the one-step witness contains the concrete inequalities
-- consumed by BalabanYM4RGCommonBudgetClosureExact:
--
--   K' <= q K + E,
--   E <= (1-q) Kmax,
--   g', L', covariance' stay inside their common caps,
--   lattice decay and inverse physical spacing remain nonnegative.
--
-- The theorem below therefore tells the lightweight checker exactly where the
-- analytic frontier begins without importing the OOM polymer implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropyLight as Light
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as Region
import DASHI.Physics.YangMills.BalabanYM4RGCommonBudgetClosureExact as Budget

record LightweightGate4OneStepWitness
    (parameters : Region.YM4RGRegionParameters)
    (current next : Region.YM4RGState) : Set₁ where
  field
    polymerAudit : Light.LightweightPolymerAuditSurface
    analyticBounds : Budget.CoupledOneStepAnalyticBounds parameters current next

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

open LightweightGate4OneStepWitness public

canonicalLightweightGate4OneStepWitness :
  ∀ {parameters current next} →
  Budget.CoupledOneStepAnalyticBounds parameters current next →
  LightweightGate4OneStepWitness parameters current next
canonicalLightweightGate4OneStepWitness analyticBounds = record
  { polymerAudit = Light.canonicalLightweightPolymerAuditSurface
  ; analyticBounds = analyticBounds
  ; p06Canonical = refl
  ; p07Canonical = refl
  ; p08Canonical = refl
  ; p09Canonical = refl
  ; noPromotion = refl
  }

lightweightGate4OneStepPreservesRegion :
  ∀ {parameters current next} →
  Region.InYM4RGInvariantRegion parameters current →
  LightweightGate4OneStepWitness parameters current next →
  Region.InYM4RGInvariantRegion parameters next
lightweightGate4OneStepPreservesRegion currentRegion witness =
  Budget.coupledOneStepPreservesAnalyticRegion
    currentRegion
    (analyticBounds witness)

lightweightGate4OneStepRegionLevel : ProofLevel
lightweightGate4OneStepRegionLevel = machineChecked

-- The lightweight polymer audit is now out of the critical import graph.  The
-- remaining theorem is exactly the physical production of the six coupled
-- inequalities stored in CoupledOneStepAnalyticBounds.
lightweightGate4PhysicalAnalyticBoundsLevel : ProofLevel
lightweightGate4PhysicalAnalyticBoundsLevel = conditional
