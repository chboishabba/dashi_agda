module DASHI.Physics.ShiftMinimalGaugeTheory where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
open import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveGlobalUpdate as SWGU

------------------------------------------------------------------------
-- First minimal interacting two-field theory over the current finite
-- wave/gauge machinery.
--
-- This lane stays intentionally narrow:
--   * matter field = existing three-point discrete-wave field
--   * gauge field = existing bounded static Phase4 link field
--   * update = gauge-covariant one-pass matter advance with gauge held fixed
--
-- The only exact reduction proved here is the vacuum slice:
-- with the vacuum static gauge field, the matter update is exactly the
-- current coarse global update.

record StaticGaugeWorld : Set where
  constructor mkStaticGaugeWorld
  field
    matterField : SSL.ShiftWaveField
    gaugeField : SFGC.GaugeField

staticGaugeWorldStep :
  StaticGaugeWorld →
  StaticGaugeWorld
staticGaugeWorldStep W =
  mkStaticGaugeWorld
    (SFGC.gaugeGlobalUpdate
      (StaticGaugeWorld.gaugeField W)
      (StaticGaugeWorld.matterField W))
    (StaticGaugeWorld.gaugeField W)

vacuumStaticGaugeWorld :
  SSL.ShiftWaveField →
  StaticGaugeWorld
vacuumStaticGaugeWorld ψ =
  mkStaticGaugeWorld ψ SFGC.vacuumGaugeField

VacuumMatterReductionLaw : Set
VacuumMatterReductionLaw =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  StaticGaugeWorld.matterField (staticGaugeWorldStep (vacuumStaticGaugeWorld ψ)) s
    ≡
  SWGU.coarseGlobalUpdate ψ s

vacuumMatterReductionLaw :
  VacuumMatterReductionLaw
vacuumMatterReductionLaw ψ s
  rewrite SFGC.vacuumGaugeCompatibility ψ s
  = refl

VacuumGaugeRetentionLaw : Set
VacuumGaugeRetentionLaw =
  (ψ : SSL.ShiftWaveField) →
  StaticGaugeWorld.gaugeField (staticGaugeWorldStep (vacuumStaticGaugeWorld ψ))
    ≡
  SFGC.vacuumGaugeField

vacuumGaugeRetentionLaw :
  VacuumGaugeRetentionLaw
vacuumGaugeRetentionLaw ψ = refl

ConstantGaugeVacuumStabilityLaw : Set
ConstantGaugeVacuumStabilityLaw =
  (φ : SPTI4.Phase4) →
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  SFGC.transformGauge (SFGS.constantGaugeTransform φ) SFGC.vacuumGaugeField s
    ≡
  SFGC.vacuumGaugeField s

constantGaugeVacuumStabilityLaw :
  ConstantGaugeVacuumStabilityLaw
constantGaugeVacuumStabilityLaw φ ψ s =
  SFGC.constantGaugePreservesVacuum φ s

record ShiftMinimalGaugeTheory : Setω where
  field
    MatterField : Set
    StaticGaugeField : Set
    World : Set
    gaugeVacuum : StaticGaugeField
    worldStep : World → World
    matterUpdate :
      StaticGaugeField →
      MatterField →
      MatterField
    vacuumMatterReduction : Set
    vacuumGaugeRetention : Set
    constantGaugeVacuumStability : Set
    nonClaimBoundary : List String

shiftMinimalGaugeTheory : ShiftMinimalGaugeTheory
shiftMinimalGaugeTheory =
  record
    { MatterField = SSL.ShiftWaveField
    ; StaticGaugeField = SFGC.GaugeField
    ; World = StaticGaugeWorld
    ; gaugeVacuum = SFGC.vacuumGaugeField
    ; worldStep = staticGaugeWorldStep
    ; matterUpdate = SFGC.gaugeGlobalUpdate
    ; vacuumMatterReduction = VacuumMatterReductionLaw
    ; vacuumGaugeRetention = VacuumGaugeRetentionLaw
    ; constantGaugeVacuumStability = ConstantGaugeVacuumStabilityLaw
    ; nonClaimBoundary =
        "Minimal static matter-plus-gauge package only"
        ∷ "Gauge field is held fixed under the one-pass update in this lane"
        ∷ "Vacuum reduction is exact: vacuum static-gauge matter update matches the current coarse global update"
        ∷ "Only vacuum retention and constant-gauge stability of the vacuum slice are witnessed explicitly"
        ∷ "No gauge dynamics, no full U(1), and no local gauge covariance theorem are implied here"
        ∷ []
    }
