module DASHI.Physics.ShiftGaugeFieldTheoryAgreement where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteContinuityCurrent as SDCC
open import DASHI.Physics.ShiftDiscreteWaveEnergy as SDWE
open import DASHI.Physics.ShiftFieldTheoryConsistency as SFTC
open import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
open import DASHI.Physics.ShiftWaveEnergyHierarchy as SWEH
open import DASHI.Physics.ShiftWaveRefinementHierarchy as SWRH
open import DASHI.Physics.ShiftWaveGlobalUpdate as SWGU

------------------------------------------------------------------------
-- Theorem-thin agreement surface between the current field-theory coherence
-- lane, the hierarchy-energy lane, and the first finite gauge-coupling lane.
--
-- This module only closes the vacuum-gauge slice:
--   * the static vacuum gauge update is exactly the current coarse global
--     update,
--   * the field-theory witness is exactly that same vacuum-gauge update,
--   * the hierarchy-energy surfaces therefore apply unchanged to the
--     vacuum-gauge-updated field.
--
-- No full local-gauge covariance, gauge-energy conservation, or multilevel
-- gauge hierarchy claim is implied.

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl q = q

vacuumGaugeWitnessField :
  SWRH.ShiftWaveField3 →
  SWRH.ShiftWaveField3
vacuumGaugeWitnessField ψ =
  SFGC.gaugeGlobalUpdate SFGC.vacuumGaugeField ψ

VacuumGaugeUpdateCompatibility : Set
VacuumGaugeUpdateCompatibility =
  (ψ : SWRH.ShiftWaveField3) →
  (s : SPTI.ShiftPressurePoint) →
  vacuumGaugeWitnessField ψ s
    ≡
  SWGU.coarseGlobalUpdate ψ s

vacuumGaugeUpdateCompatibility :
  VacuumGaugeUpdateCompatibility
vacuumGaugeUpdateCompatibility ψ s
  rewrite SFGC.vacuumGaugeCompatibility ψ s
  = refl

VacuumGaugeWitnessCompatibility : Set
VacuumGaugeWitnessCompatibility =
  (ψ : SWRH.ShiftWaveField3) →
  (s : SPTI.ShiftPressurePoint) →
  vacuumGaugeWitnessField ψ s
    ≡
  SFTC.coarseWitnessField ψ s

vacuumGaugeWitnessCompatibility :
  VacuumGaugeWitnessCompatibility
vacuumGaugeWitnessCompatibility ψ s =
  trans
    (vacuumGaugeUpdateCompatibility ψ s)
    (sym (SFTC.coarseWitnessUpdatePointwise ψ s))

VacuumGaugeUpdatedEnergyCompatibility : Set
VacuumGaugeUpdatedEnergyCompatibility =
  (ψ : SWRH.ShiftWaveField3) →
  (s : SPTI.ShiftPressurePoint) →
  SDWE.waveNormSq (vacuumGaugeWitnessField ψ s)
    ≡
  SDCC.coarseUpdatedLocalEnergy ψ s

vacuumGaugeUpdatedEnergyCompatibility :
  VacuumGaugeUpdatedEnergyCompatibility
vacuumGaugeUpdatedEnergyCompatibility ψ s =
  trans
    (SFGC.cong SDWE.waveNormSq (vacuumGaugeWitnessCompatibility ψ s))
    (sym (SFTC.coarseWitnessUpdatedEnergyCompatibility ψ s))

VacuumGaugeCoarseFieldEnergyCompatibility : Set
VacuumGaugeCoarseFieldEnergyCompatibility =
  (ψ : SWRH.ShiftWaveField3) →
  SWEH.coarseFieldEnergy (vacuumGaugeWitnessField ψ)
    ≡
  SWEH.coarseFieldEnergy (SFTC.coarseWitnessField ψ)

vacuumGaugeCoarseFieldEnergyCompatibility :
  VacuumGaugeCoarseFieldEnergyCompatibility
vacuumGaugeCoarseFieldEnergyCompatibility ψ
  rewrite vacuumGaugeWitnessCompatibility ψ SPTI.shiftStartPoint
        | vacuumGaugeWitnessCompatibility ψ SPTI.shiftNextPoint
        | vacuumGaugeWitnessCompatibility ψ SPTI.shiftHeldExitPoint
  = refl

VacuumGaugeLiftEnergyShape3to5 : Set
VacuumGaugeLiftEnergyShape3to5 =
  (ψ : SWRH.ShiftWaveField3) →
  SWEH.fineFieldEnergy (SWRH.liftField3to5 (vacuumGaugeWitnessField ψ))
    ≡
  SDWE.waveNormSq (vacuumGaugeWitnessField ψ SPTI.shiftStartPoint)
    +ℤ
  SDWE.waveNormSq (vacuumGaugeWitnessField ψ SPTI.shiftStartPoint)
    +ℤ
  SDWE.waveNormSq (vacuumGaugeWitnessField ψ SPTI.shiftNextPoint)
    +ℤ
  SDWE.waveNormSq (vacuumGaugeWitnessField ψ SPTI.shiftHeldExitPoint)
    +ℤ
  SDWE.waveNormSq (vacuumGaugeWitnessField ψ SPTI.shiftHeldExitPoint)

vacuumGaugeLiftEnergyShape3to5 :
  VacuumGaugeLiftEnergyShape3to5
vacuumGaugeLiftEnergyShape3to5 ψ =
  SWEH.liftFieldEnergyShape3to5 (vacuumGaugeWitnessField ψ)

VacuumGaugeLiftLaplacianControl3to5 : Set
VacuumGaugeLiftLaplacianControl3to5 =
  (ψ : SWRH.ShiftWaveField3) →
  SWEH.embeddedFineLaplacianEnergy
    (SWRH.liftField3to5 (vacuumGaugeWitnessField ψ))
    ≡
  SWEH.coarseLaplacianEnergy (vacuumGaugeWitnessField ψ)

vacuumGaugeLiftLaplacianControl3to5 :
  VacuumGaugeLiftLaplacianControl3to5
vacuumGaugeLiftLaplacianControl3to5 ψ =
  SWEH.liftLaplacianEnergyControl3to5 (vacuumGaugeWitnessField ψ)

record ShiftGaugeFieldTheoryAgreement : Setω where
  field
    coarseField : Set
    fieldTheoryConsistency : SFTC.ShiftFieldTheoryConsistency
    finiteGaugeCoupling : SFGC.ShiftFiniteGaugeCoupling
    energyHierarchy : SWEH.ShiftWaveEnergyHierarchy
    vacuumGaugeUpdateLaw : Set
    vacuumGaugeWitnessLaw : Set
    vacuumGaugeUpdatedEnergyLaw : Set
    vacuumGaugeCoarseFieldEnergyLaw : Set
    vacuumGaugeLiftEnergyShapeLaw : Set
    vacuumGaugeLiftLaplacianControlLaw : Set
    nonClaimBoundary : List String

shiftGaugeFieldTheoryAgreement :
  ShiftGaugeFieldTheoryAgreement
shiftGaugeFieldTheoryAgreement =
  record
    { coarseField = SWRH.ShiftWaveField3
    ; fieldTheoryConsistency = SFTC.shiftFieldTheoryConsistency
    ; finiteGaugeCoupling = SFGC.shiftFiniteGaugeCoupling
    ; energyHierarchy = SWEH.shiftWaveEnergyHierarchy
    ; vacuumGaugeUpdateLaw = VacuumGaugeUpdateCompatibility
    ; vacuumGaugeWitnessLaw = VacuumGaugeWitnessCompatibility
    ; vacuumGaugeUpdatedEnergyLaw =
        VacuumGaugeUpdatedEnergyCompatibility
    ; vacuumGaugeCoarseFieldEnergyLaw =
        VacuumGaugeCoarseFieldEnergyCompatibility
    ; vacuumGaugeLiftEnergyShapeLaw = VacuumGaugeLiftEnergyShape3to5
    ; vacuumGaugeLiftLaplacianControlLaw =
        VacuumGaugeLiftLaplacianControl3to5
    ; nonClaimBoundary =
        "Finite vacuum-gauge agreement package only"
        ∷ "agreement is only proved on the vacuum static-gauge slice of the current coarse carrier"
        ∷ "the vacuum gauge update is identified with the existing coarse one-pass update and witness field"
        ∷ "hierarchy-energy surfaces are only re-used on that same vacuum-gauge-updated field"
        ∷ "no gauge-energy conservation, full local covariance, multilevel gauge hierarchy, or path-selection claim is implied"
        ∷ []
    }
