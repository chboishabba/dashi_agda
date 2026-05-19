module DASHI.Physics.ShiftTwoFieldGaugeInteraction where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
open import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
open import DASHI.Physics.ShiftGaugeCurrentConsistency as SGCC
  using
    ( edgeCurrent
    ; currentPhase
    ; ShiftGaugeCurrentConsistency
    ; shiftGaugeCurrentConsistency
    )
open import DASHI.Physics.ShiftMinimalGaugeTheory as SMGT
  using (ShiftMinimalGaugeTheory; shiftMinimalGaugeTheory)
open import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- First theorem-thin two-field gauge-mediated interaction surface over the
-- existing finite matter+static-gauge lane.
--
-- This module stays intentionally bounded:
--   * two matter fields live on the current coarse carrier,
--   * both fields evolve through the existing static-gauge Hamiltonian plus a
--     gauge-mediated nearest-neighbor interaction term,
--   * gauge update is sourced by a combined current surface, but the active
--     current-to-phase reducer remains the neutral one inherited from the
--     current gauge-consistency lane.
--
-- The result is a coupled finite package, not a full reactive gauge theory.

MatterField : Set
MatterField = SSL.ShiftWaveField

StaticGaugeField : Set
StaticGaugeField = SFGC.GaugeField

record TwoMatterFields : Set where
  constructor mkTwoMatterFields
  field
    ψ : MatterField
    χ : MatterField

combinedMatterField :
  TwoMatterFields →
  MatterField
combinedMatterField fields s =
  SDWS.waveAdd
    (TwoMatterFields.ψ fields s)
    (TwoMatterFields.χ fields s)

interactionTerm :
  StaticGaugeField →
  MatterField →
  MatterField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
interactionTerm A ψ χ s =
  SDWS.waveAdd
    (SFGS.phaseAct
      (SFGC.leftGaugePhase A s)
      (χ (SSL.leftNeighbor s)))
    (SFGS.phaseAct
      (SFGC.rightGaugePhase A s)
      (χ (SSL.rightNeighbor s)))

Hψ :
  StaticGaugeField →
  TwoMatterFields →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
Hψ A fields s =
  SDWS.waveAdd
    (SFGC.gaugeHamiltonian A (TwoMatterFields.ψ fields) s)
    (interactionTerm A (TwoMatterFields.ψ fields) (TwoMatterFields.χ fields) s)

Hχ :
  StaticGaugeField →
  TwoMatterFields →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
Hχ A fields s =
  SDWS.waveAdd
    (SFGC.gaugeHamiltonian A (TwoMatterFields.χ fields) s)
    (interactionTerm A (TwoMatterFields.χ fields) (TwoMatterFields.ψ fields) s)

twoFieldMatterStep :
  StaticGaugeField →
  TwoMatterFields →
  TwoMatterFields
twoFieldMatterStep A fields =
  mkTwoMatterFields
    (λ s →
      SDWS.waveAdd
        (TwoMatterFields.ψ fields s)
        (SDWS.mulI (Hψ A fields s)))
    (λ s →
      SDWS.waveAdd
        (TwoMatterFields.χ fields s)
        (SDWS.mulI (Hχ A fields s)))

totalCurrent :
  TwoMatterFields →
  SPTI.ShiftPressurePoint →
  ℤ
totalCurrent fields e =
  SGCC.edgeCurrent (TwoMatterFields.ψ fields) e
    +ℤ
  SGCC.edgeCurrent (TwoMatterFields.χ fields) e

updateGaugeTwoField :
  StaticGaugeField →
  TwoMatterFields →
  GaugeField
updateGaugeTwoField A fields e =
  SFGS.phaseAdd4
    (SGCC.currentPhase (totalCurrent fields e))
    (A e)

transformTwoMatterFields :
  SFGS.GaugeTransform →
  TwoMatterFields →
  TwoMatterFields
transformTwoMatterFields g fields =
  mkTwoMatterFields
    (SFGS.transformMatter g (TwoMatterFields.ψ fields))
    (SFGS.transformMatter g (TwoMatterFields.χ fields))

twoFieldGaugeStep :
  StaticGaugeField →
  TwoMatterFields →
  Σ StaticGaugeField (λ _ → TwoMatterFields)
twoFieldGaugeStep A fields =
  updateGaugeTwoField A fields
  ,
  twoFieldMatterStep A fields

TwoFieldVacuumGaugeStability : Set
TwoFieldVacuumGaugeStability =
  (fields : TwoMatterFields) →
  (e : SPTI.ShiftPressurePoint) →
  updateGaugeTwoField SFGC.vacuumGaugeField fields e
    ≡
  SFGC.vacuumGaugeField e

twoFieldVacuumGaugeStability :
  TwoFieldVacuumGaugeStability
twoFieldVacuumGaugeStability fields e = refl

TwoFieldGaugeCurrentConsistencyTarget : Set
TwoFieldGaugeCurrentConsistencyTarget =
  (g : SFGS.GaugeTransform) →
  (A : StaticGaugeField) →
  (fields : TwoMatterFields) →
  (e : SPTI.ShiftPressurePoint) →
  updateGaugeTwoField
    (SFGC.transformGauge g A)
    (transformTwoMatterFields g fields)
    e
    ≡
  SFGC.transformGauge g (updateGaugeTwoField A fields) e

twoFieldGaugeCurrentConsistencyTarget :
  TwoFieldGaugeCurrentConsistencyTarget
twoFieldGaugeCurrentConsistencyTarget g A fields e = refl

record ShiftTwoFieldGaugeInteraction : Setω where
  field
    matterField : Set
    staticGaugeField : Set
    matterPair : Set
    minimalGaugeTheory : SMGT.ShiftMinimalGaugeTheory
    gaugeCurrentConsistency : SGCC.ShiftGaugeCurrentConsistency
    interaction :
      staticGaugeField →
      matterField →
      matterField →
      SPTI.ShiftPressurePoint →
      SDWS.DiscreteWave
    coupledMatterUpdate :
      staticGaugeField →
      matterPair →
      matterPair
    currentSourcedGaugeUpdate :
      staticGaugeField →
      matterPair →
      staticGaugeField
    jointGaugeStep :
      staticGaugeField →
      matterPair →
      Σ staticGaugeField (λ _ → matterPair)
    gaugeCurrentConsistencyTarget : Set
    vacuumGaugeStability : Set
    nonClaimBoundary : List String

shiftTwoFieldGaugeInteraction :
  ShiftTwoFieldGaugeInteraction
shiftTwoFieldGaugeInteraction =
  record
    { matterField = MatterField
    ; staticGaugeField = StaticGaugeField
    ; matterPair = TwoMatterFields
    ; minimalGaugeTheory = SMGT.shiftMinimalGaugeTheory
    ; gaugeCurrentConsistency = SGCC.shiftGaugeCurrentConsistency
    ; interaction = interactionTerm
    ; coupledMatterUpdate = twoFieldMatterStep
    ; currentSourcedGaugeUpdate = updateGaugeTwoField
    ; jointGaugeStep = twoFieldGaugeStep
    ; gaugeCurrentConsistencyTarget =
        TwoFieldGaugeCurrentConsistencyTarget
    ; vacuumGaugeStability =
        TwoFieldVacuumGaugeStability
    ; nonClaimBoundary =
        "Finite two-field gauge-mediated interaction package only"
        ∷ "Both matter fields live on the current coarse carrier and interact through the existing bounded static gauge links"
        ∷ "Gauge update is current-sourced through the inherited neutral currentPhase reducer, so the surface is symmetry-safe rather than physically reactive"
        ∷ "The joint step packages matter coupling plus a bounded gauge-update target surface only"
        ∷ "No Maxwell/Yang-Mills dynamics, local gauge covariance proof, continuum limit, non-abelian Standard Model, or dynamic geometry claim is implied"
        ∷ []
    }
