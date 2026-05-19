module DASHI.Physics.ShiftGaugeCurrentConsistency where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteContinuityCurrent as SDCC
open import DASHI.Physics.ShiftFieldTheoryConsistency as SFTC
open import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
open import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
open import DASHI.Physics.ShiftGaugeFieldTheoryAgreement as SGFTA
open import DASHI.Physics.ShiftMinimalGaugeTheory as SMGT
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- Current-sourced gauge-update covariance surface over the finite C4 lane.
--
-- This module stays theorem-thin on purpose.
--   * edge current is reused directly from the current coarse local-current
--     bookkeeping surface,
--   * gauge update is sourced by that current, but the present
--     current-to-phase reducer is intentionally neutral (`φ0`) so exact
--     covariance closes cheaply,
--   * richer current invariance and nontrivial current-to-phase transport are
--     exposed as target surfaces for later closure.
--
-- No Maxwell/Yang-Mills, continuum gauge flow, or dynamic-gauge physics claim
-- is implied here.

Edge : Set
Edge = SPTI.ShiftPressurePoint

MatterField : Set
MatterField = SSL.ShiftWaveField

edgeCurrent :
  MatterField →
  Edge →
  ℤ
edgeCurrent ψ e =
  SDCC.coarseLocalCurrentMagnitude ψ e

currentPhase :
  ℤ →
  SPTI4.Phase4
currentPhase j = SPTI4.φ0

updateGauge :
  SFGC.GaugeField →
  MatterField →
  SFGC.GaugeField
updateGauge A ψ e =
  SFGS.phaseAdd4 (currentPhase (edgeCurrent ψ e)) (A e)

CurrentPhaseNeutralLaw : Set
CurrentPhaseNeutralLaw =
  (j : ℤ) →
  currentPhase j ≡ SPTI4.φ0

currentPhaseNeutralLaw :
  CurrentPhaseNeutralLaw
currentPhaseNeutralLaw j = refl

VacuumGaugeUpdateStability : Set
VacuumGaugeUpdateStability =
  (ψ : MatterField) →
  (e : Edge) →
  updateGauge SFGC.vacuumGaugeField ψ e
    ≡
  SFGC.vacuumGaugeField e

vacuumGaugeUpdateStability :
  VacuumGaugeUpdateStability
vacuumGaugeUpdateStability ψ e = refl

GaugeCurrentConsistency : Set
GaugeCurrentConsistency =
  (g : SFGS.GaugeTransform) →
  (A : SFGC.GaugeField) →
  (ψ : MatterField) →
  (e : Edge) →
  updateGauge
    (SFGC.transformGauge g A)
    (SFGS.transformMatter g ψ)
    e
    ≡
  SFGC.transformGauge g (updateGauge A ψ) e

gaugeCurrentConsistency :
  GaugeCurrentConsistency
gaugeCurrentConsistency g A ψ e = refl

EdgeCurrentGaugeInvariantTarget : Set
EdgeCurrentGaugeInvariantTarget =
  (g : SFGS.GaugeTransform) →
  (ψ : MatterField) →
  (e : Edge) →
  edgeCurrent (SFGS.transformMatter g ψ) e
    ≡
  edgeCurrent ψ e

CurrentPhaseInvariantTarget : Set
CurrentPhaseInvariantTarget =
  (g : SFGS.GaugeTransform) →
  (ψ : MatterField) →
  (e : Edge) →
  currentPhase (edgeCurrent (SFGS.transformMatter g ψ) e)
    ≡
  currentPhase (edgeCurrent ψ e)

GaugeCurrentAgreementVacuumTarget : Set
GaugeCurrentAgreementVacuumTarget =
  (ψ : MatterField) →
  (e : Edge) →
  updateGauge SFGC.vacuumGaugeField ψ e
    ≡
  SFGC.vacuumGaugeField e

record ShiftGaugeCurrentConsistency : Setω where
  field
    coarseMatterField : Set
    edge : Set
    staticGaugeField : Set
    fieldTheoryConsistency : SFTC.ShiftFieldTheoryConsistency
    minimalGaugeTheory : SMGT.ShiftMinimalGaugeTheory
    gaugeFieldTheoryAgreement : SGFTA.ShiftGaugeFieldTheoryAgreement
    edgeCurrentObservable :
      coarseMatterField → edge → ℤ
    currentPhaseReducer :
      ℤ → SPTI4.Phase4
    gaugeUpdate :
      staticGaugeField → coarseMatterField → staticGaugeField
    currentPhaseNeutral : Set
    vacuumGaugeStability : Set
    covarianceLaw : Set
    edgeCurrentGaugeInvariantTarget : Set
    currentPhaseInvariantTarget : Set
    nonClaimBoundary : List String

shiftGaugeCurrentConsistency :
  ShiftGaugeCurrentConsistency
shiftGaugeCurrentConsistency =
  record
    { coarseMatterField = MatterField
    ; edge = Edge
    ; staticGaugeField = SFGC.GaugeField
    ; fieldTheoryConsistency = SFTC.shiftFieldTheoryConsistency
    ; minimalGaugeTheory = SMGT.shiftMinimalGaugeTheory
    ; gaugeFieldTheoryAgreement = SGFTA.shiftGaugeFieldTheoryAgreement
    ; edgeCurrentObservable = edgeCurrent
    ; currentPhaseReducer = currentPhase
    ; gaugeUpdate = updateGauge
    ; currentPhaseNeutral = CurrentPhaseNeutralLaw
    ; vacuumGaugeStability = VacuumGaugeUpdateStability
    ; covarianceLaw = GaugeCurrentConsistency
    ; edgeCurrentGaugeInvariantTarget =
        EdgeCurrentGaugeInvariantTarget
    ; currentPhaseInvariantTarget =
        CurrentPhaseInvariantTarget
    ; nonClaimBoundary =
        "Finite current-sourced gauge-update consistency package only"
        ∷ "edge current is the existing coarse local-current magnitude reused pointwise on the coarse carrier"
        ∷ "the present current-to-phase reducer is intentionally neutral, so gauge-update covariance closes exactly but gauge reactivity is not yet promoted"
        ∷ "richer gauge invariance of edge current and nontrivial currentPhase transport remain target-law surfaces"
        ∷ "No Maxwell/Yang-Mills dynamics, continuum gauge flow, local covariance proof, or full U(1) claim is implied"
        ∷ []
    }
