module DASHI.Physics.ShiftFiniteGaugeSymmetry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- Finite local phase-symmetry surface over the current shift-wave lane.
--
-- This stays intentionally small: the phase group is the four-class `Phase4`
-- table already used by the discrete-wave package, and the matter action is
-- just repeated quarter-turn rotation via `mulI`.

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

phaseAdd4 : SPTI4.Phase4 → SPTI4.Phase4 → SPTI4.Phase4
phaseAdd4 SPTI4.φ0 φ = φ
phaseAdd4 SPTI4.φ1 SPTI4.φ0 = SPTI4.φ1
phaseAdd4 SPTI4.φ1 SPTI4.φ1 = SPTI4.φ2
phaseAdd4 SPTI4.φ1 SPTI4.φ2 = SPTI4.φ3
phaseAdd4 SPTI4.φ1 SPTI4.φ3 = SPTI4.φ0
phaseAdd4 SPTI4.φ2 SPTI4.φ0 = SPTI4.φ2
phaseAdd4 SPTI4.φ2 SPTI4.φ1 = SPTI4.φ3
phaseAdd4 SPTI4.φ2 SPTI4.φ2 = SPTI4.φ0
phaseAdd4 SPTI4.φ2 SPTI4.φ3 = SPTI4.φ1
phaseAdd4 SPTI4.φ3 SPTI4.φ0 = SPTI4.φ3
phaseAdd4 SPTI4.φ3 SPTI4.φ1 = SPTI4.φ0
phaseAdd4 SPTI4.φ3 SPTI4.φ2 = SPTI4.φ1
phaseAdd4 SPTI4.φ3 SPTI4.φ3 = SPTI4.φ2

phaseInv4 : SPTI4.Phase4 → SPTI4.Phase4
phaseInv4 SPTI4.φ0 = SPTI4.φ0
phaseInv4 SPTI4.φ1 = SPTI4.φ3
phaseInv4 SPTI4.φ2 = SPTI4.φ2
phaseInv4 SPTI4.φ3 = SPTI4.φ1

phaseAct :
  SPTI4.Phase4 →
  SDWS.DiscreteWave →
  SDWS.DiscreteWave
phaseAct SPTI4.φ0 ψ = ψ
phaseAct SPTI4.φ1 ψ = SDWS.mulI ψ
phaseAct SPTI4.φ2 ψ = SDWS.mulI (SDWS.mulI ψ)
phaseAct SPTI4.φ3 ψ = SDWS.mulI (SDWS.mulI (SDWS.mulI ψ))

PhaseActComposeTarget : Set
PhaseActComposeTarget =
  (φ ψ : SPTI4.Phase4) →
  (w : SDWS.DiscreteWave) →
  phaseAct (phaseAdd4 φ ψ) w
    ≡
  phaseAct φ (phaseAct ψ w)

PhaseActInverseTarget : Set
PhaseActInverseTarget =
  (φ : SPTI4.Phase4) →
  (w : SDWS.DiscreteWave) →
  phaseAct (phaseInv4 φ) (phaseAct φ w)
    ≡
  w

PhaseActWaveAddTarget : Set
PhaseActWaveAddTarget =
  (φ : SPTI4.Phase4) →
  (w χ : SDWS.DiscreteWave) →
  phaseAct φ (SDWS.waveAdd w χ)
    ≡
  SDWS.waveAdd (phaseAct φ w) (phaseAct φ χ)

PhaseActScaleTarget : Set
PhaseActScaleTarget =
  (φ : SPTI4.Phase4) →
  (k : ℤ) →
  (w : SDWS.DiscreteWave) →
  phaseAct φ (SDWS.scaleWave k w)
    ≡
  SDWS.scaleWave k (phaseAct φ w)

GaugeTransform : Set
GaugeTransform = SPTI.ShiftPressurePoint → SPTI4.Phase4

constantGaugeTransform : SPTI4.Phase4 → GaugeTransform
constantGaugeTransform φ _ = φ

transformMatter :
  GaugeTransform →
  SSL.ShiftWaveField →
  SSL.ShiftWaveField
transformMatter g ψ s =
  phaseAct (g s) (ψ s)

record ShiftFiniteGaugeSymmetry : Set₁ where
  field
    GaugePhase : Set
    localGaugeTransform : Set
    matterAction :
      SPTI4.Phase4 → SDWS.DiscreteWave → SDWS.DiscreteWave
    matterFieldAction :
      GaugeTransform → SSL.ShiftWaveField → SSL.ShiftWaveField
    composeLawTarget : Set
    inverseLawTarget : Set
    additiveLawTarget : Set
    scaleLawTarget : Set
    nonClaimBoundary : List String

shiftFiniteGaugeSymmetry : ShiftFiniteGaugeSymmetry
shiftFiniteGaugeSymmetry =
  record
    { GaugePhase = SPTI4.Phase4
    ; localGaugeTransform = GaugeTransform
    ; matterAction = phaseAct
    ; matterFieldAction = transformMatter
    ; composeLawTarget = PhaseActComposeTarget
    ; inverseLawTarget = PhaseActInverseTarget
    ; additiveLawTarget = PhaseActWaveAddTarget
    ; scaleLawTarget = PhaseActScaleTarget
    ; nonClaimBoundary =
        "Finite C4 phase-symmetry package only"
        ∷ "Gauge phase is the four-class Phase4 table, not full continuous U(1)"
        ∷ "Matter action is repeated quarter-turn rotation over integer-pair waves"
        ∷ "Field action is local pointwise phase transport on the current three-point carrier"
        ∷ "Generic compose, inverse, additive, and scale equalities are exposed as target law surfaces, not closed proofs in this lane"
        ∷ "No continuum gauge connection, Lie algebra, or dynamic gauge-field claim is implied"
        ∷ []
    }
