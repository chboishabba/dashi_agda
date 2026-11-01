module DASHI.Physics.ShiftFieldTheoryConsistency where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftDiscreteActionPrinciple as SDAP
open import DASHI.Physics.ShiftDiscreteContinuityCurrent as SDCC
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftFiniteEvolutionWitness as SFEW
open import DASHI.Physics.ShiftFinitePathSum as SFPS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveEnergyHierarchy as SWEH
open import DASHI.Physics.ShiftWaveGlobalUpdate as SWGU

------------------------------------------------------------------------
-- Theorem-thin finite coherence surface over the current field-theory lane.
--
-- This module does not promote a single large theorem. It only packages a
-- compact set of exact bounded compatibilities showing that:
--   * the coarse Skolem witness is the current one-pass global update,
--   * updated local energy is just local energy viewed on that witness field,
--   * action density is exactly local energy + local current magnitude,
--   * the bounded path-sum is exactly the sum of its two explicit path
--     contributions,
--   * those two histories follow the same carrier advance used by the current
--     structured wave state.
--
-- No continuum continuity law, Noether theorem, variational dominance, or
-- path-selection claim is implied here.

coarseWitnessField :
  SSL.ShiftWaveField →
  SSL.ShiftWaveField
coarseWitnessField ψ =
  SFEW.SkolemEvolutionWitness.witnessField
    (SFEW.coarseOnePassWitness ψ)

CoarseWitnessAdmissibility : Set
CoarseWitnessAdmissibility =
  (ψ : SSL.ShiftWaveField) →
  SFEW.FiniteEvolutionObligation.targetField
    (SFEW.coarseOnePassObligation ψ)
    ≡
  coarseWitnessField ψ

coarseWitnessAdmissibility : CoarseWitnessAdmissibility
coarseWitnessAdmissibility ψ =
  SFEW.SkolemEvolutionWitness.witnessSatisfies
    (SFEW.coarseOnePassWitness ψ)

CoarseWitnessUpdatePointwise : Set
CoarseWitnessUpdatePointwise =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  coarseWitnessField ψ s
    ≡
  SWGU.coarseGlobalUpdate ψ s

coarseWitnessUpdatePointwise :
  CoarseWitnessUpdatePointwise
coarseWitnessUpdatePointwise ψ s = refl

CoarseWitnessUpdatedEnergyCompatibility : Set
CoarseWitnessUpdatedEnergyCompatibility =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  SDCC.coarseUpdatedLocalEnergy ψ s
    ≡
  SDCC.coarseLocalEnergy (coarseWitnessField ψ) s

coarseWitnessUpdatedEnergyCompatibility :
  CoarseWitnessUpdatedEnergyCompatibility
coarseWitnessUpdatedEnergyCompatibility ψ s = refl

CoarseWitnessActionCurrentCompatibility : Set
CoarseWitnessActionCurrentCompatibility =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  SDAP.coarseActionDensity ψ s
    ≡
  SDCC.coarseLocalEnergy ψ s
    +ℤ
  SDCC.coarseLocalCurrentMagnitude ψ s

coarseWitnessActionCurrentCompatibility :
  CoarseWitnessActionCurrentCompatibility
coarseWitnessActionCurrentCompatibility ψ s = refl

PrimaryHistoryAdvanceCompatibility : Set
PrimaryHistoryAdvanceCompatibility =
  (w : SPWSI.ShiftWavePhaseState) →
  Σ
    (SFPS.FinitePathHistory.middle (SFPS.primaryHistory w)
       ≡
     SPWSI.advanceWavePhaseState w)
    (λ _ →
      SFPS.FinitePathHistory.end (SFPS.primaryHistory w)
        ≡
      SPWSI.advanceWavePhaseState
        (SPWSI.advanceWavePhaseState w))

ShiftedHistoryAdvanceCompatibility : Set
ShiftedHistoryAdvanceCompatibility =
  (w : SPWSI.ShiftWavePhaseState) →
  Σ
    (SFPS.FinitePathHistory.start (SFPS.shiftedHistory w)
       ≡
     SPWSI.advanceWavePhaseState w)
    (λ _ →
      SFPS.FinitePathHistory.end (SFPS.shiftedHistory w)
        ≡
      SPWSI.advanceWavePhaseState
        (SPWSI.advanceWavePhaseState
          (SPWSI.advanceWavePhaseState w)))

primaryHistoryAdvanceCompatibility :
  PrimaryHistoryAdvanceCompatibility
primaryHistoryAdvanceCompatibility w = refl , refl

shiftedHistoryAdvanceCompatibility :
  ShiftedHistoryAdvanceCompatibility
shiftedHistoryAdvanceCompatibility w = refl , refl

BoundedPathWeightCompatibility : Set
BoundedPathWeightCompatibility =
  (w : SPWSI.ShiftWavePhaseState) →
  SFPS.boundedPathSum w
    ≡
  SDWS.waveAdd
    (SFPS.pathContribution (SFPS.primaryHistory w))
    (SFPS.pathContribution (SFPS.shiftedHistory w))

boundedPathWeightCompatibility :
  BoundedPathWeightCompatibility
boundedPathWeightCompatibility w = refl

record ShiftFieldTheoryConsistency : Setω where
  field
    coarseField : Set
    waveState : Set
    coarseEnergyHierarchy : SWEH.ShiftWaveEnergyHierarchy
    continuityCurrent : SDCC.ShiftDiscreteContinuityCurrent
    actionPrinciple : SDAP.ShiftDiscreteActionPrinciple
    evolutionWitness : SFEW.ShiftFiniteEvolutionWitness
    finitePathSum : SFPS.ShiftFinitePathSum
    witnessAdmissibility : Set
    witnessUpdatePointwise : Set
    witnessUpdatedEnergyCompatibility : Set
    witnessActionCurrentCompatibility : Set
    primaryPathAdvanceCompatibility : Set
    shiftedPathAdvanceCompatibility : Set
    pathWeightCompatibility : Set
    nonClaimBoundary : List String

shiftFieldTheoryConsistency :
  ShiftFieldTheoryConsistency
shiftFieldTheoryConsistency =
  record
    { coarseField = SSL.ShiftWaveField
    ; waveState = SPWSI.ShiftWavePhaseState
    ; coarseEnergyHierarchy = SWEH.shiftWaveEnergyHierarchy
    ; continuityCurrent = SDCC.shiftDiscreteContinuityCurrent
    ; actionPrinciple = SDAP.shiftDiscreteActionPrinciple
    ; evolutionWitness = SFEW.shiftFiniteEvolutionWitness
    ; finitePathSum = SFPS.shiftFinitePathSum
    ; witnessAdmissibility = CoarseWitnessAdmissibility
    ; witnessUpdatePointwise = CoarseWitnessUpdatePointwise
    ; witnessUpdatedEnergyCompatibility =
        CoarseWitnessUpdatedEnergyCompatibility
    ; witnessActionCurrentCompatibility =
        CoarseWitnessActionCurrentCompatibility
    ; primaryPathAdvanceCompatibility =
        PrimaryHistoryAdvanceCompatibility
    ; shiftedPathAdvanceCompatibility =
        ShiftedHistoryAdvanceCompatibility
    ; pathWeightCompatibility =
        BoundedPathWeightCompatibility
    ; nonClaimBoundary =
        "Finite field-theory consistency package only"
        ∷ "coarse witness admissibility is exact equality to the current one-pass global update"
        ∷ "updated local energy is only tied pointwise to that witness field on the current coarse carrier"
        ∷ "action/current compatibility is only the explicit bookkeeping identity action = local energy + local current magnitude"
        ∷ "bounded path compatibility is only the exact two-history decomposition already present in the finite path-sum package"
        ∷ "primary and shifted histories are only shown to follow the current deterministic bounded advance"
        ∷ "No continuum continuity law, Noether theorem, stationary-action theorem, dominance theorem, or path-selection claim is implied"
        ∷ []
    }
