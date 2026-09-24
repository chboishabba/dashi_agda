module DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedCycleBookkeepingExact where

------------------------------------------------------------------------
-- NATIVE PORT: RELEASED SELECTED-CYCLE BOOKKEEPING
--
-- This is the first proof-bearing body from
--   NavierStokes/ActualCandidateConstruction.lean
-- moved into Agda.
--
-- Scope of this tranche:
--   * one fixed selected recurrence,
--   * exact stage counter,
--   * residual band 2^(j+1),
--   * labels/carrier/representation/base error preserved by the recurrence,
--   * alias history accumulated one stage at a time.
--
-- The analytic contents of one correction step (particular/signed/mean fields,
-- estimates, support, away extensions) are intentionally represented by one
-- proof-relevant StepEvidence object.  This module proves the recurrence laws
-- once; later ports only have to construct the actual StepEvidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedActualCandidatePhysicalInputsExact
  as Inputs

------------------------------------------------------------------------
-- 1. Exact dyadic residual-band arithmetic used by the released recurrence.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

residualBandAt : Nat → Nat
residualBandAt j = pow2 (suc j)

residualBandAtZero : residualBandAt zero ≡ 2
residualBandAtZero = refl

residualBandAtSucc :
  (j : Nat) →
  residualBandAt (suc j) ≡ 2 * residualBandAt j
residualBandAtSucc j = refl

------------------------------------------------------------------------
-- 2. Proof-relevant selected physical payload.
--
-- These are not booleans/status flags.  A caller chooses the actual types
-- used for labels, carriers, representations, base errors and alias terms.
------------------------------------------------------------------------

record ReleasedCyclePayloadSurface : Set₁ where
  field
    Labels : Set
    Carrier : Set
    Representation : Set
    BaseError : Set
    AliasTerm : Set

open ReleasedCyclePayloadSurface public

record ReleasedCycleInitialPayload
    (P : ReleasedCyclePayloadSurface) : Set₁ where
  field
    labels : Labels P
    carrier : Carrier P
    representation : Representation P
    baseError : BaseError P
    initialTemporalAlias : AliasTerm P
    initialPressureAlias : AliasTerm P

open ReleasedCycleInitialPayload public

------------------------------------------------------------------------
-- 3. Native cycle state.
------------------------------------------------------------------------

record ReleasedCycleState
    (P : ReleasedCyclePayloadSurface) : Set₁ where
  constructor released-cycle-state
  field
    stage : Nat
    labels : Labels P
    carrier : Carrier P
    representation : Representation P
    baseError : BaseError P
    temporalAliasHistory : List (AliasTerm P)
    currentPressureAlias : AliasTerm P
    residualBand : Nat
    residualBandExact : residualBand ≡ residualBandAt stage

open ReleasedCycleState public

initialState :
  ∀ {P} →
  ReleasedCycleInitialPayload P →
  ReleasedCycleState P
initialState I =
  released-cycle-state
    zero
    (ReleasedCycleInitialPayload.labels I)
    (ReleasedCycleInitialPayload.carrier I)
    (ReleasedCycleInitialPayload.representation I)
    (ReleasedCycleInitialPayload.baseError I)
    (ReleasedCycleInitialPayload.initialTemporalAlias I ∷ [])
    (ReleasedCycleInitialPayload.initialPressureAlias I)
    (residualBandAt zero)
    refl

------------------------------------------------------------------------
-- 4. One actual correction step has one new alias contribution and evidence
-- that the source-fixed payload is retained.
------------------------------------------------------------------------

record ReleasedCycleStepEvidence
    {P : ReleasedCyclePayloadSurface}
    (state : ReleasedCycleState P) : Set₁ where
  field
    newTemporalAlias : AliasTerm P
    newPressureAlias : AliasTerm P

    nextLabels : Labels P
    nextCarrier : Carrier P
    nextRepresentation : Representation P
    nextBaseError : BaseError P

    labelsPreserved : nextLabels ≡ labels state
    carrierPreserved : nextCarrier ≡ carrier state
    representationPreserved :
      nextRepresentation ≡ representation state
    baseErrorPreserved : nextBaseError ≡ baseError state

open ReleasedCycleStepEvidence public

stepFromEvidence :
  ∀ {P} {state : ReleasedCycleState P} →
  ReleasedCycleStepEvidence state →
  ReleasedCycleState P
stepFromEvidence {state = state} E =
  released-cycle-state
    (suc (stage state))
    (nextLabels E)
    (nextCarrier E)
    (nextRepresentation E)
    (nextBaseError E)
    (newTemporalAlias E ∷ temporalAliasHistory state)
    (newPressureAlias E)
    (residualBandAt (suc (stage state)))
    refl

------------------------------------------------------------------------
-- 5. Fixed selected recurrence.
------------------------------------------------------------------------

record ReleasedSelectedCycleKernel
    (P : ReleasedCyclePayloadSurface) : Set₁ where
  field
    initial : ReleasedCycleInitialPayload P

    stepEvidence :
      (state : ReleasedCycleState P) →
      ReleasedCycleStepEvidence state

open ReleasedSelectedCycleKernel public

selectedCycle :
  ∀ {P} →
  ReleasedSelectedCycleKernel P →
  Nat →
  ReleasedCycleState P
selectedCycle K zero = initialState (initial K)
selectedCycle K (suc j) =
  stepFromEvidence
    (stepEvidence K (selectedCycle K j))

------------------------------------------------------------------------
-- 6. Native inhabitants of the bookkeeping laws.
------------------------------------------------------------------------

selectedCycleStage :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  stage (selectedCycle K j) ≡ j
selectedCycleStage K zero = refl
selectedCycleStage K (suc j)
  rewrite selectedCycleStage K j = refl

selectedCycleResidualBand :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  residualBand (selectedCycle K j) ≡ residualBandAt j
selectedCycleResidualBand K j =
  residualBandExact (selectedCycle K j)

selectedCycleLabels :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  labels (selectedCycle K j) ≡
  ReleasedCycleInitialPayload.labels (initial K)
selectedCycleLabels K zero = refl
selectedCycleLabels K (suc j)
  rewrite labelsPreserved
    (stepEvidence K (selectedCycle K j))
  | selectedCycleLabels K j = refl

selectedCycleCarrier :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  carrier (selectedCycle K j) ≡
  ReleasedCycleInitialPayload.carrier (initial K)
selectedCycleCarrier K zero = refl
selectedCycleCarrier K (suc j)
  rewrite carrierPreserved
    (stepEvidence K (selectedCycle K j))
  | selectedCycleCarrier K j = refl

selectedCycleRepresentation :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  representation (selectedCycle K j) ≡
  ReleasedCycleInitialPayload.representation (initial K)
selectedCycleRepresentation K zero = refl
selectedCycleRepresentation K (suc j)
  rewrite representationPreserved
    (stepEvidence K (selectedCycle K j))
  | selectedCycleRepresentation K j = refl

selectedCycleBaseError :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  baseError (selectedCycle K j) ≡
  ReleasedCycleInitialPayload.baseError (initial K)
selectedCycleBaseError K zero = refl
selectedCycleBaseError K (suc j)
  rewrite baseErrorPreserved
    (stepEvidence K (selectedCycle K j))
  | selectedCycleBaseError K j = refl

selectedCycleTemporalAliasStep :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  temporalAliasHistory (selectedCycle K (suc j))
  ≡
  newTemporalAlias (stepEvidence K (selectedCycle K j))
    ∷ temporalAliasHistory (selectedCycle K j)
selectedCycleTemporalAliasStep K j = refl

selectedCyclePressureAliasCurrent :
  ∀ {P} →
  (K : ReleasedSelectedCycleKernel P) →
  (j : Nat) →
  currentPressureAlias (selectedCycle K (suc j))
  ≡ newPressureAlias (stepEvidence K (selectedCycle K j))
selectedCyclePressureAliasCurrent K j = refl

------------------------------------------------------------------------
-- 7. Source-fixed selected coordinates are attached to this recurrence.
------------------------------------------------------------------------

selectedBudgetMatchesReleasedSource :
  Inputs.selectedBudget ≡ zero
selectedBudgetMatchesReleasedSource = refl

selectedConstructionCoordinates :
  Inputs.ReleasedSelectedConstructionCoordinates
selectedConstructionCoordinates =
  Inputs.canonicalReleasedSelectedConstructionCoordinates

selectedCycleBookkeepingPorted : Bool
selectedCycleBookkeepingPorted = true

selectedResidualBandLawPorted : Bool
selectedResidualBandLawPorted = true

selectedLabelsPreservationPorted : Bool
selectedLabelsPreservationPorted = true

selectedCarrierPreservationPorted : Bool
selectedCarrierPreservationPorted = true

selectedRepresentationPreservationPorted : Bool
selectedRepresentationPreservationPorted = true

selectedBaseErrorPreservationPorted : Bool
selectedBaseErrorPreservationPorted = true

selectedTemporalAliasAccumulationPorted : Bool
selectedTemporalAliasAccumulationPorted = true

selectedCurrentPressureAliasPorted : Bool
selectedCurrentPressureAliasPorted = true

analyticStepEvidencePopulatedHere : Bool
analyticStepEvidencePopulatedHere = false

selectedCycleBookkeepingPortedIsTrue :
  selectedCycleBookkeepingPorted ≡ true
selectedCycleBookkeepingPortedIsTrue = refl

selectedResidualBandLawPortedIsTrue :
  selectedResidualBandLawPorted ≡ true
selectedResidualBandLawPortedIsTrue = refl

analyticStepEvidencePopulatedHereIsFalse :
  analyticStepEvidencePopulatedHere ≡ false
analyticStepEvidencePopulatedHereIsFalse = refl
