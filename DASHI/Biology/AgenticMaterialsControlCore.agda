module DASHI.Biology.AgenticMaterialsControlCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set; Set₁)

------------------------------------------------------------------------
-- Agentic materials: minimal control-theoretic core.
--
-- Agency is not identified with complexity, replication, persistence, or
-- entropy reduction alone.  An agentic material carries:
--
--   * a material state,
--   * an observation channel,
--   * an action channel,
--   * a viability / target defect,
--   * a closed-loop policy, and
--   * a proof that corrective action improves defect away from target.
--
-- Thermodynamic order is local and paid for by an open-system throughput;
-- no global entropy decrease is asserted.  The formalism is deliberately
-- substrate-neutral: cells, tissues, collectives, and engineered living
-- materials may instantiate it at different scales.

record OpenSystemBookkeeping : Set₁ where
  field
    EnergyCarrier : Set
    EntropyCarrier : Set

    intake : EnergyCarrier
    exportedWaste : EntropyCarrier

    localOrderMaintained : Bool
    localOrderMaintainedIsTrue : localOrderMaintained ≡ true

    globalEntropyDecreaseClaimed : Bool
    globalEntropyDecreaseClaimedIsFalse :
      globalEntropyDecreaseClaimed ≡ false

open OpenSystemBookkeeping public

record AgenticMaterial : Set₁ where
  field
    State : Set
    Observation : Set
    Action : Set
    Defect : Set

    observe : State → Observation
    policy : Observation → Action
    actuate : Action → State → State
    defect : State → Defect

    target : State
    better : Defect → Defect → Set

    targetHasNoCorrectiveMotion :
      actuate (policy (observe target)) target ≡ target

    correctionImproves :
      (x : State) →
      x ≡ target →
      actuate (policy (observe x)) x ≡ target

    offTargetCorrectionImproves :
      (x : State) →
      (x ≡ target → Bool) →
      better
        (defect (actuate (policy (observe x)) x))
        (defect x)

    thermodynamics : OpenSystemBookkeeping

open AgenticMaterial public

closedLoopStep :
  (M : AgenticMaterial) →
  State M →
  State M
closedLoopStep M x =
  actuate M (policy M (observe M x)) x

closedLoopTargetFixed :
  (M : AgenticMaterial) →
  closedLoopStep M (target M) ≡ target M
closedLoopTargetFixed M =
  targetHasNoCorrectiveMotion M

closedLoopCorrectionImproves :
  (M : AgenticMaterial) →
  (x : State M) →
  (x ≡ target M → Bool) →
  better M
    (defect M (closedLoopStep M x))
    (defect M x)
closedLoopCorrectionImproves M x offTarget =
  offTargetCorrectionImproves M x offTarget

agenticMaterialDoesNotClaimGlobalEntropyDecrease :
  (M : AgenticMaterial) →
  globalEntropyDecreaseClaimed (thermodynamics M) ≡ false
agenticMaterialDoesNotClaimGlobalEntropyDecrease M =
  globalEntropyDecreaseClaimedIsFalse (thermodynamics M)

------------------------------------------------------------------------
-- Minimal agency gate.
--
-- Replication or templated propagation is not sufficient.  This blocks the
-- slide from prion-like conformational propagation to biological agency.

record TemplatedPropagation : Set₁ where
  field
    Carrier : Set
    propagate : Carrier → Carrier → Carrier
    selfAmplifying : Bool
    selfAmplifyingIsTrue : selfAmplifying ≡ true

open TemplatedPropagation public

record AgencyGate (P : TemplatedPropagation) : Set₁ where
  field
    hasObservationChannel : Bool
    hasActionChannel : Bool
    hasTargetDefect : Bool
    hasCorrectiveFeedback : Bool

    observationRequired :
      hasObservationChannel ≡ true

    actionRequired :
      hasActionChannel ≡ true

    targetDefectRequired :
      hasTargetDefect ≡ true

    correctiveFeedbackRequired :
      hasCorrectiveFeedback ≡ true

open AgencyGate public

record PrionLikeBoundary (P : TemplatedPropagation) : Set where
  field
    observationChannelAbsent : Bool
    observationChannelAbsentIsTrue :
      observationChannelAbsent ≡ true

    targetDefectAbsent : Bool
    targetDefectAbsentIsTrue :
      targetDefectAbsent ≡ true

    correctiveFeedbackAbsent : Bool
    correctiveFeedbackAbsentIsTrue :
      correctiveFeedbackAbsent ≡ true

    agencyPromoted : Bool
    agencyPromotedIsFalse :
      agencyPromoted ≡ false

open PrionLikeBoundary public

prionLikePropagationIsNotAgency :
  {P : TemplatedPropagation} →
  (B : PrionLikeBoundary P) →
  agencyPromoted B ≡ false
prionLikePropagationIsNotAgency B =
  agencyPromotedIsFalse B

------------------------------------------------------------------------
-- Origins-of-life ladder.
--
-- These stages are typed distinctions, not a claim that history followed a
-- unique linear sequence.  The agency threshold is crossed only when a
-- compartment couples sensing, target-relative defect, and corrective work.

data OriginStage : Set where
  geochemicalGradient : OriginStage
  autocatalyticNetwork : OriginStage
  compartmentalisedMetabolism : OriginStage
  closedLoopProtoAgency : OriginStage
  multiscaleBiologicalAgency : OriginStage

stageHasEnergyGradient : OriginStage → Bool
stageHasEnergyGradient geochemicalGradient = true
stageHasEnergyGradient autocatalyticNetwork = true
stageHasEnergyGradient compartmentalisedMetabolism = true
stageHasEnergyGradient closedLoopProtoAgency = true
stageHasEnergyGradient multiscaleBiologicalAgency = true

stageHasCorrectiveTarget : OriginStage → Bool
stageHasCorrectiveTarget geochemicalGradient = false
stageHasCorrectiveTarget autocatalyticNetwork = false
stageHasCorrectiveTarget compartmentalisedMetabolism = false
stageHasCorrectiveTarget closedLoopProtoAgency = true
stageHasCorrectiveTarget multiscaleBiologicalAgency = true

protoAgencyThresholdWitness :
  stageHasCorrectiveTarget closedLoopProtoAgency ≡ true
protoAgencyThresholdWitness = refl

geochemicalGradientNotYetAgentic :
  stageHasCorrectiveTarget geochemicalGradient ≡ false
geochemicalGradientNotYetAgentic = refl

------------------------------------------------------------------------
-- Multiscale competency.
--
-- A higher-scale material is not inferred merely from many lower-scale
-- agents.  A composition witness must provide an observation/action lift and
-- show that the higher target remains fixed under the induced closed loop.

record MultiscaleComposition
  (Lower Higher : AgenticMaterial) : Set₁ where
  field
    liftState : State Lower → State Higher
    liftObservation : Observation Lower → Observation Higher
    liftAction : Action Lower → Action Higher

    observationCommutes :
      (x : State Lower) →
      observe Higher (liftState x) ≡
      liftObservation (observe Lower x)

    targetCommutes :
      liftState (target Lower) ≡ target Higher

    higherTargetStable :
      closedLoopStep Higher (target Higher) ≡ target Higher

open MultiscaleComposition public

multiscaleTargetStability :
  {Lower Higher : AgenticMaterial} →
  (C : MultiscaleComposition Lower Higher) →
  closedLoopStep Higher (target Higher) ≡ target Higher
multiscaleTargetStability C =
  higherTargetStable C
