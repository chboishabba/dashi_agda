module DASHI.Core.DualEffectAdaptiveFidelityExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Shared action/fidelity kernel for Animalexic, SeaMeInIt and LES.
-- An action can change the world, generate information, or do both.  Cheap
-- evaluation may be used only when a declared discrepancy relation is known to
-- preserve the terminal consumer's decision.
--
-- Literature vocabulary:
--   Frank Dellaert, "Factor Graphs and GTSAM: A Hands-on Introduction",
--   Georgia Tech technical tutorial (no DOI recorded here).
--   Chanho Kim, Fuxin Li, Arridhana Ciptadi, James M. Rehg,
--   "Multiple Hypothesis Tracking Revisited", ICCV 2015,
--   DOI 10.1109/ICCV.2015.533.
--
-- The exact constructions below are DASHI theorem surfaces; the references do
-- not import correctness of any application model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- 1. Dual-effect actions.
------------------------------------------------------------------------

data ActionEffectKind : Set where
  worldOnly : ActionEffectKind
  informationOnly : ActionEffectKind
  worldAndInformation : ActionEffectKind

record DualEffectActionSystem
    (State Action Evidence : Set) : Set₁ where
  constructor dualEffectActionSystem
  field
    kind : Action → ActionEffectKind
    worldEffect : Action → State → State
    evidenceEffect : Action → State → Evidence

open DualEffectActionSystem public

InformationOnly :
  ∀ {State Action Evidence} →
  DualEffectActionSystem State Action Evidence →
  Action → Set
InformationOnly system action =
  ∀ state → worldEffect system action state ≡ state

record InformationBearingIntervention
    {State Action Evidence : Set}
    (system : DualEffectActionSystem State Action Evidence)
    (action : Action) : Set₁ where
  constructor informationBearingIntervention
  field
    evidenceProduced : ∀ state → Evidence
    agreesWithSystem :
      ∀ state →
      evidenceProduced state ≡ evidenceEffect system action state

open InformationBearingIntervention public

------------------------------------------------------------------------
-- 2. Low/high fidelity evaluation with an application-supplied discrepancy
--    relation.  No probability or metric is manufactured by the core.
------------------------------------------------------------------------

record FidelityPair
    (Input Value : Set)
    (Within : Value → Value → Set) : Set₁ where
  constructor fidelityPair
  field
    low : Input → Value
    high : Input → Value
    discrepancyBound :
      ∀ input → Within (high input) (low input)

open FidelityPair public

record DecisionStableUnder
    {Value Decision : Set}
    (Within : Value → Value → Set)
    (decide : Value → Decision) : Set₁ where
  constructor decisionStableUnder
  field
    stable :
      ∀ highValue lowValue →
      Within highValue lowValue →
      decide highValue ≡ decide lowValue

open DecisionStableUnder public

lowFidelityDecisionAgrees :
  ∀ {Input Value Decision}
    {Within : Value → Value → Set}
    {decide : Value → Decision} →
  (pair : FidelityPair Input Value Within) →
  DecisionStableUnder Within decide →
  ∀ input →
  decide (high pair input) ≡ decide (low pair input)
lowFidelityDecisionAgrees pair stableDecision input =
  stable stableDecision
    (high pair input)
    (low pair input)
    (discrepancyBound pair input)

------------------------------------------------------------------------
-- 3. Adaptive fidelity policy.  Materialisation is a typed policy decision;
--    the core does not pretend cost, value-of-information and risk share one
--    canonical scalar.
------------------------------------------------------------------------

record AdaptiveFidelityPolicy
    (Input : Set) : Set₁ where
  constructor adaptiveFidelityPolicy
  field
    NeedsHighFidelity : Input → Set
    CheapDecisionSafe : Input → Set
    highFidelityCostReference : Input → String
    informationValueReference : Input → String
    riskReference : Input → String
    unsafeCheapRequiresHigh :
      ∀ input →
      ¬ CheapDecisionSafe input →
      NeedsHighFidelity input

open AdaptiveFidelityPolicy public

record SafeCheapEvaluation
    {Input : Set}
    (policy : AdaptiveFidelityPolicy Input)
    (input : Input) : Set where
  constructor safeCheapEvaluation
  field
    safe : CheapDecisionSafe policy input

open SafeCheapEvaluation public

------------------------------------------------------------------------
-- 4. A dual-control trace keeps both state transitions and newly generated
--    evidence.  The generated evidence is not silently promoted to truth.
------------------------------------------------------------------------

record DualEffectOutcome
    (State Evidence : Set) : Set where
  constructor dualEffectOutcome
  field
    nextState : State
    generatedEvidence : Evidence

open DualEffectOutcome public

executeDualEffect :
  ∀ {State Action Evidence} →
  DualEffectActionSystem State Action Evidence →
  Action → State → DualEffectOutcome State Evidence
executeDualEffect system action state =
  dualEffectOutcome
    (worldEffect system action state)
    (evidenceEffect system action state)

informationOnlyPreservesWorld :
  ∀ {State Action Evidence}
    {system : DualEffectActionSystem State Action Evidence}
    {action : Action} →
  InformationOnly system action →
  ∀ state →
  nextState (executeDualEffect system action state) ≡ state
informationOnlyPreservesWorld informationOnly state =
  informationOnly state

------------------------------------------------------------------------
-- 5. Active experiment selection remains consumer/policy relative.
------------------------------------------------------------------------

record InformationActionPolicy
    (Action : Set) : Set₁ where
  constructor informationActionPolicy
  field
    admissibleInformationAction : Action → Set
    preferableForInformation : Action → Action → Set
    preferenceBasis : String
    costBasis : String
    consumerReference : String

open InformationActionPolicy public

------------------------------------------------------------------------
-- Shared boundary.
------------------------------------------------------------------------

record DualEffectAdaptiveFidelityBoundary : Set where
  constructor dualEffectAdaptiveFidelityBoundary
  field
    actionMayChangeWorldAndInformationTogether : Bool
    informationOnlyActionNeedNotChangeWorld : Bool
    lowFidelityNeedsDiscrepancyControl : Bool
    discrepancyControlIsConsumerRelative : Bool
    safeCheapEvaluationNeedsDecisionStability : Bool
    highFidelityAllocationIsAPolicyDecision : Bool
    informationValueIsNotAutomaticallyProbability : Bool
    generatedEvidenceDoesNotAutomaticallyPromoteAuthority : Bool

open DualEffectAdaptiveFidelityBoundary public

canonicalDualEffectAdaptiveFidelityBoundary :
  DualEffectAdaptiveFidelityBoundary
canonicalDualEffectAdaptiveFidelityBoundary =
  dualEffectAdaptiveFidelityBoundary
    true true true true true true true true
