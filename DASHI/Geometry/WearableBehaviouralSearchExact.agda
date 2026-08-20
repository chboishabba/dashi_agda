module DASHI.Geometry.WearableBehaviouralSearchExact where

------------------------------------------------------------------------
-- WEARABLE BEHAVIOURAL SEARCH
--
-- This is the theorem/API counterpart of SeaMeInIt's intended
-- `operator_basis_search.v2` semantics:
--
--   ordered panel action
--     -> actual materialised child geometry/state
--     -> consumer observation
--     -> bounded future-behaviour quotient
--     -> optional low-fidelity predictor with measured discrepancy.
--
-- No additive single-operation delta is treated as sequential materialisation.
-- Beam termination and finite behavioural stabilization remain distinct.
--
-- Literature calibration:
-- Thomas Dean and Robert Givan, "Model Minimization in Markov Decision
-- Processes", AAAI 1997.
-- Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon,
-- "A trust-region framework for managing the use of approximation models in
-- optimization", Structural Optimization 15 (1998), 16-23.
-- DOI: 10.1007/BF01197433.
-- Marc C. Kennedy and Anthony O'Hagan,
-- "Predicting the output from a complex computer code when fast approximations
-- are available", Biometrika 87(1), 2000. DOI: 10.1093/biomet/87.1.1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)

import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity
import DASHI.Core.BoundedLanguageBehaviouralCompletenessExact as Bounded
import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Geometry.AdaptiveWearableCompilerExact as Wearable

private
  variable
    Body Panel Fabric Provenance Coarse Decision : Set

WearableFineState : Set → Set → Set → Set → Set
WearableFineState = Wearable.WearableState

PanelFutureEquivalent :
  ∀ {Body Panel Fabric Provenance} →
  Wearable.AdaptiveWearableCompiler Body Panel Fabric Provenance →
  Wearable.WearableConsumer →
  Nat →
  Wearable.WearableState Body Panel Fabric Provenance →
  Wearable.WearableState Body Panel Fabric Provenance →
  Set
PanelFutureEquivalent compiler consumer depth =
  Governed.FutureEquivalent
    (Wearable.asGovernedTransition compiler)
    consumer depth

------------------------------------------------------------------------
-- Low/high fidelity pair for one action applied to one state.
--
-- low  = v1-style predicted coarse transition
-- high = coarse observation of the actually materialised v2 child.
------------------------------------------------------------------------

record PanelFidelityModel
    (Body Panel Fabric Provenance Coarse : Set)
    (compiler : Wearable.AdaptiveWearableCompiler
      Body Panel Fabric Provenance) : Set₁ where
  constructor panelFidelityModel
  field
    coarse : Wearable.WearableState Body Panel Fabric Provenance → Coarse
    predict : Wearable.PanelAction → Coarse → Coarse
    lowModelReference : String
    highBackendReference : String

open PanelFidelityModel public

PanelActionInput :
  ∀ {Body Panel Fabric Provenance} → Set
PanelActionInput {Body} {Panel} {Fabric} {Provenance} =
  Wearable.PanelAction × Wearable.WearableState Body Panel Fabric Provenance

panelLow :
  ∀ {Body Panel Fabric Provenance Coarse}
    {compiler : Wearable.AdaptiveWearableCompiler
      Body Panel Fabric Provenance} →
  PanelFidelityModel Body Panel Fabric Provenance Coarse compiler →
  PanelActionInput {Body} {Panel} {Fabric} {Provenance} → Coarse
panelLow model (action , state) =
  predict model action (coarse model state)

panelHigh :
  ∀ {Body Panel Fabric Provenance Coarse}
    {compiler : Wearable.AdaptiveWearableCompiler
      Body Panel Fabric Provenance} →
  PanelFidelityModel Body Panel Fabric Provenance Coarse compiler →
  PanelActionInput {Body} {Panel} {Fabric} {Provenance} → Coarse
panelHigh {compiler = compiler} model (action , state) =
  coarse model (Wearable.materialise compiler action state)

asFidelityPair :
  ∀ {Body Panel Fabric Provenance Coarse}
    {compiler : Wearable.AdaptiveWearableCompiler
      Body Panel Fabric Provenance} →
  PanelFidelityModel Body Panel Fabric Provenance Coarse compiler →
  Fidelity.FidelityPair
    (PanelActionInput {Body} {Panel} {Fabric} {Provenance})
    Coarse
asFidelityPair model =
  Fidelity.fidelityPair
    (panelLow model)
    (panelHigh model)
    (lowModelReference model)
    (highBackendReference model)

------------------------------------------------------------------------
-- Explicit discrepancy evidence for each materialised child.  This is the
-- formal commutation defect between predicted and actual coarse transition.
------------------------------------------------------------------------

record OperatorFidelityDiscrepancy
    {Body Panel Fabric Provenance Coarse}
    {compiler : Wearable.AdaptiveWearableCompiler
      Body Panel Fabric Provenance}
    (model : PanelFidelityModel Body Panel Fabric Provenance Coarse compiler)
    (action : Wearable.PanelAction)
    (state : Wearable.WearableState Body Panel Fabric Provenance) : Set₁ where
  constructor operatorFidelityDiscrepancy
  field
    WithinDefect : Coarse → Coarse → Set
    measured :
      WithinDefect
        (panelLow model (action , state))
        (panelHigh model (action , state))
    defectReference : String
    confidenceReference : String

open OperatorFidelityDiscrepancy public

------------------------------------------------------------------------
-- Behavioural stabilization certificate specialized to the wearable compiler.
------------------------------------------------------------------------

WearableSearchExhaustion :
  ∀ {Body Panel Fabric Provenance} →
  (compiler : Wearable.AdaptiveWearableCompiler
    Body Panel Fabric Provenance) →
  Wearable.WearableConsumer → Set₁
WearableSearchExhaustion compiler consumer =
  Bounded.LanguageRelativeBehaviouralExhaustion
    (Wearable.asGovernedTransition compiler)
    consumer

------------------------------------------------------------------------
-- Search-useful children and hard promotion are deliberately not identified.
------------------------------------------------------------------------

data SearchUtility : Set where
  usefulForSearch : SearchUtility
  dominatedForSearch : SearchUtility

data HardGateDisposition : Set where
  hardPromote : HardGateDisposition
  hardAbstain : HardGateDisposition
  hardReject : HardGateDisposition

record SearchChildDisposition : Set where
  constructor searchChildDisposition
  field
    searchUtility : SearchUtility
    hardGate : HardGateDisposition

open SearchChildDisposition public

------------------------------------------------------------------------
-- Failure classification after bounded/materialised search.  These labels do
-- not prove the diagnosis; they prevent serializer, panelization, physics and
-- policy failures from being collapsed into one generic "operator exhausted".
------------------------------------------------------------------------

data SearchFailureClass : Set where
  operatorExpressivity : SearchFailureClass
  serializerFailure : SearchFailureClass
  panelizationFailure : SearchFailureClass
  physicalOrMaterialFailure : SearchFailureClass
  authorityOrPolicyFailure : SearchFailureClass
  fidelityModelFailure : SearchFailureClass
  boundedSearchNoResult : SearchFailureClass

record SearchFailureDiagnosis : Set where
  constructor searchFailureDiagnosis
  field
    classification : SearchFailureClass
    evidenceReference : String
    generatorReference : String
    backendReference : String
    policyReference : String
    beamReference : String
    dedupReference : String

open SearchFailureDiagnosis public

record WearableSearchBoundary : Set where
  constructor wearableSearchBoundary
  field
    additiveDeltaIsNotSequentialMaterialisation : Bool
    searchUsefulDoesNotMeanHardPromoted : Bool
    beamNoResultDoesNotMeanGlobalExhaustion : Bool
    exhaustionMustBeScopedToFiniteSpecification : Bool
    failureDiagnosisRequiresPostSearchEvidence : Bool

canonicalWearableSearchBoundary : WearableSearchBoundary
canonicalWearableSearchBoundary =
  wearableSearchBoundary true true true true true
