module DASHI.Reasoning.TypedHyperfabricSelectedSectionActionRealizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact as SectionReduction
import DASHI.Reasoning.TypedHyperfabricActionCrossingTransportExact as Crossing

------------------------------------------------------------------------
-- SELECTED-SECTION ACTION REALIZATION
--
-- Consumer-relative reduction acts on Set-sized SectionCode values, while the
-- physical hyperfabric state remains a GlobalSection in Set₁.  Future safety of
-- the code-level reduction is not by itself a mechanistic realization claim.
--
-- This bridge pays exactly the missing square: every declared code action must
-- realize as one physical crossing event, and realizing after the code-level
-- fine step must equal transporting the realized GlobalSection by that event.
------------------------------------------------------------------------

record SelectedSectionActionRealization
    {Vertex Edge CodeAction PhysicalAction Observation : Set}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    (bridge :
      SectionReduction.HyperfabricSectionReduction
        {Action = CodeAction}
        {Observation = Observation}
        fabric)
    (transport :
      Crossing.HyperfabricCrossingTransport
        {Action = PhysicalAction}
        fabric) : Set₁ where
  constructor selected-section-action-realization
  field
    realizeAction :
      CodeAction → Trace.CrossingEvent Edge PhysicalAction
    actionRealizationCommutes :
      (action : CodeAction) →
      (code : SectionReduction.SectionCode
        (SectionReduction.selectedSections bridge)) →
      SectionReduction.realizeSection
        (SectionReduction.selectedSections bridge)
        (Reduction.fineStep
          (SectionReduction.sectionReduction bridge)
          action
          code)
      ≡
      Crossing.crossingStep transport (realizeAction action)
        (SectionReduction.realizeSection
          (SectionReduction.selectedSections bridge)
          code)
    realizationReceipt : String

open SelectedSectionActionRealization public

realizeActionTrace :
  ∀ {Vertex Edge CodeAction PhysicalAction Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {bridge :
      SectionReduction.HyperfabricSectionReduction
        {Action = CodeAction}
        {Observation = Observation}
        fabric}
    {transport :
      Crossing.HyperfabricCrossingTransport
        {Action = PhysicalAction}
        fabric} →
  SelectedSectionActionRealization bridge transport →
  List CodeAction →
  Trace.ActionTrace Edge PhysicalAction
realizeActionTrace realization [] = []
realizeActionTrace realization (action ∷ actions) =
  realizeAction realization action ∷ realizeActionTrace realization actions

selectedActionTraceRealizationCommutes :
  ∀ {Vertex Edge CodeAction PhysicalAction Observation}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {bridge :
      SectionReduction.HyperfabricSectionReduction
        {Action = CodeAction}
        {Observation = Observation}
        fabric}
    {transport :
      Crossing.HyperfabricCrossingTransport
        {Action = PhysicalAction}
        fabric} →
  (realization : SelectedSectionActionRealization bridge transport) →
  (actions : List CodeAction) →
  (code : SectionReduction.SectionCode
    (SectionReduction.selectedSections bridge)) →
  SectionReduction.realizeSection
    (SectionReduction.selectedSections bridge)
    (Reduction.run
      (Reduction.fineStep (SectionReduction.sectionReduction bridge))
      actions
      code)
  ≡
  Crossing.transportTrace transport
    (realizeActionTrace realization actions)
    (SectionReduction.realizeSection
      (SectionReduction.selectedSections bridge)
      code)
selectedActionTraceRealizationCommutes realization [] code = refl
selectedActionTraceRealizationCommutes
  {bridge = bridge} {transport = transport}
  realization (action ∷ actions) code =
  trans
    (selectedActionTraceRealizationCommutes
      realization
      actions
      (Reduction.fineStep
        (SectionReduction.sectionReduction bridge)
        action
        code))
    (cong
      (Crossing.transportTrace transport
        (realizeActionTrace realization actions))
      (actionRealizationCommutes realization action code))

------------------------------------------------------------------------
-- Finite exact specimen: both the selected-section and physical crossing
-- fixtures use identity dynamics, so the realization square closes by refl.
------------------------------------------------------------------------

finiteActionRealization :
  SelectedSectionActionRealization
    SectionReduction.specBridge
    Crossing.finiteTransport
finiteActionRealization = selected-section-action-realization
  (λ _ → Crossing.finiteCrossing)
  (λ _ _ → refl)
  "the finite selected-section identity action realizes as the finite identity crossing transport"

finiteActionTraceRealization :
  SectionReduction.realizeSpecSection
    (Reduction.run
      (Reduction.fineStep SectionReduction.specReduction)
      (tt ∷ tt ∷ [])
      SectionReduction.leftCode)
  ≡
  Crossing.transportTrace
    Crossing.finiteTransport
    (realizeActionTrace finiteActionRealization (tt ∷ tt ∷ []))
    SectionReduction.leftSection
finiteActionTraceRealization =
  selectedActionTraceRealizationCommutes
    finiteActionRealization
    (tt ∷ tt ∷ [])
    SectionReduction.leftCode

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data ConsumerFutureSafetyAloneImpliesPhysicalRealization : Set where

data PhysicalTransportAloneAuthorizesConsumerReduction : Set where

data ReducedCodeEqualityImpliesPhysicalSectionIdentity : Set where

consumerFutureSafetyAloneDoesNotImplyPhysicalRealization :
  ConsumerFutureSafetyAloneImpliesPhysicalRealization → ⊥
consumerFutureSafetyAloneDoesNotImplyPhysicalRealization ()

physicalTransportAloneDoesNotAuthorizeConsumerReduction :
  PhysicalTransportAloneAuthorizesConsumerReduction → ⊥
physicalTransportAloneDoesNotAuthorizeConsumerReduction ()

reducedCodeEqualityDoesNotImplyPhysicalSectionIdentity :
  ReducedCodeEqualityImpliesPhysicalSectionIdentity → ⊥
reducedCodeEqualityDoesNotImplyPhysicalSectionIdentity ()

record SelectedSectionActionRealizationBoundary : Set where
  constructor selected-section-action-realization-boundary
  field
    selectedSectionCodesRemainSetSized : Bool
    physicalSectionsRemainGlobalSections : Bool
    oneStepRealizationSquareRequired : Bool
    oneStepSquareLiftsToOrderedActionTrace : Bool
    consumerFutureSafetyAloneImpliesPhysicalRealization : Bool
    consumerFutureSafetyAloneImpliesPhysicalRealizationIsFalse :
      consumerFutureSafetyAloneImpliesPhysicalRealization ≡ false
    physicalTransportAloneAuthorizesConsumerReduction : Bool
    physicalTransportAloneAuthorizesConsumerReductionIsFalse :
      physicalTransportAloneAuthorizesConsumerReduction ≡ false
    reducedCodeEqualityImpliesPhysicalSectionIdentity : Bool
    reducedCodeEqualityImpliesPhysicalSectionIdentityIsFalse :
      reducedCodeEqualityImpliesPhysicalSectionIdentity ≡ false
    boundaryNote : String

open SelectedSectionActionRealizationBoundary public

canonicalSelectedSectionActionRealizationBoundary :
  SelectedSectionActionRealizationBoundary
canonicalSelectedSectionActionRealizationBoundary =
  selected-section-action-realization-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "Consumer-safe code dynamics become a physical hyperfabric realization only when an explicit action-realization square commutes. That square lifts to ordered traces, while Set-sized reduction codes and Set₁ GlobalSections remain distinct and reduced equality still does not imply physical section identity."
