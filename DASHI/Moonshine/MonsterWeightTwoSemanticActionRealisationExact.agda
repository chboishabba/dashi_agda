module DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as MonsterVOA
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Nested

------------------------------------------------------------------------
-- WEIGHT-TWO ACTION REALISATION
--
-- GradedRepresentation owns G -> End and traces, but End is abstract: it does
-- not itself contain an evaluation End -> V -> V.  This owner isolates that
-- missing action-realisation payment and then transports the realised grade-2
-- action across the semantic weight-two carrier.
------------------------------------------------------------------------

record EndomorphismEvaluation
    {G K : Set}
    (group : GR.Group G)
    (representation : GR.FiniteDimensionalRepresentation G K group) : Setω where
  field
    applyEnd : GR.End representation → GR.V representation → GR.V representation

    identityEvaluates :
      (v : GR.V representation) →
      applyEnd (GR.identityEnd representation) v ≡ v

    compositionEvaluates :
      (left right : GR.End representation) →
      (v : GR.V representation) →
      applyEnd (GR._∘End_ representation left right) v
      ≡ applyEnd left (applyEnd right v)

open EndomorphismEvaluation public

groupActionOnVectors :
  {G K : Set} →
  {group : GR.Group G} →
  {representation : GR.FiniteDimensionalRepresentation G K group} →
  EndomorphismEvaluation group representation →
  G → GR.V representation → GR.V representation
groupActionOnVectors evaluation g v =
  applyEnd evaluation (GR.action _ g) v

groupIdentityActsOnVectors :
  {G K : Set} →
  {group : GR.Group G} →
  {representation : GR.FiniteDimensionalRepresentation G K group} →
  (evaluation : EndomorphismEvaluation group representation) →
  (v : GR.V representation) →
  groupActionOnVectors evaluation (GR.Group.identity group) v ≡ v
groupIdentityActsOnVectors {representation = representation} evaluation v
  rewrite GR.actionIdentity representation = identityEvaluates evaluation v

groupCompositionActsOnVectors :
  {G K : Set} →
  {group : GR.Group G} →
  {representation : GR.FiniteDimensionalRepresentation G K group} →
  (evaluation : EndomorphismEvaluation group representation) →
  (g h : G) →
  (v : GR.V representation) →
  groupActionOnVectors evaluation (GR.Group._∙_ group g h) v
  ≡ groupActionOnVectors evaluation g (groupActionOnVectors evaluation h v)
groupCompositionActsOnVectors {representation = representation} evaluation g h v
  rewrite GR.actionComposition representation g h =
    compositionEvaluates evaluation
      (GR.action representation g)
      (GR.action representation h)
      v

------------------------------------------------------------------------
-- Full semantic weight-two bridge.
--
-- Starting from the full 196884 carrier is important: the actual weight-two
-- space contains the conformal vector plus the 196883 Monster constituent.
------------------------------------------------------------------------

record WeightTwoSemanticActionBridge
    {Monster K : Set}
    (bridge : MonsterVOA.MonsterGradedVOABridge Monster K) : Setω where
  field
    evaluation :
      EndomorphismEvaluation
        (GVOA.group (MonsterVOA.voaAction bridge))
        (GR.grade
          (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
          2)

    weightTwoCarrierIso :
      Stable.CarrierIso
        Nested.SemanticWeightTwo196884
        (GR.V
          (GR.grade
            (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
            2))

    conformalInRepresentation :
      GR.V
        (GR.grade
          (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
          2)

    semanticConformalMapsExactly :
      Stable.to weightTwoCarrierIso (inj₂ Nested.unit-at)
      ≡ conformalInRepresentation

    conformalFixedByMonsterAction :
      (g : Monster) →
      groupActionOnVectors evaluation g conformalInRepresentation
      ≡ conformalInRepresentation

open WeightTwoSemanticActionBridge public

semanticWeightTwoAction :
  {Monster K : Set} →
  {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  WeightTwoSemanticActionBridge bridge →
  Monster →
  Nested.SemanticWeightTwo196884 →
  Nested.SemanticWeightTwo196884
semanticWeightTwoAction actionBridge g state =
  Stable.from (weightTwoCarrierIso actionBridge)
    (groupActionOnVectors
      (evaluation actionBridge)
      g
      (Stable.to (weightTwoCarrierIso actionBridge) state))

semanticWeightTwoIdentityActs :
  {Monster K : Set} →
  {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  (actionBridge : WeightTwoSemanticActionBridge bridge) →
  (state : Nested.SemanticWeightTwo196884) →
  semanticWeightTwoAction actionBridge
    (GR.Group.identity (GVOA.group (MonsterVOA.voaAction bridge)))
    state
  ≡ state
semanticWeightTwoIdentityActs actionBridge state
  rewrite groupIdentityActsOnVectors
    (evaluation actionBridge)
    (Stable.to (weightTwoCarrierIso actionBridge) state)
  = Stable.fromTo (weightTwoCarrierIso actionBridge) state

semanticConformalUnitFixed :
  {Monster K : Set} →
  {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  (actionBridge : WeightTwoSemanticActionBridge bridge) →
  (g : Monster) →
  semanticWeightTwoAction actionBridge g (inj₂ Nested.unit-at)
  ≡ inj₂ Nested.unit-at
semanticConformalUnitFixed actionBridge g =
  trans
    (cong
      (Stable.from (weightTwoCarrierIso actionBridge))
      (trans
        (cong
          (groupActionOnVectors (evaluation actionBridge) g)
          (semanticConformalMapsExactly actionBridge))
        (conformalFixedByMonsterAction actionBridge g)))
    (trans
      (cong
        (Stable.from (weightTwoCarrierIso actionBridge))
        (sym (semanticConformalMapsExactly actionBridge)))
      (Stable.fromTo (weightTwoCarrierIso actionBridge) (inj₂ Nested.unit-at)))

------------------------------------------------------------------------
-- Constituent preservation is a separate payment.  Fixing the conformal point
-- does not by itself produce an explicit action on the semantic complement.
------------------------------------------------------------------------

record ConstituentPreservation
    {Monster K : Set}
    {bridge : MonsterVOA.MonsterGradedVOABridge Monster K}
    (actionBridge : WeightTwoSemanticActionBridge bridge) : Set₁ where
  field
    constituentAction :
      Monster →
      Nested.SemanticMonsterConstituent196883 →
      Nested.SemanticMonsterConstituent196883

    inclusionIntertwines :
      (g : Monster) →
      (state : Nested.SemanticMonsterConstituent196883) →
      semanticWeightTwoAction actionBridge g (inj₁ state)
      ≡ inj₁ (constituentAction g state)

open ConstituentPreservation public

------------------------------------------------------------------------
-- The representation-side route is now explicit and staged.
------------------------------------------------------------------------

data WeightTwoSemanticActionStage : Set where
  gradedEndomorphismOwned
  endomorphismEvaluationRequired
  fullWeightTwoCarrierBridgeRequired
  conformalLineCompatibilityRequired
  constituentPreservationRequired
  semanticCoordinateIntertwiningRequired
  : WeightTwoSemanticActionStage

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data AbstractEndAutomaticallyActsOnVectors : Set where
data CardinalityCreatesWeightTwoCarrierIso : Set where
data FixedConformalPointAutomaticallySplitsConstituent : Set where
data WeightTwoCarrierIsoCreatesMonsterAutomorphismTheorem : Set where

actionEndRequiresEvaluation : AbstractEndAutomaticallyActsOnVectors → ⊥
actionEndRequiresEvaluation ()

cardinalityDoesNotCreateWeightTwoIso : CardinalityCreatesWeightTwoCarrierIso → ⊥
cardinalityDoesNotCreateWeightTwoIso ()

fixedConformalDoesNotAloneSplitConstituent :
  FixedConformalPointAutomaticallySplitsConstituent → ⊥
fixedConformalDoesNotAloneSplitConstituent ()

weightTwoIsoDoesNotCreateMonsterAutomorphismTheorem :
  WeightTwoCarrierIsoCreatesMonsterAutomorphismTheorem → ⊥
weightTwoIsoDoesNotCreateMonsterAutomorphismTheorem ()

record MonsterWeightTwoSemanticActionBoundary : Set where
  constructor monster-weight-two-semantic-action-boundary
  field
    abstractGradeActionRecovered : Bool
    endEvaluationSeparated : Bool
    fullWeightTwoBridgePreferredToBareFinConstituent : Bool
    conformalUnitCompatibilityExplicit : Bool
    constituentPreservationSeparate : Bool
    semanticCoordinateIntertwiningStillSeparate : Bool
    cardinalityAloneCreatesBridge : Bool

canonicalMonsterWeightTwoSemanticActionBoundary :
  MonsterWeightTwoSemanticActionBoundary
canonicalMonsterWeightTwoSemanticActionBoundary =
  monster-weight-two-semantic-action-boundary
    true true true true true true false
