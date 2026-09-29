module DASHI.Reasoning.Trialectic369SemanticLinearConstituentRetractionCompilerExact where

------------------------------------------------------------------------
-- SEMANTIC 196883 <-> LINEAR 196883 WELD COMPILES THE RETRACTION
--
-- DASHI CONTRIBUTION
--
-- Existing owners already provide:
--
--   SemanticWeightTwo196884
--     = SemanticMonsterConstituent196883 ⊎ {conformal unit},
--
-- together with an exact carrier iso
--
--   SemanticWeightTwo196884 <-> abstract grade-two representation carrier.
--
-- The linear weight-two bridge separately provides:
--
--   constituentLinearCarrier
--   constituentInclusion : V_196883 -> V_2.
--
-- Therefore the missing retraction can be compiled from a much smaller
-- same-object weld:
--
--   linear constituent <-> semantic constituent
--
-- plus one square identifying linear inclusion with semantic inj₁ under the
-- existing full grade-two carrier charts.
--
-- The conformal semantic point is sent to linear zero.  This yields a total
-- projection V_2 -> V_196883 whose left-inverse law on the included constituent
-- is compiler output.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Nested
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as Semantic
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as Retraction

------------------------------------------------------------------------
-- 1. Same-object weld of the two 196883 carriers.
------------------------------------------------------------------------

record SemanticLinearConstituentWeld
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    linearToSemantic :
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))
      →
      Nested.SemanticMonsterConstituent196883

    semanticToLinear :
      Nested.SemanticMonsterConstituent196883
      →
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))

    semanticAfterLinear :
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      semanticToLinear (linearToSemantic state)
      ≡ state

    linearAfterSemantic :
      (state : Nested.SemanticMonsterConstituent196883) →
      linearToSemantic (semanticToLinear state)
      ≡ state

    -- The decisive same-object square.  Convert the linear inclusion to the
    -- abstract grade-two representation carrier, then back through the
    -- semantic weight-two carrier iso: this must be exactly inj₁ of the
    -- corresponding semantic constituent state.
    inclusionMatchesSemanticInjection :
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      Stable.from
        (Semantic.weightTwoCarrierIso
          (WeightTwo.semanticActionBridge
            (Core.weightTwoLinearBridge core)))
        (LinearRep.toRepresentationCarrier
          (WeightTwo.fullWeightTwoLinearRealisation
            (Core.weightTwoLinearBridge core))
          (WeightTwo.constituentInclusion
            (Core.weightTwoLinearBridge core)
            state))
      ≡ inj₁ (linearToSemantic state)

open SemanticLinearConstituentWeld public

------------------------------------------------------------------------
-- 2. Semantic projection: constituent branch survives, conformal branch -> 0.
------------------------------------------------------------------------

projectSemanticWeightTwo :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SemanticLinearConstituentWeld core →
  Nested.SemanticWeightTwo196884 →
  Linear.Vector
    (WeightTwo.constituentLinearCarrier
      (Core.weightTwoLinearBridge core))
projectSemanticWeightTwo core weld (inj₁ constituent) =
  semanticToLinear weld constituent
projectSemanticWeightTwo core weld (inj₂ Nested.unit-at) =
  Linear.zero
    (WeightTwo.constituentLinearCarrier
      (Core.weightTwoLinearBridge core))

------------------------------------------------------------------------
-- 3. Transport the projection to the actual full linear grade-two carrier.
------------------------------------------------------------------------

projectLinearWeightTwoToConstituent :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SemanticLinearConstituentWeld core →
  Linear.Vector
    (LinearRep.linearCarrier
      (WeightTwo.fullWeightTwoLinearRealisation
        (Core.weightTwoLinearBridge core)))
  →
  Linear.Vector
    (WeightTwo.constituentLinearCarrier
      (Core.weightTwoLinearBridge core))
projectLinearWeightTwoToConstituent core weld state =
  projectSemanticWeightTwo core weld
    (Stable.from
      (Semantic.weightTwoCarrierIso
        (WeightTwo.semanticActionBridge
          (Core.weightTwoLinearBridge core)))
      (LinearRep.toRepresentationCarrier
        (WeightTwo.fullWeightTwoLinearRealisation
          (Core.weightTwoLinearBridge core))
        state))

------------------------------------------------------------------------
-- 4. Left inverse is automatic from the weld square.
------------------------------------------------------------------------

projectionAfterInclusion :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (weld : SemanticLinearConstituentWeld core) →
  (state :
    Linear.Vector
      (WeightTwo.constituentLinearCarrier
        (Core.weightTwoLinearBridge core))) →
  projectLinearWeightTwoToConstituent core weld
    (WeightTwo.constituentInclusion
      (Core.weightTwoLinearBridge core)
      state)
  ≡ state
projectionAfterInclusion core weld state
  rewrite inclusionMatchesSemanticInjection weld state =
  semanticAfterLinear weld state

------------------------------------------------------------------------
-- 5. Compile the canonical constituent retraction.
------------------------------------------------------------------------

constituentRetractionFromSemanticWeld :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SemanticLinearConstituentWeld core →
  Retraction.ConstituentRetraction core
constituentRetractionFromSemanticWeld core weld =
  record
    { projectToConstituent =
        projectLinearWeightTwoToConstituent core weld
    ; leftInverse =
        projectionAfterInclusion core weld
    }

------------------------------------------------------------------------
-- 6. Falsification surface.
------------------------------------------------------------------------

record InclusionSemanticSquareCounterexample
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    (weld : SemanticLinearConstituentWeld core)
    : Setω where
  field
    state :
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))

    mismatch :
      Stable.from
        (Semantic.weightTwoCarrierIso
          (WeightTwo.semanticActionBridge
            (Core.weightTwoLinearBridge core)))
        (LinearRep.toRepresentationCarrier
          (WeightTwo.fullWeightTwoLinearRealisation
            (Core.weightTwoLinearBridge core))
          (WeightTwo.constituentInclusion
            (Core.weightTwoLinearBridge core)
            state))
      ≢ inj₁ (linearToSemantic weld state)

open InclusionSemanticSquareCounterexample public

------------------------------------------------------------------------
-- 7. Firewalls.
------------------------------------------------------------------------

data EqualCardinalityCreatesSemanticLinearWeld : Set where
data SemanticPointedSplitCreatesLinearWeld : Set where
data CoordinateIsoCreatesHilbertSameObjectWeld : Set where

cardinalityDoesNotCreateSemanticLinearWeld :
  EqualCardinalityCreatesSemanticLinearWeld → ⊥
cardinalityDoesNotCreateSemanticLinearWeld ()

semanticSplitDoesNotCreateLinearWeld :
  SemanticPointedSplitCreatesLinearWeld → ⊥
semanticSplitDoesNotCreateLinearWeld ()

coordinateIsoDoesNotCreateHilbertWeld :
  CoordinateIsoCreatesHilbertSameObjectWeld → ⊥
coordinateIsoDoesNotCreateHilbertWeld ()

------------------------------------------------------------------------
-- 8. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369SemanticLinearRetractionCompilerBoundary : Set where
  constructor trialectic-369-semantic-linear-retraction-compiler-boundary
  field
    semanticWeightTwoAlreadyPointed196883PlusOne : Bool
    fullGradeTwoSemanticCarrierIsoAlreadyOwned : Bool
    semanticLinearConstituentWeldIsOnlyNewSameObjectInput : Bool
    inclusionSemanticSquareSeparated : Bool
    conformalBranchProjectsToLinearZero : Bool
    leftInverseCompilerOwned : Bool
    constituentRetractionCompilerOwned : Bool
    semanticLinearWeldInhabitedHere : Bool
    inclusionSquareInhabitedHere : Bool
    actualRetractionInhabitedHere : Bool

canonicalTrialectic369SemanticLinearRetractionCompilerBoundary :
  Trialectic369SemanticLinearRetractionCompilerBoundary
canonicalTrialectic369SemanticLinearRetractionCompilerBoundary =
  trialectic-369-semantic-linear-retraction-compiler-boundary
    true true true true true true true
    false false false
