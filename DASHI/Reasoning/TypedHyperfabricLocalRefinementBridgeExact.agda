module DASHI.Reasoning.TypedHyperfabricLocalRefinementBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Topology.TetrationalGateField as Gate
import DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact as SectionReduction

------------------------------------------------------------------------
-- TYPED HYPERFABRIC LOCAL REFINEMENT BRIDGE
--
-- This is an adapter, not a second hyperfabric kernel.  It records that two
-- already-compatible GlobalSections are related by one declared local
-- refinement request at a selected vertex.  The gate transition is pinned to
-- refineWithinChart, which keeps chart refinement distinct from fibre-
-- dimension increase and tower recursion.
--
-- No generic decidable inequality on Vertex is assumed, so this witness does
-- not claim that every other stalk is definitionally unchanged.  Domains that
-- need an exclusive one-stalk update must supply that stronger property
-- separately.
------------------------------------------------------------------------

record LocalStalkRefinement
    {Vertex Edge : Set}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    (before after : Hyperfabric.GlobalSection fabric) : Set₁ where
  constructor local-stalk-refinement
  field
    refinedVertex : Vertex
    beforeLocalValue : Hyperfabric.vertexStalk fabric refinedVertex
    afterLocalValue : Hyperfabric.vertexStalk fabric refinedVertex
    beforeValueMatchesSection :
      beforeLocalValue ≡ Hyperfabric.vertexValue before refinedVertex
    afterValueMatchesSection :
      afterLocalValue ≡ Hyperfabric.vertexValue after refinedVertex
    requestedTransition : Gate.TransitionKind
    requestedTransitionIsRefineWithinChart :
      requestedTransition ≡ Gate.refineWithinChart
    refinementReceipt : String

open LocalStalkRefinement public

localRefinementDoesNotOpenTower :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {before after : Hyperfabric.GlobalSection fabric} →
  (refinement : LocalStalkRefinement before after) →
  requestedTransition refinement ≡ Gate.openTowerLevel → ⊥
localRefinementDoesNotOpenTower refinement equality
  with requestedTransitionIsRefineWithinChart refinement | equality
... | refl | ()

localRefinementDoesNotIncreaseFibreDimension :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {before after : Hyperfabric.GlobalSection fabric} →
  (refinement : LocalStalkRefinement before after) →
  requestedTransition refinement ≡ Gate.increaseFibreDimension → ⊥
localRefinementDoesNotIncreaseFibreDimension refinement equality
  with requestedTransitionIsRefineWithinChart refinement | equality
... | refl | ()

------------------------------------------------------------------------
-- Finite specimen reusing the existing section/reduction fixture.
------------------------------------------------------------------------

finiteHiddenStalkRefinement :
  LocalStalkRefinement SectionReduction.leftSection SectionReduction.rightSection
finiteHiddenStalkRefinement = local-stalk-refinement
  SectionReduction.region
  (false , false)
  (false , true)
  refl
  refl
  Gate.refineWithinChart
  refl
  "refine the hidden coordinate while preserving compatibility with the visible edge value"

finiteRefinementTransitionIsWithinChart :
  requestedTransition finiteHiddenStalkRefinement ≡ Gate.refineWithinChart
finiteRefinementTransitionIsWithinChart = refl

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data LocalRefinementProvesExclusiveSingleStalkMutation : Set where

localRefinementDoesNotProveExclusiveSingleStalkMutation :
  LocalRefinementProvesExclusiveSingleStalkMutation → ⊥
localRefinementDoesNotProveExclusiveSingleStalkMutation ()

record TypedHyperfabricLocalRefinementBoundary : Set where
  constructor typed-hyperfabric-local-refinement-boundary
  field
    typedHyperfabricCoreRemainsCanonicalKernel : Bool
    beforeAndAfterAreCompatibleGlobalSections : Bool
    refinementActsOnDeclaredVertexStalkValues : Bool
    requestedTransitionPinnedToRefineWithinChart : Bool
    refinementImpliesIncreaseFibreDimension : Bool
    refinementImpliesIncreaseFibreDimensionIsFalse :
      refinementImpliesIncreaseFibreDimension ≡ false
    refinementImpliesOpenTowerLevel : Bool
    refinementImpliesOpenTowerLevelIsFalse :
      refinementImpliesOpenTowerLevel ≡ false
    refinementProvesEveryOtherStalkUnchanged : Bool
    refinementProvesEveryOtherStalkUnchangedIsFalse :
      refinementProvesEveryOtherStalkUnchanged ≡ false
    refinementCreatesParallelHyperfabricKernel : Bool
    refinementCreatesParallelHyperfabricKernelIsFalse :
      refinementCreatesParallelHyperfabricKernel ≡ false
    boundaryNote : String

open TypedHyperfabricLocalRefinementBoundary public

canonicalTypedHyperfabricLocalRefinementBoundary :
  TypedHyperfabricLocalRefinementBoundary
canonicalTypedHyperfabricLocalRefinementBoundary =
  typed-hyperfabric-local-refinement-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    "Local refinement is a relation between already-compatible GlobalSections at one declared vertex and is pinned to refineWithinChart. It neither opens a tower nor increases fibre dimension, and it does not manufacture an exclusivity theorem for untouched stalks."
