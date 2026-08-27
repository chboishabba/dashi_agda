module DASHI.Reasoning.RelationalLensSynthesisCore where

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", 2nd ed.,
-- Graduate Texts in Mathematics 5, Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- Iulia Duta, Giulia Cassara, Fabrizio Silvestri and Pietro Lio,
-- "Sheaf Hypergraph Networks", arXiv:2309.17116.
-- DOI: 10.48550/arXiv.2309.17116.
--
-- The category/sheaf references motivate only the span, local-view and
-- restriction vocabulary. The concrete ternary comparison and synthesis
-- carriers below are DASHI constructions and reuse existing repository types.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Sigma using (_,_)

import Base369 as Base
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.CounterpositionOrderedJoinExact as Counter
import DASHI.Foundations.RepresentationChartInvariant as Representation
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Latent object and family of projections.
------------------------------------------------------------------------

record LensFamily (Latent Lens View : Set) : Set₁ where
  constructor lensFamily
  field
    project : Lens → Latent → View

open LensFamily public

record TernaryLensFamily (Latent Lens View : Set) : Set₁ where
  constructor ternaryLensFamily
  field
    family : LensFamily Latent Lens View
    quantize : View → Base.TriTruth

open TernaryLensFamily public

observeThrough :
  ∀ {Latent Lens View} →
  TernaryLensFamily Latent Lens View →
  Lens → Latent → Base.TriTruth
observeThrough ternaryFamily lens latent =
  quantize ternaryFamily
    (project (family ternaryFamily) lens latent)

compareLenses :
  ∀ {Latent Lens View} →
  TernaryLensFamily Latent Lens View →
  Lens → Lens → Latent →
  Synthesis.Comparison9
compareLenses ternaryFamily leftLens rightLens latent =
  observeThrough ternaryFamily leftLens latent ,
  observeThrough ternaryFamily rightLens latent

------------------------------------------------------------------------
-- Total synthesis over two projections of one latent object.
------------------------------------------------------------------------

record LensSynthesisSystem (Latent Lens View : Set) : Set₁ where
  constructor lensSynthesisSystem
  field
    ternaryFamily : TernaryLensFamily Latent Lens View
    synthesisRule : Synthesis.TotalSynthesisRule

open LensSynthesisSystem public

synthesizeLenses :
  ∀ {Latent Lens View} →
  LensSynthesisSystem Latent Lens View →
  Lens → Lens → Latent →
  Synthesis.SynthesisChoice27
synthesizeLenses system leftLens rightLens latent =
  Synthesis.applySynthesisRule
    (synthesisRule system)
    (compareLenses (ternaryFamily system) leftLens rightLens latent)

lensSynthesisRetainsComparison :
  ∀ {Latent Lens View}
    (system : LensSynthesisSystem Latent Lens View)
    (leftLens rightLens : Lens)
    (latent : Latent) →
  Synthesis.comparisonOfSynthesis
    (synthesizeLenses system leftLens rightLens latent)
  ≡ compareLenses
      (ternaryFamily system)
      leftLens rightLens latent
lensSynthesisRetainsComparison system leftLens rightLens latent =
  Synthesis.everyComparisonReceivesSynthesis
    (synthesisRule system)
    (compareLenses (ternaryFamily system) leftLens rightLens latent)

------------------------------------------------------------------------
-- A chart/lens inverse exists only when a real two-sided transport has been
-- supplied. Merely comparing two projections does not manufacture one.
------------------------------------------------------------------------

record InvertibleLensTransition
    {Latent Lens View : Set}
    (family : LensFamily Latent Lens View)
    (leftLens rightLens : Lens) : Set₁ where
  constructor invertibleLensTransition
  field
    forward : View → View
    backward : View → View
    forwardProjects :
      (latent : Latent) →
      forward (project family leftLens latent)
      ≡ project family rightLens latent
    backwardProjects :
      (latent : Latent) →
      backward (project family rightLens latent)
      ≡ project family leftLens latent
    backwardForward :
      (view : View) → backward (forward view) ≡ view
    forwardBackward :
      (view : View) → forward (backward view) ≡ view

------------------------------------------------------------------------
-- Operator roles remain separated. In particular a counter-view,
-- orientation reversal, algebraic inverse, logical negation and lens
-- transition are not definitionally identified.
--
-- Cross-pollination from CounterpositionOrderedJoinExact is deliberate:
-- contextual counterposition may invert only one coordinate or merely reindex
-- coordinates.  Therefore "take the opposing position" cannot silently mean
-- "apply the global inverse" at the lens layer.
------------------------------------------------------------------------

data RelationalOperatorRole : Set where
  logicalNegationRole : RelationalOperatorRole
  algebraicInverseRole : RelationalOperatorRole
  orientationReversalRole : RelationalOperatorRole
  contextualCounterpositionRole : RelationalOperatorRole
  lensTransitionRole : RelationalOperatorRole

orientationReversalIsNotLogicalNegation :
  orientationReversalRole ≡ logicalNegationRole → ⊥
orientationReversalIsNotLogicalNegation ()

orientationReversalIsNotAlgebraicInverse :
  orientationReversalRole ≡ algebraicInverseRole → ⊥
orientationReversalIsNotAlgebraicInverse ()

contextualCounterpositionIsNotAlgebraicInverseByRole :
  contextualCounterpositionRole ≡ algebraicInverseRole → ⊥
contextualCounterpositionIsNotAlgebraicInverseByRole ()

contextualCounterpositionIsNotLogicalNegationByRole :
  contextualCounterpositionRole ≡ logicalNegationRole → ⊥
contextualCounterpositionIsNotLogicalNegationByRole ()

lensTransitionIsNotAlgebraicInverseByRole :
  lensTransitionRole ≡ algebraicInverseRole → ⊥
lensTransitionIsNotAlgebraicInverseByRole ()

logicalNegationIsNotLensTransitionByRole :
  logicalNegationRole ≡ lensTransitionRole → ⊥
logicalNegationIsNotLensTransitionByRole ()

foundationCounterpositionWitnessSeparatesFromInverse :
  Counter.counterUnder Counter.rejectThird BT.allPositive
  ≡ Counter.counterUnder Counter.invertAll BT.allPositive
  → ⊥
foundationCounterpositionWitnessSeparatesFromInverse =
  Counter.partialCounterpositionIsNotFullInverse

------------------------------------------------------------------------
-- The existing FramedAtlas is a special lossless lens family: transitions
-- hit their requested chart while preserving evaluation.
------------------------------------------------------------------------

atlasProjection :
  ∀ {Value Rep Chart}
    (atlas : Representation.FramedAtlas Value Rep Chart) →
  Chart → Rep → Value
atlasProjection atlas target representation =
  Representation.FramedAtlas.evaluate atlas target
    (Representation.FramedAtlas.transition atlas target representation)

atlasProjectionPreservesInvariant :
  ∀ {Value Rep Chart}
    (atlas : Representation.FramedAtlas Value Rep Chart) →
    (target : Chart) →
    (representation : Rep) →
  atlasProjection atlas target representation
  ≡
  Representation.FramedAtlas.evaluate atlas
    (Representation.FramedAtlas.activeChart atlas representation)
    representation
atlasProjectionPreservesInvariant atlas target representation =
  Representation.FramedAtlas.transitionPreservesEvaluation
    atlas target representation

------------------------------------------------------------------------
-- The existing typed hyperfabric is the higher-arity substrate. This alias
-- does not identify every hyperfabric edge with a reversible lens transition.
------------------------------------------------------------------------

HyperfabricLensSubstrate : Set → Set → Set₁
HyperfabricLensSubstrate Vertex Edge =
  Hyperfabric.TypedHyperfabric Vertex Edge

record RelationalLensSynthesisBoundary : Set where
  field
    latentObjectSeparatedFromLens : Bool
    latentObjectSeparatedFromLensIsTrue :
      latentObjectSeparatedFromLens ≡ true

    synthesisRetainsDirectedComparison : Bool
    synthesisRetainsDirectedComparisonIsTrue :
      synthesisRetainsDirectedComparison ≡ true

    lensTransitionRequiresExplicitTransport : Bool
    lensTransitionRequiresExplicitTransportIsTrue :
      lensTransitionRequiresExplicitTransport ≡ true

    reversalNegationInverseCollapsed : Bool
    reversalNegationInverseCollapsedIsFalse :
      reversalNegationInverseCollapsed ≡ false

    contextualCounterpositionCollapsedIntoInverse : Bool
    contextualCounterpositionCollapsedIntoInverseIsFalse :
      contextualCounterpositionCollapsedIntoInverse ≡ false

    everyGenericLensDeclaredLossless : Bool
    everyGenericLensDeclaredLosslessIsFalse :
      everyGenericLensDeclaredLossless ≡ false

canonicalRelationalLensSynthesisBoundary :
  RelationalLensSynthesisBoundary
canonicalRelationalLensSynthesisBoundary =
  record
    { latentObjectSeparatedFromLens = true
    ; latentObjectSeparatedFromLensIsTrue = refl
    ; synthesisRetainsDirectedComparison = true
    ; synthesisRetainsDirectedComparisonIsTrue = refl
    ; lensTransitionRequiresExplicitTransport = true
    ; lensTransitionRequiresExplicitTransportIsTrue = refl
    ; reversalNegationInverseCollapsed = false
    ; reversalNegationInverseCollapsedIsFalse = refl
    ; contextualCounterpositionCollapsedIntoInverse = false
    ; contextualCounterpositionCollapsedIntoInverseIsFalse = refl
    ; everyGenericLensDeclaredLossless = false
    ; everyGenericLensDeclaredLosslessIsFalse = refl
    }
