{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologySelectionExact as Selection
import DASHI.Quantum.QuantumMereologySchwingerObjectiveExact as Schwinger
import DASHI.Quantum.EntanglementGeometryMereologyBridgeExact as Geometry
import DASHI.Quantum.QuantumMereologySpacetimePromotionExact as Spacetime
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- QUANTUM MEREOLOGY MAX-CUT
--
-- The shortest honest chain in the current repository is:
--
--   source-shaped Schwinger search
--     -> supplied optimal selection receipt
--     -> the SAME selected TPS
--     -> supplied pair-relation geometry on that TPS
--     -> optional, separately supplied spacetime promotion.
--
-- The theorem-bearing contribution here is composition.  In particular:
-- * the selected candidate inherits the existing Schwinger minimizer theorem;
-- * downstream geometry remains indexed by that exact selected TPS;
-- * a criterion collision that changes a geometry-sensitive consumer blocks
--   descent/factorisation and forces every adequate refinement to separate the
--   witnessed pair;
-- * the geometry consumer itself is the canonical least-sufficient observer:
--   every observer adequate for that consumer must refine it;
-- * spacetime remains a separate promotion witness.
------------------------------------------------------------------------

record SelectedSchwingerSpatialPipeline
    {W : QM.BareQuantumWorld}
    (D : Schwinger.SchwingerSearchData W) : Set₁ where
  field
    selectionReceipt :
      Selection.PreferredTPSSelectionReceipt
        (Schwinger.selectionProblem D)

    state : QM.State W

    geometry :
      Geometry.FactorRelationGeometry
        W
        (Schwinger.realizes D
          (Selection.selected selectionReceipt))

open SelectedSchwingerSpatialPipeline public

selectedTPS :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W} →
  SelectedSchwingerSpatialPipeline D →
  QM.TensorProductStructure W
selectedTPS {D = D} P =
  Schwinger.realizes D
    (Selection.selected (selectionReceipt P))

selectedMinimizesSchwingerScore :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W} →
  (P : SelectedSchwingerSpatialPipeline D) →
  (other : Schwinger.Candidate D) →
  Schwinger.Admissible D other →
  Schwinger.ScoreNoWorse D
    (Schwinger.schwingerScore D
      (Selection.selected (selectionReceipt P)))
    (Schwinger.schwingerScore D other)
selectedMinimizesSchwingerScore {D = D} P =
  Schwinger.selectedMinimizesSchwingerScore
    D
    (selectionReceipt P)

selectedEmergentGeometry :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W} →
  (P : SelectedSchwingerSpatialPipeline D) →
  Geometry.Geometry (geometry P)
selectedEmergentGeometry P =
  Geometry.emergentGeometry
    (geometry P)
    (state P)

------------------------------------------------------------------------
-- GEOMETRY-SENSITIVE CONSUMER DESCENT
--
-- This is the operational form of the factorisation ambiguity: if a criterion
-- observer identifies two candidate TPSs that a declared geometry consumer
-- distinguishes, the criterion cannot be sufficient for that consumer.
------------------------------------------------------------------------

record GeometryCriterionConsumer
    {W : QM.BareQuantumWorld}
    (D : Schwinger.SchwingerSearchData W) : Set₁ where
  field
    Surface Outcome : Set

    observeCriterion :
      Schwinger.Candidate D → Surface

    geometryOutcome :
      Schwinger.Candidate D → Outcome

open GeometryCriterionConsumer public

asCriterionConsumerSurface :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W} →
  GeometryCriterionConsumer D →
  Selection.CriterionConsumerSurface
    (Schwinger.selectionProblem D)
asCriterionConsumerSurface G = record
  { Surface = Surface G
  ; Outcome = Outcome G
  ; observeCriterion = observeCriterion G
  ; consumer = geometryOutcome G
  }

GeometryCriterionCollision :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W} →
  GeometryCriterionConsumer D → Set
GeometryCriterionCollision G =
  Selection.CriterionCollision
    (asCriterionConsumerSurface G)

geometryCriterionCollisionBlocksSufficiency :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W}
    {G : GeometryCriterionConsumer D} →
  GeometryCriterionCollision G →
  Selection.CriterionConsumerSufficient
    (asCriterionConsumerSurface G) →
  ⊥
geometryCriterionCollisionBlocksSufficiency =
  Selection.criterionCollisionBlocksConsumerSufficiency

geometryCriterionCollisionBlocksFactorization :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W}
    {G : GeometryCriterionConsumer D} →
  GeometryCriterionCollision G →
  Descent.FactorsThrough
    (observeCriterion G)
    (geometryOutcome G) →
  ⊥
geometryCriterionCollisionBlocksFactorization =
  Selection.criterionCollisionBlocksFactorization

geometryCriterionCollisionForcesSeparationInEveryRepair :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W}
    {G : GeometryCriterionConsumer D}
    {Refinement : Set}
    {refine : Schwinger.Candidate D → Refinement} →
  (collision : GeometryCriterionCollision G) →
  Repair.RefinementRepairs
    (observeCriterion G)
    refine
    (geometryOutcome G) →
  refine
      (Descent.left
        (Selection.witness collision))
    ≡
  refine
      (Descent.right
        (Selection.witness collision)) →
  ⊥
geometryCriterionCollisionForcesSeparationInEveryRepair =
  Selection.criterionCollisionForcesSeparationInEveryRepair

------------------------------------------------------------------------
-- LEAST-SUFFICIENT GEOMETRY OBSERVER
--
-- Productive cross-pollination from the repository's generic observer lattice:
-- the geometry consumer itself is the canonical least-informative observer that
-- is sufficient for that declared geometry outcome.  Hence any criterion,
-- boundary encoding, compressed representation or holographic observation that
-- claims adequacy for this geometry consumer must refine the consumer outcome.
-- This is consumer-relative and makes no claim that one geometry outcome is a
-- complete observer of the quantum world.
------------------------------------------------------------------------

geometryConsumerObserverIsLeast :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W} →
  (G : GeometryCriterionConsumer D) →
  Descent.LeastSufficientConsumerObserver
    (geometryOutcome G)
geometryConsumerObserverIsLeast G =
  Descent.canonicalConsumerObserverIsLeast
    (geometryOutcome G)

everyGeometryAdequateObserverRefinesGeometryOutcome :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W}
    {G : GeometryCriterionConsumer D}
    {BoundarySurface : Set} →
  (observeBoundary : Schwinger.Candidate D → BoundarySurface) →
  Descent.ConsumerSufficient
    observeBoundary
    (geometryOutcome G) →
  Observer.Refines
    (geometryOutcome G)
    observeBoundary
everyGeometryAdequateObserverRefinesGeometryOutcome {G = G}
    observeBoundary sufficient =
  Descent.belowEverySufficient
    (geometryConsumerObserverIsLeast G)
    observeBoundary
    sufficient

------------------------------------------------------------------------
-- SPACETIME REMAINS A SEPARATE PROMOTION
------------------------------------------------------------------------

record SelectedSchwingerSpacetimePipeline
    {W : QM.BareQuantumWorld}
    {D : Schwinger.SchwingerSearchData W}
    (P : SelectedSchwingerSpatialPipeline D) : Set₁ where
  field
    promotion :
      Spacetime.QuantumMereologySpacetimePromotion
        W
        (selectedTPS P)
        (geometry P)

open SelectedSchwingerSpacetimePipeline public

selectedSpacetimeSameSpatialCarrier :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W}
    {P : SelectedSchwingerSpatialPipeline D} →
  (S : SelectedSchwingerSpacetimePipeline P) →
  Spacetime.SameSpatialCarrier (promotion S)
selectedSpacetimeSameSpatialCarrier S =
  Spacetime.sameSpatialCarrier (promotion S)

selectedSpacetimeGluingPaid :
  ∀ {W}
    {D : Schwinger.SchwingerSearchData W}
    {P : SelectedSchwingerSpatialPipeline D} →
  (S : SelectedSchwingerSpacetimePipeline P) →
  Spacetime.SpacetimeGluingPaid (promotion S)
selectedSpacetimeGluingPaid S =
  Spacetime.spacetimeGluingPaid (promotion S)

------------------------------------------------------------------------
-- FAIL-CLOSED TERMINAL BOUNDARY
------------------------------------------------------------------------

record QuantumMereologyMaxCutBoundary : Set where
  field
    sourceWrittenProducerCreatesSelection : Bool
    sourceWrittenProducerCreatesSelectionIsFalse :
      sourceWrittenProducerCreatesSelection ≡ false

    selectedTPSCreatesGeometryWithoutPairRelation : Bool
    selectedTPSCreatesGeometryWithoutPairRelationIsFalse :
      selectedTPSCreatesGeometryWithoutPairRelation ≡ false

    spatialGeometryCreatesSpacetime : Bool
    spatialGeometryCreatesSpacetimeIsFalse :
      spatialGeometryCreatesSpacetime ≡ false

    geometryCriterionCollisionCreatesRefinementObligation : Bool
    geometryCriterionCollisionCreatesRefinementObligationIsTrue :
      geometryCriterionCollisionCreatesRefinementObligation ≡ true

    geometryConsumerObserverIsLeastSufficient : Bool
    geometryConsumerObserverIsLeastSufficientIsTrue :
      geometryConsumerObserverIsLeastSufficient ≡ true

    holographicBoundaryAdequacyIsConsumerRelative : Bool
    holographicBoundaryAdequacyIsConsumerRelativeIsTrue :
      holographicBoundaryAdequacyIsConsumerRelative ≡ true

open QuantumMereologyMaxCutBoundary public

canonicalQuantumMereologyMaxCutBoundary :
  QuantumMereologyMaxCutBoundary
canonicalQuantumMereologyMaxCutBoundary = record
  { sourceWrittenProducerCreatesSelection = false
  ; sourceWrittenProducerCreatesSelectionIsFalse = refl
  ; selectedTPSCreatesGeometryWithoutPairRelation = false
  ; selectedTPSCreatesGeometryWithoutPairRelationIsFalse = refl
  ; spatialGeometryCreatesSpacetime = false
  ; spatialGeometryCreatesSpacetimeIsFalse = refl
  ; geometryCriterionCollisionCreatesRefinementObligation = true
  ; geometryCriterionCollisionCreatesRefinementObligationIsTrue = refl
  ; geometryConsumerObserverIsLeastSufficient = true
  ; geometryConsumerObserverIsLeastSufficientIsTrue = refl
  ; holographicBoundaryAdequacyIsConsumerRelative = true
  ; holographicBoundaryAdequacyIsConsumerRelativeIsTrue = refl
  }

dashiQuantumMereologyMaxCutReceipt : Sources.AttributionReceipt
dashiQuantumMereologyMaxCutReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI"
    "Composes the existing Carroll--Singh-shaped Schwinger selection, exact selected-TPS indexing, factor-relation geometry, consumer-descent/refinement no-go, canonical least-sufficient geometry observer, and separately witnessed spacetime promotion. Any criterion or boundary observer adequate for the declared geometry consumer must refine that consumer outcome. It creates no minimizer, CPO eigenprojector, pair-relation geometry, holographic dictionary, spacetime gluing, Einstein dynamics, or empirical authority."
