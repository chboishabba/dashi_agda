{-# OPTIONS --safe #-}
module DASHI.Reasoning.TrialecticWeightedGraphFaceMediationSelectedExact where

------------------------------------------------------------------------
-- SELECTED FINITE MEDIATION FIXTURE ABOVE A WEIGHTED DIRECTED GRAPH.
--
-- This *does not* derive a face from an edge matrix.  It constructs a
-- declared three-case chart of an independently provided attached face,
-- and reuses canonical Grothendieck T18-boundary descent and
-- SecondOrderCellGluing / carry.  It is a concrete consumer of those
-- existing theorem owners, NOT a universal trialectic law or empirical
-- sociological/psychological synthesis.
--
-- Proof ownership: DASHI.  Retains source-typed argument/face distinction.
-- The selected chart is synthetic and should never be labelled source-
-- justified face mediation, a smooth pants cobordism or a physical theory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact as Graph
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as Groth
import DASHI.Reasoning.TrialecticThreeCellCarryDepthExact as Carry
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- The face-to-output policy is declared, not deduced from any weighted arc.
------------------------------------------------------------------------

selectedOutput : Face.TriadicFaceRelation -> Cell.TrialecticBasis3Cell
selectedOutput Face.reciprocalFace = Geometry.positiveCorner
selectedOutput Face.coerciveFace = Geometry.negativeCorner
selectedOutput Face.underdeterminedFace = Geometry.origin

selectedFaceMediationLaw : Groth.FaceMediationLaw
selectedFaceMediationLaw _ face output = output ≡ selectedOutput face

-- The descended T18 boundary is explicitly chosen from the *existing*
-- compatible T9 local sections.  It is not reconstructed from arbitrary
-- three-node weighted matrix values.
selectedSection :
  (state : Graph.GraphWithAttachedFace) ->
  Groth.GrothendieckFaceMediatedSection selectedFaceMediationLaw
selectedSection state =
  Groth.grothendieck-face-mediated-section
    (Groth.structuredLocals Cell.canonicalCompatibleThreeCellBoundary)
    (Groth.structuredCompatibility Cell.canonicalCompatibleThreeCellBoundary)
    (Graph.attachedFace state)
    (selectedOutput (Graph.attachedFace state))
    refl

selectedSectionRetainsAttachedFace :
  (state : Graph.GraphWithAttachedFace) ->
  Groth.face (selectedSection state) ≡ Graph.attachedFace state
selectedSectionRetainsAttachedFace state = refl

selectedSectionRetainsCanonicalBoundary :
  (state : Graph.GraphWithAttachedFace) ->
  Groth.mediatedDescendedBoundary (selectedSection state)
  ≡ Cell.canonicalCompatibleThreeCellBoundary
selectedSectionRetainsCanonicalBoundary state =
  Groth.structuredGlueRoundTrip Cell.canonicalCompatibleThreeCellBoundary

------------------------------------------------------------------------
-- Native next-depth carry from the existing canonical mediator interface.
------------------------------------------------------------------------

selectedGraphCarry :
  (depth : Nat) ->
  (state : Graph.GraphWithAttachedFace) ->
  Carry.TrialecticCellCarryStep
    depth
    (Groth.mediatedStructuredState (selectedSection state))
    (Groth.toSecondOrderCellGluing (selectedSection state))
selectedGraphCarry depth state =
  Carry.promoteGrothendieckMediated depth (selectedSection state)

selectedCarryOutputDependsOnFace :
  (depth : Nat) ->
  (state : Graph.GraphWithAttachedFace) ->
  Carry.nextDepthCell (selectedGraphCarry depth state)
  ≡ selectedOutput (Graph.attachedFace state)
selectedCarryOutputDependsOnFace depth state = refl

selectedCarryRetainsSourceState :
  (depth : Nat) ->
  (state : Graph.GraphWithAttachedFace) ->
  Carry.retainedSource (selectedGraphCarry depth state)
  ≡ Groth.mediatedStructuredState (selectedSection state)
selectedCarryRetainsSourceState depth state = refl

------------------------------------------------------------------------
-- Same complete 3x3 weighted matrix, different selected next-depth cell.
-- The *selected output*, not merely the face label, cannot factor through
-- the weighted graph projection.  No inference from graph to face is made.
------------------------------------------------------------------------

selectedOutputConsumer :
  Graph.GraphWithAttachedFace -> Cell.TrialecticBasis3Cell
selectedOutputConsumer state = selectedOutput (Graph.attachedFace state)

selectedInputsSameGraph :
  Graph.graphObserver Graph.sameMatrixReciprocal
  ≡ Graph.graphObserver Graph.sameMatrixCoercive
selectedInputsSameGraph = Graph.sameMatrixDifferentFace

selectedCornersDifferent :
  Geometry.positiveCorner ≡ Geometry.negativeCorner -> ⊥
selectedCornersDifferent equality with cong Geometry.x equality
... | ()

selectedOutputsDifferent :
  selectedOutputConsumer Graph.sameMatrixReciprocal
  ≡ selectedOutputConsumer Graph.sameMatrixCoercive -> ⊥
selectedOutputsDifferent = selectedCornersDifferent

outputNonDescentWitness :
  Descent.ConsumerNonDescentWitness
    Graph.graphObserver selectedOutputConsumer
outputNonDescentWitness =
  Descent.consumerNonDescentWitness
    Graph.sameMatrixReciprocal
    Graph.sameMatrixCoercive
    selectedInputsSameGraph
    selectedOutputsDifferent

selectedNextDepthOutputCannotFactorThroughGraph :
  Descent.FactorsThrough
    Graph.graphObserver selectedOutputConsumer -> ⊥
selectedNextDepthOutputCannotFactorThroughGraph =
  Descent.nonDescentWitnessBlocksFactorization outputNonDescentWitness

------------------------------------------------------------------------
-- Exact status: concrete *selected* policy inhabited, universal semantic
-- or source-justified mediation not promoted.
------------------------------------------------------------------------

record SelectedMediationBoundary : Set where
  constructor selected-mediation-boundary
  field
    separateFaceInputRequired : Bool
    compatibleT18BoundaryReused : Bool
    concreteSelectedLawAndNextCellConstructed : Bool
    selectedOutputFactorsThroughWeightedGraph : Bool
    genericSocialOrPhysicalFaceLawEstablished : Bool
    smoothPantsOrTQFTEstablished : Bool
    kernelVerificationPerformedHere : Bool

canonicalSelectedMediationBoundary : SelectedMediationBoundary
canonicalSelectedMediationBoundary =
  selected-mediation-boundary true true true false false false false
