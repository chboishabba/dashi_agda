module DASHI.Reasoning.TernarySynthesisCellComplexExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Give the repository's 27-cell synthesis carrier its literal finite cellular
-- reading. A local 1-cell is a directed comparison a -> b. A local 2-cell is
-- a synthesis triple (a,b,s) whose triangular boundary is
--
--   a -> b,  b -> s,  s -> a.
--
-- Therefore a total synthesis rule fills every ordered comparison while
-- retaining the original comparison edge as part of the boundary. No
-- averaging, deletion or contradiction erasure is required.
--
-- The PNF realization interface below is deliberately proof-carrying: mapping
-- this local cell complex into PNFHodgeResidualTopology requires explicit
-- vertex/edge/two-cell maps plus endpoint and triangle-boundary laws.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)

import Base369 as Base
import DASHI.Interop.PNFHodgeResidualTopology as Hodge
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis

record LocalOneCell : Set where
  constructor localOneCell
  field
    source target : Base.TriTruth

open LocalOneCell public

comparisonOneCell : Synthesis.Comparison9 → LocalOneCell
comparisonOneCell (left , right) = localOneCell left right

record LocalTriangleBoundary : Set where
  constructor localTriangleBoundary
  field
    edge01 edge12 edge20 : LocalOneCell

open LocalTriangleBoundary public

record LocalSynthesisTwoCell : Set where
  constructor localSynthesisTwoCell
  field
    vertex0 vertex1 synthesisVertex : Base.TriTruth
    triangleBoundary : LocalTriangleBoundary
    boundaryIsCanonical :
      triangleBoundary
      ≡ localTriangleBoundary
          (localOneCell vertex0 vertex1)
          (localOneCell vertex1 synthesisVertex)
          (localOneCell synthesisVertex vertex0)

open LocalSynthesisTwoCell public

choiceToTwoCell :
  Synthesis.SynthesisChoice27 → LocalSynthesisTwoCell
choiceToTwoCell (left , (right , synthesis)) =
  localSynthesisTwoCell
    left
    right
    synthesis
    (localTriangleBoundary
      (localOneCell left right)
      (localOneCell right synthesis)
      (localOneCell synthesis left))
    refl

twoCellToChoice :
  LocalSynthesisTwoCell → Synthesis.SynthesisChoice27
twoCellToChoice cell =
  Synthesis.makeSynthesisChoice
    (vertex0 cell)
    (vertex1 cell)
    (synthesisVertex cell)

twoCellChoiceRoundTrip :
  (choice : Synthesis.SynthesisChoice27) →
  twoCellToChoice (choiceToTwoCell choice) ≡ choice
twoCellChoiceRoundTrip (left , (right , synthesis)) = refl

choiceTwoCellRoundTrip :
  (cell : LocalSynthesisTwoCell) →
  choiceToTwoCell (twoCellToChoice cell) ≡ cell
choiceTwoCellRoundTrip
  (localSynthesisTwoCell left right synthesis boundary refl) = refl

originalComparisonEdge :
  LocalSynthesisTwoCell → LocalOneCell
originalComparisonEdge cell = edge01 (triangleBoundary cell)

originalComparisonRetained :
  (choice : Synthesis.SynthesisChoice27) →
  originalComparisonEdge (choiceToTwoCell choice)
  ≡ comparisonOneCell (Synthesis.comparisonOfSynthesis choice)
originalComparisonRetained (left , (right , synthesis)) = refl

------------------------------------------------------------------------
-- Every comparison gets a local 2-cell when a total synthesis rule is given.
------------------------------------------------------------------------

fillComparison :
  Synthesis.TotalSynthesisRule →
  Synthesis.Comparison9 →
  LocalSynthesisTwoCell
fillComparison rule comparison =
  choiceToTwoCell (Synthesis.applySynthesisRule rule comparison)

filledBoundaryRetainsComparison :
  (rule : Synthesis.TotalSynthesisRule) →
  (comparison : Synthesis.Comparison9) →
  originalComparisonEdge (fillComparison rule comparison)
  ≡ comparisonOneCell comparison
filledBoundaryRetainsComparison rule (left , right) = refl

------------------------------------------------------------------------
-- Explicit realization obligations into the existing PNF Hodge topology.
------------------------------------------------------------------------

record PNFCellularRealization : Set₁ where
  field
    realizeVertex : Base.TriTruth → Hodge.PNFZeroCellRef
    realizeEdge : LocalOneCell → Hodge.PNFOneCell
    realizeTwoCell : LocalSynthesisTwoCell → Hodge.PNFTwoCell

    edgeSourcePreserved :
      (edge : LocalOneCell) →
      Hodge.oneCellSource (realizeEdge edge)
      ≡ realizeVertex (source edge)

    edgeTargetPreserved :
      (edge : LocalOneCell) →
      Hodge.oneCellTarget (realizeEdge edge)
      ≡ realizeVertex (target edge)

    triangleEdge01Preserved :
      (cell : LocalSynthesisTwoCell) →
      Hodge.edge01
        (Hodge.triangleBoundary (realizeTwoCell cell))
      ≡ Hodge.oneCellRef
          (realizeEdge (edge01 (triangleBoundary cell)))

    triangleEdge12Preserved :
      (cell : LocalSynthesisTwoCell) →
      Hodge.edge12
        (Hodge.triangleBoundary (realizeTwoCell cell))
      ≡ Hodge.oneCellRef
          (realizeEdge (edge12 (triangleBoundary cell)))

    triangleEdge20Preserved :
      (cell : LocalSynthesisTwoCell) →
      Hodge.edge20
        (Hodge.triangleBoundary (realizeTwoCell cell))
      ≡ Hodge.oneCellRef
          (realizeEdge (edge20 (triangleBoundary cell)))

record TernarySynthesisCellBoundary : Set where
  field
    localTwoCellConstructed : Bool
    localTwoCellConstructedIsTrue :
      localTwoCellConstructed ≡ true

    everyComparisonFillableUnderTotalRule : Bool
    everyComparisonFillableUnderTotalRuleIsTrue :
      everyComparisonFillableUnderTotalRule ≡ true

    originalTensionEdgeErasedByFilling : Bool
    originalTensionEdgeErasedByFillingIsFalse :
      originalTensionEdgeErasedByFilling ≡ false

    arbitraryPNFRealizationManufacturedWithoutWitness : Bool
    arbitraryPNFRealizationManufacturedWithoutWitnessIsFalse :
      arbitraryPNFRealizationManufacturedWithoutWitness ≡ false

canonicalTernarySynthesisCellBoundary : TernarySynthesisCellBoundary
canonicalTernarySynthesisCellBoundary =
  record
    { localTwoCellConstructed = true
    ; localTwoCellConstructedIsTrue = refl
    ; everyComparisonFillableUnderTotalRule = true
    ; everyComparisonFillableUnderTotalRuleIsTrue = refl
    ; originalTensionEdgeErasedByFilling = false
    ; originalTensionEdgeErasedByFillingIsFalse = refl
    ; arbitraryPNFRealizationManufacturedWithoutWitness = false
    ; arbitraryPNFRealizationManufacturedWithoutWitnessIsFalse = refl
    }
