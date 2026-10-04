module DASHI.Reasoning.TrialecticThreeCellCarryDepthExact where

------------------------------------------------------------------------
-- STRUCTURED TRIALECTIC FACE MEDIATION -> NEXT-DEPTH 27-CELL
--
-- This module is deliberately conditional.
--
-- TrialecticThreeCellHyperformSynthesisExact establishes that:
--
--   * A/B/C are finite T^3 / 27-state basis cells;
--   * every pairwise dialectic may itself be a T^9 three-cell hyperform;
--   * three such edge dialectics can be cyclically compatible;
--   * their compatible boundary still does not determine the triadic face.
--
-- If an explicit SecondOrderCellGluing witness is supplied, its output is a
-- full 27-state basis cell.  We may then retain the entire depth-d trialectic
-- as history while exposing that output at depth d+1.
--
-- This is the typed shape suggested by the existing carry vocabulary:
--
--   lower structured state retained
--             +
--   one next-depth synthesis cell
--
-- It does NOT derive a concrete face-mediation law, stochastic dynamics,
-- psychological development law, or certified higher-stack/hypersheaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; suc)

import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as GrothCell
import DASHI.Reasoning.CarryMemorySubvoxelReceipt as Carry
import DASHI.Cognition.RecursiveFibreTower as Tower

------------------------------------------------------------------------
-- 1. One retained promotion step.
------------------------------------------------------------------------

record TrialecticCellCarryStep
    (depth : Nat)
    (state : Cell.StructuredTrialecticState)
    (gluing : Cell.SecondOrderCellGluing state) : Set₁ where
  constructor trialectic-cell-carry-step
  field
    sourceDepth : Nat
    sourceDepthIsDeclared : sourceDepth ≡ depth

    retainedSource : Cell.StructuredTrialecticState
    retainedSourceExact : retainedSource ≡ state

    promotedDepth : Nat
    promotedDepthIsSuccessor : promotedDepth ≡ suc depth

    nextDepthCell : Cell.TrialecticBasis3Cell
    nextDepthCellIsMediated :
      nextDepthCell ≡ Cell.outputCell gluing

open TrialecticCellCarryStep public

promoteWithFaceGluing :
  (depth : Nat) →
  (state : Cell.StructuredTrialecticState) →
  (gluing : Cell.SecondOrderCellGluing state) →
  TrialecticCellCarryStep depth state gluing
promoteWithFaceGluing depth state gluing =
  trialectic-cell-carry-step
    depth
    refl
    state
    refl
    (suc depth)
    refl
    (Cell.outputCell gluing)
    refl

promotionRetainsWholeStructuredSource :
  (depth : Nat) →
  (state : Cell.StructuredTrialecticState) →
  (gluing : Cell.SecondOrderCellGluing state) →
  retainedSource (promoteWithFaceGluing depth state gluing)
  ≡ state
promotionRetainsWholeStructuredSource depth state gluing = refl

promotionAdvancesExactlyOneDepth :
  (depth : Nat) →
  (state : Cell.StructuredTrialecticState) →
  (gluing : Cell.SecondOrderCellGluing state) →
  promotedDepth (promoteWithFaceGluing depth state gluing)
  ≡ suc depth
promotionAdvancesExactlyOneDepth depth state gluing = refl

promotionOutputIsFullBasisCell :
  (depth : Nat) →
  (state : Cell.StructuredTrialecticState) →
  (gluing : Cell.SecondOrderCellGluing state) →
  nextDepthCell (promoteWithFaceGluing depth state gluing)
  ≡ Cell.outputCell gluing
promotionOutputIsFullBasisCell depth state gluing = refl


------------------------------------------------------------------------
-- 1b. Grothendieck-mediated promotion.
--
-- Once the three local T^9 edge sections have descended to the T^18 global
-- boundary and a separate face-mediation receipt has selected the next T^3
-- cell, the existing one-step carry package applies directly.
------------------------------------------------------------------------

promoteGrothendieckMediated :
  {law : GrothCell.FaceMediationLaw} →
  (depth : Nat) →
  (section : GrothCell.GrothendieckFaceMediatedSection law) →
  TrialecticCellCarryStep
    depth
    (GrothCell.mediatedStructuredState section)
    (GrothCell.toSecondOrderCellGluing section)
promoteGrothendieckMediated depth section =
  promoteWithFaceGluing
    depth
    (GrothCell.mediatedStructuredState section)
    (GrothCell.toSecondOrderCellGluing section)

grothendieckPromotionRetainsDescendedState :
  {law : GrothCell.FaceMediationLaw} →
  (depth : Nat) →
  (section : GrothCell.GrothendieckFaceMediatedSection law) →
  retainedSource
    (promoteGrothendieckMediated depth section)
  ≡ GrothCell.mediatedStructuredState section
grothendieckPromotionRetainsDescendedState depth section = refl

grothendieckPromotionOutputIsMediatedCell :
  {law : GrothCell.FaceMediationLaw} →
  (depth : Nat) →
  (section : GrothCell.GrothendieckFaceMediatedSection law) →
  nextDepthCell
    (promoteGrothendieckMediated depth section)
  ≡ GrothCell.nextDepthCell section
grothendieckPromotionOutputIsMediatedCell depth section = refl

------------------------------------------------------------------------
-- 2. Existing carry owner is provenance/shape donor only.
------------------------------------------------------------------------

existingCarryBoundary :
  Carry.DepthEvaluationBoundary
existingCarryBoundary =
  Carry.depthEvaluationBoundary Carry.canonicalCarryMemorySubvoxelReceipt

existingCarryReadsJAndJPlusOneTogether :
  existingCarryBoundary ≡ Carry.evaluateJAndJPlusOneTogether
existingCarryReadsJAndJPlusOneTogether =
  Carry.depthEvaluationBoundaryIsJAndJPlusOne
    Carry.canonicalCarryMemorySubvoxelReceipt

existingCarryRetainsLowerResidue :
  Carry.subvoxelMemory Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.lowerResiduePersistsAsMemory
existingCarryRetainsLowerResidue =
  Carry.subvoxelMemoryPersists Carry.canonicalCarryMemorySubvoxelReceipt

------------------------------------------------------------------------
-- 3. Existing generic inverse-limit vocabulary remains available.
--
-- We do not claim the conditional trialectic promotion above already defines
-- an infinite coherent tower.  A full tower needs a gluing witness at every
-- depth plus coherence of the chosen promotions.
------------------------------------------------------------------------

existingRecursiveFibreTower :
  Tower.FibreTower
existingRecursiveFibreTower =
  Tower.recursivePhaseTower

data OneCarryStepDefinesWholeInverseLimit : Set where

oneCarryStepDoesNotDefineWholeInverseLimit :
  OneCarryStepDefinesWholeInverseLimit →
  ⊥
oneCarryStepDoesNotDefineWholeInverseLimit ()

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record TrialecticThreeCellCarryDepthBoundary : Set where
  constructor trialectic-three-cell-carry-depth-boundary
  field
    faceMediationMayExposeNextDepthCell : Bool
    promotedObjectIsTwentySevenStateCell : Bool
    lowerStructuredTrialecticRetained : Bool
    promotionAdvancesOneDeclaredDepth : Bool
    existingCarryShapeReused : Bool
    oneConditionalStepDefinesInfiniteTower : Bool
    concreteFaceMediationDerivedAutomatically : Bool
    certifiedHypersheafDerivedAutomatically : Bool

canonicalTrialecticThreeCellCarryDepthBoundary :
  TrialecticThreeCellCarryDepthBoundary
canonicalTrialecticThreeCellCarryDepthBoundary =
  trialectic-three-cell-carry-depth-boundary
    true
    true
    true
    true
    true
    false
    false
    false
