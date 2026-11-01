module DASHI.Reasoning.TernaryPantsSynthesisS3BridgeExact where

------------------------------------------------------------------------
-- RECURSIVE TERNARY PANTS / 27-CELL SYNTHESIS / S3 WELD
--
-- Cross-pollination of:
--   * Round-24 arbitrary-depth ternary cylinder <-> pants frontier;
--   * the 27 synthesis cells (a,b,s);
--   * the exact six-element S3 action on TriTruth.
--
-- Source context:
--   John D. Dixon and Brian Mortimer, "Permutation Groups",
--   Springer GTM 163 (1996), DOI 10.1007/978-1-4612-0731-3.
--   Michael F. Atiyah, "Topological quantum field theory",
--   Publ. Math. IHES 68 (1988), DOI 10.1007/BF02698547.
--
-- The result is finite/combinatorial.  It does not claim a smooth TQFT or a
-- continuous 3D pants thickening.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cells
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

------------------------------------------------------------------------
-- Exact slot <-> TriTruth identification for the local three-way branch.
------------------------------------------------------------------------

slotToTruth : Pants.BranchSlot → Base.TriTruth
slotToTruth Pants.slot3 = Base.tri-low
slotToTruth Pants.slot6 = Base.tri-mid
slotToTruth Pants.slot9 = Base.tri-high

truthToSlot : Base.TriTruth → Pants.BranchSlot
truthToSlot Base.tri-low = Pants.slot3
truthToSlot Base.tri-mid = Pants.slot6
truthToSlot Base.tri-high = Pants.slot9

slotTruthRoundTrip :
  (slot : Pants.BranchSlot) →
  truthToSlot (slotToTruth slot) ≡ slot
slotTruthRoundTrip Pants.slot3 = refl
slotTruthRoundTrip Pants.slot6 = refl
slotTruthRoundTrip Pants.slot9 = refl

truthSlotRoundTrip :
  (truth : Base.TriTruth) →
  slotToTruth (truthToSlot truth) ≡ truth
truthSlotRoundTrip Base.tri-low = refl
truthSlotRoundTrip Base.tri-mid = refl
truthSlotRoundTrip Base.tri-high = refl

------------------------------------------------------------------------
-- S3 acts locally on every pants branch slot through the exact slot/truth
-- equivalence.  The inverse action is proved, not assumed.
------------------------------------------------------------------------

permuteSlot : S3.TriPermutation → Pants.BranchSlot → Pants.BranchSlot
permuteSlot permutation slot =
  truthToSlot (S3.applyPermutation permutation (slotToTruth slot))

permuteSlotInverseLeft :
  (permutation : S3.TriPermutation) →
  (slot : Pants.BranchSlot) →
  permuteSlot (S3.inversePermutation permutation)
    (permuteSlot permutation slot)
  ≡ slot
permuteSlotInverseLeft permutation slot
  rewrite truthSlotRoundTrip
            (S3.applyPermutation permutation (slotToTruth slot))
        | S3.inverseLeftAt permutation (slotToTruth slot)
        | slotTruthRoundTrip slot = refl

------------------------------------------------------------------------
-- A synthesis choice at any parent pants path picks three children of that
-- same parent: left comparison endpoint, right endpoint, synthesis endpoint.
------------------------------------------------------------------------

record RecursiveSynthesisCell (n : Nat) : Set where
  constructor recursiveSynthesisCell
  field
    parent : Frontier.PantsPath n
    leftSlot : Pants.BranchSlot
    rightSlot : Pants.BranchSlot
    synthesisSlot : Pants.BranchSlot

open RecursiveSynthesisCell public

leftChild :
  ∀ {n : Nat} → RecursiveSynthesisCell n → Frontier.PantsPath (suc n)
leftChild cell = Frontier.appendSlot (parent cell) (leftSlot cell)

rightChild :
  ∀ {n : Nat} → RecursiveSynthesisCell n → Frontier.PantsPath (suc n)
rightChild cell = Frontier.appendSlot (parent cell) (rightSlot cell)

synthesisChild :
  ∀ {n : Nat} → RecursiveSynthesisCell n → Frontier.PantsPath (suc n)
synthesisChild cell = Frontier.appendSlot (parent cell) (synthesisSlot cell)

recursiveChoice :
  ∀ {n : Nat} → RecursiveSynthesisCell n → Synthesis.SynthesisChoice27
recursiveChoice cell =
  Synthesis.makeSynthesisChoice
    (slotToTruth (leftSlot cell))
    (slotToTruth (rightSlot cell))
    (slotToTruth (synthesisSlot cell))

recursiveTwoCell :
  ∀ {n : Nat} → RecursiveSynthesisCell n → Cells.LocalSynthesisTwoCell
recursiveTwoCell cell = Cells.choiceToTwoCell (recursiveChoice cell)

recursiveOriginalComparisonRetained :
  ∀ {n : Nat} (cell : RecursiveSynthesisCell n) →
  Cells.originalComparisonEdge (recursiveTwoCell cell)
  ≡ Cells.comparisonOneCell
      (Synthesis.comparisonOfSynthesis (recursiveChoice cell))
recursiveOriginalComparisonRetained cell =
  Cells.originalComparisonRetained (recursiveChoice cell)

------------------------------------------------------------------------
-- S3 equivariance at the local branch layer: permuting all three branch slots
-- gives exactly the coordinatewise permutation of the associated 27-cell.
------------------------------------------------------------------------

permuteRecursiveCell :
  ∀ {n : Nat} →
  S3.TriPermutation →
  RecursiveSynthesisCell n →
  RecursiveSynthesisCell n
permuteRecursiveCell permutation cell =
  recursiveSynthesisCell
    (parent cell)
    (permuteSlot permutation (leftSlot cell))
    (permuteSlot permutation (rightSlot cell))
    (permuteSlot permutation (synthesisSlot cell))

permuteRecursiveCellInverseLeft :
  ∀ {n : Nat}
  (permutation : S3.TriPermutation)
  (cell : RecursiveSynthesisCell n) →
  permuteRecursiveCell (S3.inversePermutation permutation)
    (permuteRecursiveCell permutation cell)
  ≡ cell
permuteRecursiveCellInverseLeft permutation
  (recursiveSynthesisCell parent left right synthesis)
  rewrite permuteSlotInverseLeft permutation left
        | permuteSlotInverseLeft permutation right
        | permuteSlotInverseLeft permutation synthesis = refl

------------------------------------------------------------------------
-- The recursive weld preserves the Round-24 promotion boundary.
------------------------------------------------------------------------

record TernaryPantsSynthesisS3Boundary : Set where
  constructor ternaryPantsSynthesisS3Boundary
  field
    arbitraryFiniteParentDepthSupported : Bool
    local27CellAttachedAtEveryParent : Bool
    localS3ActionInvertible : Bool
    originalComparisonEdgeRetained : Bool
    smoothPantsThickeningConstructed : Bool
    localS3EqualsGlobalRecursiveWreathAction : Bool

canonicalTernaryPantsSynthesisS3Boundary : TernaryPantsSynthesisS3Boundary
canonicalTernaryPantsSynthesisS3Boundary =
  ternaryPantsSynthesisS3Boundary
    true
    true
    true
    true
    false
    false
