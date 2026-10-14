module DASHI.Biology.IITCausalPantsOrientationBoundaryExact where

------------------------------------------------------------------------
-- ORIENTATION FIREWALL FOR CAUSAL PANTS
--
-- The existing topological owner supplies a canonical finite 1 -> 3 pants
-- junction.  IITCausalPantsFibreGluingExact supplies a causal 2 -> 1 local
-- synthesis cell (A,B) -> C.  They share trivalent/pants geometry, but the
-- causal reverse orientation is not obtained for free.
--
-- A future equivalence may provide an explicit reversal/duality/transport
-- witness.  Until then, branch and synthesis orientations remain distinct.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITCausalPantsFibreGluingExact as Causal
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Cobordism

existingBranchingOutputCountIsThree :
  Cobordism.outputCount Cobordism.composedOneToThree ≡ 3
existingBranchingOutputCountIsThree = Pants.canonicalPantsHasThreeOutputs

record CausalPantsOrientationBoundary : Set where
  constructor causal-pants-orientation-boundary
  field
    existingCanonicalPantsIsOneToThreeBranching : Bool
    causalLocalCellIsTwoToOneSynthesis : Bool
    bothAreTrivalentInterfaces : Bool
    oneToThreeOwnerSuppliesCausalReverseByDefinition : Bool
    reversalNeedsExplicitWitness : Bool

open CausalPantsOrientationBoundary public

canonicalCausalPantsOrientationBoundary : CausalPantsOrientationBoundary
canonicalCausalPantsOrientationBoundary =
  causal-pants-orientation-boundary
    true true true false true

branchingDoesNotManufactureSynthesisOrientation :
  oneToThreeOwnerSuppliesCausalReverseByDefinition
    canonicalCausalPantsOrientationBoundary ≡ false
branchingDoesNotManufactureSynthesisOrientation = refl

causalCellStillOwnsTwoInputs :
  Causal.localCellHasTwoInputsOneOutput
    Causal.canonicalIITCausalPantsFibreBoundary ≡ true
causalCellStillOwnsTwoInputs = refl
