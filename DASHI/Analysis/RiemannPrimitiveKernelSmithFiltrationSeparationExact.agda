module DASHI.Analysis.RiemannPrimitiveKernelSmithFiltrationSeparationExact where

------------------------------------------------------------------------
-- RH PRIMITIVE KERNEL: SMITH INVARIANT VS 3-ADIC FILTRATION
--
-- Capstone for the current arithmetic cross-pollination.
--
-- 1. The row is primitive / Smith-style invariant one.
-- 2. The displayed 3-adic depth tuple (0,5,5,5) is NOT invariant under
--    arbitrary unimodular column basis changes.
-- 3. The correct basis-transported replacement is the zero fibre/kernel of a
--    depth-five reduced functional.
--
-- The concrete ZMod 243 instantiation is currently Lean-native.  Agda owns
-- the determinant-one coordinate equivalence, the changed depth tuple, and
-- the generic exact kernel-transport theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_)

import DASHI.Analysis.RiemannPrimitiveKernelBalancedTernaryStencilExact as Stencil
import DASHI.Analysis.RiemannPrimitiveKernelUnimodularBasisExact as Basis
import DASHI.Analysis.RiemannPrimitiveKernelFiltrationTransportExact as Filtration
import DASHI.Analysis.RiemannPrimitiveKernelExplicitSmithReductionExact as Smith

primitiveSmithStyleReceipt :
  Basis.SmithInvariantOneReceipt
primitiveSmithStyleReceipt =
  Basis.canonicalSmithInvariantOneReceipt

originalThreeAdicProfile :
  Basis.FourDepthProfile
originalThreeAdicProfile =
  Basis.originalDepthProfile

unimodularlyTransformedThreeAdicProfile :
  Basis.FourDepthProfile
unimodularlyTransformedThreeAdicProfile =
  Basis.transformedDepthProfile

rawDepthProfileChangesUnderBasis :
  Basis.secondDepth unimodularlyTransformedThreeAdicProfile
  ≡ Basis.secondDepth originalThreeAdicProfile ->
  ⊥
rawDepthProfileChangesUnderBasis =
  Basis.depthProfileChangesUnderUnimodularBasis

genericKernelTransportAvailable :
  {Old New Value : Set}
  {zeroValue : Value}
  {equiv : Filtration.TwoSidedCoordinateEquivalence Old New}
  (transport : Filtration.FunctionalKernelTransport zeroValue equiv)
  (y : New) ->
  Filtration.KernelCorrespondence transport y
genericKernelTransportAvailable =
  Filtration.canonicalKernelCorrespondence

explicitSmithNormalFormOwned :
  Smith.smithReduce Smith.originalRow
  ≡ Smith.row4 (+ 1) (+ 0) (+ 0) (+ 0)
explicitSmithNormalFormOwned =
  Smith.explicitSmithNormalForm

rowMapSurjectiveWitness :
  (value : ℤ) ->
  Smith.rowMap (Smith.rowPreimage value) ≡ value
rowMapSurjectiveWitness =
  Smith.rowMapHasPreimage

record SmithFiltrationSeparationBoundary : Set where
  constructor smith-filtration-separation-boundary
  field
    primitiveSmithInvariantOneOwned : Bool
    originalDepthProfileZeroFiveFiveFiveOwned : Bool
    explicitDeterminantOneBasisChangeOwned : Bool
    transformedDepthProfileZeroOneFiveFiveOwned : Bool
    rawDepthTupleBasisInvariant : Bool
    genericKernelTransportOwned : Bool
    explicitSmithOneZeroZeroZeroOwned : Bool
    rowMapSurjectivityOwned : Bool
    concreteMod243KernelTransportOwnedInAgda : Bool
    concreteMod243KernelTransportOwnedInLean : Bool
    filteredKernelIsPreferredInvariantObject : Bool

canonicalSmithFiltrationSeparationBoundary :
  SmithFiltrationSeparationBoundary
canonicalSmithFiltrationSeparationBoundary =
  smith-filtration-separation-boundary
    true true true true false true true true false true true
