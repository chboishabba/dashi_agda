module DASHI.Combinatorics.TextileFibreOrderHyperfabricExact where

open import DASHI.Core.Prelude

import DASHI.Combinatorics.TextileNFibreCalculusExact as T
import DASHI.Combinatorics.TextileFibreHyperfabricExact as Textile
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.FibreOrderNonfactorabilityExact as Order
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Reasoning.TypedHyperfabricCore as Hyper

------------------------------------------------------------------------
-- ACTUAL CANONICAL FIBRE-ORDER INSTANTIATION
--
-- This file does not re-prove the generic order theorem.  It supplies textile
-- carrier operators on the exact FibreRestrictionCore constructed in
-- TextileFibreHyperfabricExact, then invokes the repository's canonical
-- FibreOrderNonfactorabilityExact theorem.
------------------------------------------------------------------------

replaceBraidWord :
  {n : Nat} →
  T.BraidWord n →
  T.BraidedFibreHistory n →
  T.BraidedFibreHistory n
replaceBraidWord replacement history =
  T.braidedFibreHistory
    replacement
    (T.handedness history)
    (T.provenanceDepth history)

replaceBraidWordPreservesSurface :
  {n : Nat} →
  (replacement : T.BraidWord n) →
  Dynamics.SurfaceInvariant
    (Textile.textileFibreCore n)
    (replaceBraidWord replacement)
replaceBraidWordPreservesSurface replacement history = refl

replaceBraidWordEndomorphism :
  {n : Nat} →
  T.BraidWord n →
  Dynamics.FibreEndomorphism (Textile.textileFibreCore n)
replaceBraidWordEndomorphism replacement =
  Dynamics.fibreEndomorphism
    (replaceBraidWord replacement)
    (replaceBraidWordPreservesSurface replacement)

------------------------------------------------------------------------
-- Concrete 3-fibre noncommutation.
--
-- Two overwrite transports preserve the SAME coarse textile surface.  Their
-- ordered composites differ because the later transport determines the retained
-- relative-fine braid word.  This is intentionally a small exact witness used
-- to instantiate the generic theorem; it is not claimed to be a physical
-- braiding procedure by itself.
------------------------------------------------------------------------

leftRewriteOperator :
  T.BraidedFibreHistory 3 →
  T.BraidedFibreHistory 3
leftRewriteOperator = replaceBraidWord T.threeFibreYangBaxterLeft

rightRewriteOperator :
  T.BraidedFibreHistory 3 →
  T.BraidedFibreHistory 3
rightRewriteOperator = replaceBraidWord T.threeFibreYangBaxterRight

leftRewriteSurfaceInvariant :
  Dynamics.SurfaceInvariant
    (Textile.textileFibreCore 3)
    leftRewriteOperator
leftRewriteSurfaceInvariant =
  replaceBraidWordPreservesSurface T.threeFibreYangBaxterLeft

rightRewriteSurfaceInvariant :
  Dynamics.SurfaceInvariant
    (Textile.textileFibreCore 3)
    rightRewriteOperator
rightRewriteSurfaceInvariant =
  replaceBraidWordPreservesSurface T.threeFibreYangBaxterRight

firstCrossingCode : T.BraidWord 3 → Nat
firstCrossingCode [] = 0
firstCrossingCode (crossing ∷ rest) = suc (T.leftIndex crossing)

leftFirstCrossingCode :
  firstCrossingCode T.threeFibreYangBaxterLeft ≡ 1
leftFirstCrossingCode = refl

rightFirstCrossingCode :
  firstCrossingCode T.threeFibreYangBaxterRight ≡ 2
rightFirstCrossingCode = refl

oneNotTwo : 1 ≡ 2 → ⊥
oneNotTwo ()

threeYangBaxterWordsDifferent :
  T.threeFibreYangBaxterLeft ≡ T.threeFibreYangBaxterRight → ⊥
threeYangBaxterWordsDifferent same =
  oneNotTwo (cong firstCrossingCode same)

canonicalSeed : T.BraidedFibreHistory 3
canonicalSeed = T.threeLeftHistory

orderedRewriteEndpointsDifferent :
  leftRewriteOperator (rightRewriteOperator canonicalSeed)
  ≡
  rightRewriteOperator (leftRewriteOperator canonicalSeed) → ⊥
orderedRewriteEndpointsDifferent same =
  threeYangBaxterWordsDifferent (cong T.word same)

------------------------------------------------------------------------
-- Direct reuse of the canonical repository theorem.
------------------------------------------------------------------------

textileOrderNonfactorability :
  NF.NonFactorabilityWitness
    (Order.orderedSurface
      leftRewriteOperator rightRewriteOperator canonicalSeed)
    (Order.orderedEndpoint
      leftRewriteOperator rightRewriteOperator canonicalSeed)
textileOrderNonfactorability =
  Order.orderEndpointNonfactorability
    leftRewriteSurfaceInvariant
    rightRewriteSurfaceInvariant
    canonicalSeed
    orderedRewriteEndpointsDifferent

textileSurfaceCannotDecodeOrderedBraidEndpoint :
  NF.FactorsThrough
    (Order.orderedSurface
      leftRewriteOperator rightRewriteOperator canonicalSeed)
    (Order.orderedEndpoint
      leftRewriteOperator rightRewriteOperator canonicalSeed)
  → ⊥
textileSurfaceCannotDecodeOrderedBraidEndpoint =
  Order.surfaceCannotDecodeOrderedEndpoint
    leftRewriteSurfaceInvariant
    rightRewriteSurfaceInvariant
    canonicalSeed
    orderedRewriteEndpointsDifferent

------------------------------------------------------------------------
-- Hyperfabric companion traces use the same two literal words as the
-- fibre-order witness.  Thus the quotient theorem and the edge-trace geometry
-- do not silently switch textile objects.
------------------------------------------------------------------------

leftOrderedHyperfabricTrace :
  Hyper.HyperfabricTrace (Textile.TextileEdge 3)
leftOrderedHyperfabricTrace =
  Textile.braidWordToHyperfabricTrace T.threeFibreYangBaxterLeft

rightOrderedHyperfabricTrace :
  Hyper.HyperfabricTrace (Textile.TextileEdge 3)
rightOrderedHyperfabricTrace =
  Textile.braidWordToHyperfabricTrace T.threeFibreYangBaxterRight

record TextileOrderHyperformWeld : Set where
  constructor textileOrderHyperformWeld
  field
    fibreCoreIsCanonical : Bool
    fibreCoreIsCanonicalIsTrue : fibreCoreIsCanonical ≡ true

    hyperfabricIsCanonical : Bool
    hyperfabricIsCanonicalIsTrue : hyperfabricIsCanonical ≡ true

    sameLiteralLeftWordFeedsBothViews : Bool
    sameLiteralLeftWordFeedsBothViewsIsTrue :
      sameLiteralLeftWordFeedsBothViews ≡ true

    sameLiteralRightWordFeedsBothViews : Bool
    sameLiteralRightWordFeedsBothViewsIsTrue :
      sameLiteralRightWordFeedsBothViews ≡ true

    coarseSurfaceDeterminesTransportOrder : Bool
    coarseSurfaceDeterminesTransportOrderIsFalse :
      coarseSurfaceDeterminesTransportOrder ≡ false

open TextileOrderHyperformWeld public

canonicalTextileOrderHyperformWeld : TextileOrderHyperformWeld
canonicalTextileOrderHyperformWeld =
  textileOrderHyperformWeld
    true refl
    true refl
    true refl
    true refl
    false refl
