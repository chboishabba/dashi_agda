module DASHI.Combinatorics.TextileFibreHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List using (map)

import DASHI.Combinatorics.TextileNFibreCalculusExact as T
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.CoarseFineRelativeFibreExact as CoarseFine
import DASHI.Reasoning.TypedHyperfabricCore as Hyper

------------------------------------------------------------------------
-- SAME-OBJECT TEXTILE WELD
--
-- The textile carrier is viewed in two already-canonical repository languages:
--
--   (1) FibreRestrictionCore:
--       hidden construction history -> coarse textile surface + residual fibre;
--
--   (2) TypedHyperfabric:
--       local fibre/loop vertices -> crossing/stitch/interlacement edges with
--       explicit incidence, restriction, provenance, salience and traces.
--
-- This module does not introduce a competing generic fibre or hyperfabric core.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical fibre view of an n-fibre braid history.
------------------------------------------------------------------------

record TextileSurface : Set where
  constructor textileSurface
  field
    surfaceFibreCount : Nat
    surfaceHandedness : T.Handedness
    surfaceDepth : Nat

open TextileSurface public

textileSurfaceOf :
  {n : Nat} →
  T.BraidedFibreHistory n →
  TextileSurface
textileSurfaceOf {n} history =
  textileSurface n (T.handedness history) (T.provenanceDepth history)

record TextileFibreEvidence : Set where
  constructor textileFibreEvidence
  field
    observedCrossingDepth : Nat

open TextileFibreEvidence public

textileFibreCore : (n : Nat) → Fibre.FibreRestrictionCore
textileFibreCore n =
  Fibre.fibreRestrictionCore
    (T.BraidedFibreHistory n)
    TextileSurface
    TextileFibreEvidence
    textileSurfaceOf
    (λ surface → T.BraidWord n)
    (λ evidence surface → T.BraidWord n)
    true
    false

------------------------------------------------------------------------
-- Exact coarse + relative-fine reopening.
--
-- Coarse information retains n, handedness and provenance depth.  The relative
-- fine fibre is the actual braid word.  The pair reconstructs the literal
-- BraidedFibreHistory definitionally.
------------------------------------------------------------------------

textileCoarseFineReopening :
  (n : Nat) →
  CoarseFine.CoarseFineReopening (T.BraidedFibreHistory n)
textileCoarseFineReopening n =
  CoarseFine.coarseFineReopening
    TextileSurface
    (T.BraidWord n)
    textileSurfaceOf
    T.word
    (λ surface word →
      T.braidedFibreHistory
        word
        (surfaceHandedness surface)
        (surfaceDepth surface))
    (λ history → refl)

textileCoarseFineDeterminesHistory :
  {n : Nat} →
  {left right : T.BraidedFibreHistory n} →
  textileSurfaceOf left ≡ textileSurfaceOf right →
  T.word left ≡ T.word right →
  left ≡ right
textileCoarseFineDeterminesHistory {n} =
  CoarseFine.coarseAndRelativeFineDetermineState
    (textileCoarseFineReopening n)

------------------------------------------------------------------------
-- Textile hyperfabric vertices and hyperedges.
--
-- Vertices are persistent local carriers.  Edges are typed process relations.
-- Crossing edges retain the exact AdjacentCrossing n object, so an out-of-range
-- braid generator is unconstructible here for the same reason it is
-- unconstructible in TextileNFibreCalculusExact.
------------------------------------------------------------------------

data TextileVertex (n : Nat) : Set where
  fibreVertex : Nat → TextileVertex n
  retainedLoopVertex : Nat → TextileVertex n
  activeLoopVertex : TextileVertex n
  warpVertex : Nat → TextileVertex n
  weftVertex : Nat → TextileVertex n

data TextileEdge (n : Nat) : Set where
  braidCrossingEdge : T.AdjacentCrossing n → TextileEdge n
  weaveInterlaceEdge : Nat → Nat → T.CrossingOrientation → TextileEdge n
  knitDependencyEdge : Nat → Nat → TextileEdge n
  crochetPullThroughEdge : Nat → TextileEdge n

-- The stalk payload is deliberately minimal and structural: a local fibre/loop
-- address code.  Textile physics such as tension, elasticity, thickness and
-- material constitutive laws can refine this later without changing the
-- incidence architecture.

textileVertexStalk : {n : Nat} → TextileVertex n → Set
textileVertexStalk _ = Nat

textileEdgeStalk : {n : Nat} → TextileEdge n → Set
textileEdgeStalk _ = Nat

data TextileIncidence {n : Nat} : TextileVertex n → TextileEdge n → Set where
  leftCrossingIncidence :
    (crossing : T.AdjacentCrossing n) →
    TextileIncidence
      (fibreVertex (T.leftIndex crossing))
      (braidCrossingEdge crossing)

  rightCrossingIncidence :
    (crossing : T.AdjacentCrossing n) →
    TextileIncidence
      (fibreVertex (suc (T.leftIndex crossing)))
      (braidCrossingEdge crossing)

  warpInterlaceIncidence :
    (warp weft : Nat) (orientation : T.CrossingOrientation) →
    TextileIncidence
      (warpVertex warp)
      (weaveInterlaceEdge warp weft orientation)

  weftInterlaceIncidence :
    (warp weft : Nat) (orientation : T.CrossingOrientation) →
    TextileIncidence
      (weftVertex weft)
      (weaveInterlaceEdge warp weft orientation)

  retainedLoopDependencyIncidence :
    (old new : Nat) →
    TextileIncidence
      (retainedLoopVertex old)
      (knitDependencyEdge old new)

  activeLoopDependencyIncidence :
    (old new : Nat) →
    TextileIncidence
      activeLoopVertex
      (knitDependencyEdge old new)

  crochetActiveIncidence :
    (fabricLoop : Nat) →
    TextileIncidence
      activeLoopVertex
      (crochetPullThroughEdge fabricLoop)

  crochetFabricIncidence :
    (fabricLoop : Nat) →
    TextileIncidence
      (retainedLoopVertex fabricLoop)
      (crochetPullThroughEdge fabricLoop)

textileRestrict :
  {n : Nat} {vertex : TextileVertex n} {edge : TextileEdge n} →
  TextileIncidence vertex edge →
  textileVertexStalk vertex →
  textileEdgeStalk edge
textileRestrict _ localCode = localCode

textileEdgeProvenance : {n : Nat} → TextileEdge n → List String
textileEdgeProvenance (braidCrossingEdge crossing) =
  "TextileNFibreCalculusExact: indexed adjacent crossing" ∷ []
textileEdgeProvenance (weaveInterlaceEdge warp weft orientation) =
  "TextileNFibreCalculusExact: warp/weft interlacement" ∷ []
textileEdgeProvenance (knitDependencyEdge old new) =
  "TextileNFibreCalculusExact: retained-loop dependency" ∷ []
textileEdgeProvenance (crochetPullThroughEdge fabricLoop) =
  "TextileNFibreCalculusExact: active-loop pull-through dependency" ∷ []

textileEdgeSalience : {n : Nat} → TextileEdge n → Nat
textileEdgeSalience (braidCrossingEdge crossing) = 1
textileEdgeSalience (weaveInterlaceEdge warp weft orientation) = 1
textileEdgeSalience (knitDependencyEdge old new) = 2
textileEdgeSalience (crochetPullThroughEdge fabricLoop) = 2

textileHyperfabric :
  (n : Nat) →
  Hyper.TypedHyperfabric (TextileVertex n) (TextileEdge n)
textileHyperfabric n = record
  { vertexStalk = textileVertexStalk
  ; edgeStalk = textileEdgeStalk
  ; incidence = TextileIncidence
  ; restrict = textileRestrict
  ; edgeProvenance = textileEdgeProvenance
  ; edgeSalience = textileEdgeSalience
  ; fabricLabel = "DASHI n-fibre textile hyperfabric"
  }

------------------------------------------------------------------------
-- Every braid word lifts canonically to a real HyperfabricTrace over the same
-- indexed crossings.  This is not a parallel provenance list.
------------------------------------------------------------------------

crossingEdge : {n : Nat} → T.AdjacentCrossing n → TextileEdge n
crossingEdge = braidCrossingEdge

braidWordToHyperfabricTrace :
  {n : Nat} →
  T.BraidWord n →
  Hyper.HyperfabricTrace (TextileEdge n)
braidWordToHyperfabricTrace word = record
  { visitedEdges = map crossingEdge word
  ; traceReceipts =
      "braid word lifted edge-for-edge into canonical TypedHyperfabric trace" ∷ []
  ; traceLabel = "n-fibre braid hyperfabric trace"
  }

threeYangBaxterLeftTrace :
  Hyper.HyperfabricTrace (TextileEdge 3)
threeYangBaxterLeftTrace =
  braidWordToHyperfabricTrace T.threeFibreYangBaxterLeft

threeYangBaxterRightTrace :
  Hyper.HyperfabricTrace (TextileEdge 3)
threeYangBaxterRightTrace =
  braidWordToHyperfabricTrace T.threeFibreYangBaxterRight

fifteenFibreSweepTrace :
  Hyper.HyperfabricTrace (TextileEdge 15)
fifteenFibreSweepTrace =
  braidWordToHyperfabricTrace (T.braidSteps T.braid15)

------------------------------------------------------------------------
-- nMin survives on the actual hyperfabric edge carrier.
------------------------------------------------------------------------

textileHyperfabricNMin : Nat
textileHyperfabricNMin = T.nMinFibreTarget

textileHyperfabricNMinIs15 : textileHyperfabricNMin ≡ 15
textileHyperfabricNMinIs15 = refl

------------------------------------------------------------------------
-- Boundary: these are genuine instantiations of canonical repository cores,
-- but they do not claim material mechanics, continuum textile topology, or a
-- completed sheaf cohomology / braid-group representation theorem.
------------------------------------------------------------------------

record TextileFibreHyperfabricBoundary : Set where
  constructor textileFibreHyperfabricBoundary
  field
    textileIntroducesSecondGenericFibreCore : Bool
    textileIntroducesSecondGenericFibreCoreIsFalse :
      textileIntroducesSecondGenericFibreCore ≡ false

    textileIntroducesSecondGenericHyperfabricCore : Bool
    textileIntroducesSecondGenericHyperfabricCoreIsFalse :
      textileIntroducesSecondGenericHyperfabricCore ≡ false

    braidHistoryIsRelativeFineFibre : Bool
    braidHistoryIsRelativeFineFibreIsTrue :
      braidHistoryIsRelativeFineFibre ≡ true

    braidWordLiftsToCanonicalHyperfabricTrace : Bool
    braidWordLiftsToCanonicalHyperfabricTraceIsTrue :
      braidWordLiftsToCanonicalHyperfabricTrace ≡ true

    sameCoarseSurfaceImpliesSameBraidHistory : Bool
    sameCoarseSurfaceImpliesSameBraidHistoryIsFalse :
      sameCoarseSurfaceImpliesSameBraidHistory ≡ false

    hyperfabricIncidenceAloneProvesMaterialMechanics : Bool
    hyperfabricIncidenceAloneProvesMaterialMechanicsIsFalse :
      hyperfabricIncidenceAloneProvesMaterialMechanics ≡ false

open TextileFibreHyperfabricBoundary public

canonicalTextileFibreHyperfabricBoundary : TextileFibreHyperfabricBoundary
canonicalTextileFibreHyperfabricBoundary =
  textileFibreHyperfabricBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
