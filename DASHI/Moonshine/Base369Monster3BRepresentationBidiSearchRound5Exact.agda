module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound5Exact where

------------------------------------------------------------------------
-- ROUND 5 BIDI SEARCH: THE REPO-NATIVE VOA ACTION IS THE RECOVERY SURFACE
--
-- Round 4 asked for a literal State/Normalizer action plus recognition on its
-- literal zeta eigenspace.  VertexOperatorAlgebraCore already supplies the
-- correct kind of literal State/action surface: a Moonshine-facing VOA bridge
-- with Monster action on the graded-module Carrier.
--
-- Base369Monster3BVOAActionPhaseAdapterBidiExact compiles selected order-three
-- and normalizer receipts on that SAME carrier into CentralNormalizerAction.
-- The exact Q(zeta_3) phase chart is already owned.  Hence we no longer search
-- for a fresh Monster state carrier or a new phase algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound4Exact as R4
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as VOAAdapter

------------------------------------------------------------------------
-- 1. Search coordinates after exposing the VOA action owner.
------------------------------------------------------------------------

data Round5Leaf : Set where
  repoNativeVOAActionSurface : Round5Leaf
  selectedThreeBCentralElementReceipts : Round5Leaf
  cyclotomicScalarEmbeddingOnSameVOA : Round5Leaf
  normalizerPreserveInvertReceipts : Round5Leaf
  recognitionOnLiteralVOAZetaEigenspace : Round5Leaf
  separatePhaseResolvedConstruction : Round5Leaf
  separateCyclotomicPhaseAlgebra : Round5Leaf
  actualFin90InertiaAction : Round5Leaf
  sameActionTwelveSeventyEight : Round5Leaf
  actualFiftyFourResidualAction : Round5Leaf
  nestedLocalGlobalUnitBridge : Round5Leaf

data LeafState : Set where
  owned generated live pruned downstream parallel : LeafState

leafState : Round5Leaf → LeafState
leafState repoNativeVOAActionSurface = owned
leafState selectedThreeBCentralElementReceipts = live
leafState cyclotomicScalarEmbeddingOnSameVOA = live
leafState normalizerPreserveInvertReceipts = live
leafState recognitionOnLiteralVOAZetaEigenspace = live
leafState separatePhaseResolvedConstruction = pruned
leafState separateCyclotomicPhaseAlgebra = pruned
leafState actualFin90InertiaAction = downstream
leafState sameActionTwelveSeventyEight = downstream
leafState actualFiftyFourResidualAction = parallel
leafState nestedLocalGlobalUnitBridge = parallel

voaActionSurfaceIsOwned :
  leafState repoNativeVOAActionSurface ≡ owned
voaActionSurfaceIsOwned = refl

phaseResolvedSearchRemainsPruned :
  leafState separatePhaseResolvedConstruction ≡ pruned
phaseResolvedSearchRemainsPruned = refl

phaseAlgebraSearchIsPruned :
  leafState separateCyclotomicPhaseAlgebra ≡ pruned
phaseAlgebraSearchIsPruned = refl

------------------------------------------------------------------------
-- 2. Highest-alpha recovery is now receipt-level on one literal VOA carrier.
------------------------------------------------------------------------

highestAlphaRound5Leaf : Round5Leaf
highestAlphaRound5Leaf = selectedThreeBCentralElementReceipts

highestAlphaRound5LeafIsLive :
  leafState highestAlphaRound5Leaf ≡ live
highestAlphaRound5LeafIsLive = refl

recognitionRemainsSameCarrierLive :
  leafState recognitionOnLiteralVOAZetaEigenspace ≡ live
recognitionRemainsSameCarrierLive = refl

------------------------------------------------------------------------
-- 3. The cyclotomic phase chart is literally the adapter's existing owner.
------------------------------------------------------------------------

zetaPhaseIsRepoCyclotomicZeta :
  VOAAdapter.phaseCyclotomic VOAAdapter.Inertia.phaseZeta
  ≡ VOAAdapter.C3.zeta
zetaPhaseIsRepoCyclotomicZeta = refl

------------------------------------------------------------------------
-- 4. The attachment-inspired nested-unit question remains parallel.
--
-- The local 54 = 53 + 1 and global 196884 = 196883 + 1 shapes may share a
-- completion pattern, but no equality of their distinguished unit carriers is
-- inferred.  A future bridge must be named and equivariant on an actual action.
------------------------------------------------------------------------

nestedUnitBridgeIsParallelNotGenerated :
  leafState nestedLocalGlobalUnitBridge ≡ parallel
nestedUnitBridgeIsParallelNotGenerated = refl

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record Round5Boundary : Set where
  constructor round5-boundary
  field
    repoVOAActionSurfaceAlreadyOwned : Bool
    freshMonsterCarrierSearchPruned : Bool
    exactOneZetaZetaSquaredPhaseAlgebraOwned : Bool
    zeroIsFourthEigenphase : Bool
    selectedThreeBReceiptsStillLive : Bool
    literalVOAZetaRecognitionStillLive : Bool
    characterZeroCreatesZetaEigenvector : Bool
    fin90ActionDownstream : Bool
    twelveSeventyEightDownstream : Bool
    localGlobalUnitLinesIdentifiedByCardinality : Bool
    localGlobalUnitBridgeStillNeedsEquivariance : Bool

canonicalRound5Boundary : Round5Boundary
canonicalRound5Boundary =
  round5-boundary
    true true true false true true false true true false true

------------------------------------------------------------------------
-- 6. Round-4 phase-resolution pruning remains valid.
------------------------------------------------------------------------

round4PhaseSearchAlreadyPruned :
  R4.searchStatus R4.separatelyConstructPhaseResolvedSector ≡ R4.pruned
round4PhaseSearchAlreadyPruned = refl
