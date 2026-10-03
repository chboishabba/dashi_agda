module DASHI.Moonshine.OggSSP2BSameObjectMaxCutFrontierExact where

------------------------------------------------------------------------
-- 2B SAME-OBJECT MAX-CUT FRONTIER
--
-- This is the canonical programme-status owner after the runtime screens.
-- It keeps focus on the original 2B recognition problem and deliberately
-- treats 31/279, 4371, 4096, radix depth and Frobenius observations as
-- downstream/supporting material unless they construct one of the same-object
-- welds below.
--
-- Remaining scientific spine:
--
--   A' actual Monster-local order-three action on the integral Moonshine
--      carrier, hence actual Tate intertwiners among the three 2B fibres;
--
--   B' one actual ten-dimensional 10a/10b subquotient of one Tate fibre;
--
--   C' a larger sourced action/filtration realizing Completion10 on that
--      subquotient (the bare M22 involution route is dead);
--
--   D  a source-defined five-mode invariant with profile 3,3,2,1,1;
--
--   E  only afterwards promote 30 -> 31 -> 279 to a same-object observable.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BPureKleinFourThreeTateFibreExact as Three
import DASHI.Moonshine.OggSSP2BPureKleinFourM24S3LocalRouteExact as Local
import DASHI.Moonshine.OggSSP2BM22RuntimeMaxCutReceiptExact as Runtime
import DASHI.Moonshine.OggP31CompletionTenTwoSevenNineCrossPollinationExact as P279

------------------------------------------------------------------------
-- 1. Closed architecture retained from the original programme.
------------------------------------------------------------------------

threeTwoBFibres : Nat
threeTwoBFibres = Three.twoBElementCount

threeTwoBFibresIsThree : threeTwoBFibres ≡ 3
threeTwoBFibresIsThree = Three.twoBElementCountIsThree

completionTenPerFibre : Nat
completionTenPerFibre = Three.completionTenPerFibre

transportedSelectedTotal : Nat
transportedSelectedTotal = threeTwoBFibres * completionTenPerFibre

transportedSelectedTotalIsThirty : transportedSelectedTotal ≡ 30
transportedSelectedTotalIsThirty = Three.threeFibreCompletionCountIsThirty

------------------------------------------------------------------------
-- 2. Runtime max-cut consequences.
------------------------------------------------------------------------

tenAFiveCopies : Runtime.factorMultiplicity Runtime.tenA ≡ 5
tenAFiveCopies = Runtime.tenAMultiplicityIsFive

tenBFiveCopies : Runtime.factorMultiplicity Runtime.tenB ≡ 5
tenBFiveCopies = Runtime.tenBMultiplicityIsFive

tenDimensionalFactorMultiplicityIsTen :
  Runtime.factorMultiplicity Runtime.tenA
  + Runtime.factorMultiplicity Runtime.tenB
  ≡ 10
tenDimensionalFactorMultiplicityIsTen =
  Runtime.totalTenDimensionalFactorMultiplicityIsTen

bareM22CompletionRouteKilled :
  Runtime.BareM22InvolutionRealizesCompletionFivePairs → ⊥
bareM22CompletionRouteKilled =
  Runtime.bareM22InvolutionDoesNotRealizeCompletionFivePairs

------------------------------------------------------------------------
-- 3. Three hard same-object welds.
------------------------------------------------------------------------

data ActualMoonshineLocalRepresentationAcquired : Set where
data ActualTateTransportPaid : Set where
data ActualTateTenSubquotientPaid : Set where
data LargerCompletionActionPaid : Set where
data SourceFiveModeDefectPaid : Set where

actualLocalRepresentationStillOpen :
  ActualMoonshineLocalRepresentationAcquired → ⊥
actualLocalRepresentationStillOpen ()

actualTateTransportStillOpen : ActualTateTransportPaid → ⊥
actualTateTransportStillOpen ()

actualTenSubquotientStillOpen : ActualTateTenSubquotientPaid → ⊥
actualTenSubquotientStillOpen ()

largerCompletionActionStillOpen : LargerCompletionActionPaid → ⊥
largerCompletionActionStillOpen ()

sourceFiveModeDefectStillOpen : SourceFiveModeDefectPaid → ⊥
sourceFiveModeDefectStillOpen ()

------------------------------------------------------------------------
-- 4. Downstream observer arithmetic remains available but unpromoted.
------------------------------------------------------------------------

pointedThirtyArithmetic : 1 + transportedSelectedTotal ≡ P279.p31Value
pointedThirtyArithmetic = Three.pointedThreeFibreCompletionIsP31

nonary279Arithmetic :
  P279.nonaryScale * (1 + transportedSelectedTotal) ≡ 279
nonary279Arithmetic = Three.nonaryPointedThreeFibreCompletionIs279

data ThirtyToP31PromotedSameObject : Set where
data P31To279PromotedSameObject : Set where

thirtyToP31StillObserverOnly : ThirtyToP31PromotedSameObject → ⊥
thirtyToP31StillObserverOnly ()

p31To279StillObserverOnly : P31To279PromotedSameObject → ⊥
p31To279StillObserverOnly ()

------------------------------------------------------------------------
-- 5. Canonical status after max-cut.
------------------------------------------------------------------------

record SameObjectMaxCutStatus : Set where
  constructor same-object-max-cut-status
  field
    threeFibreArchitectureClosed : Bool
    localPureC3FiniteElementFound : Bool
    genericTateTransportAlgebraClosed : Bool
    thirtyTraceSplitClosed : Bool

    duadTenFactorsObserved : Bool
    tenAIdentified : Bool
    tenBIdentified : Bool
    bareM22CompletionRouteKilled : Bool

    actualMoonshineLocalRepresentationPaid : Bool
    actualTateTransportPaid : Bool
    actualTateTenSubquotientPaid : Bool
    largerCompletionActionPaid : Bool
    sourceFiveModeDefectPaid : Bool

    p31SameObjectPromotionPaid : Bool
    twoSevenNineSameObjectPromotionPaid : Bool
    sideOntologyFrozenUnlessSourceRelevant : Bool
    nextResidual : String

canonicalSameObjectMaxCutStatus : SameObjectMaxCutStatus
canonicalSameObjectMaxCutStatus =
  same-object-max-cut-status
    true true true true
    true true true true
    false false false false false
    false false true
    "A': acquire the actual local-group representation on the integral Moonshine carrier so the known C3 conjugacy compiles to Tate transport; B': realize one observed 10a/10b factor as an actual Tate subquotient; C': find a larger sourced action or filtration realizing Completion10; then source the 3,3,2,1,1 invariant before touching 31/279 promotion"
