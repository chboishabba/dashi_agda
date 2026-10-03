module DASHI.Moonshine.OggSSP2BSameObjectMaxCutFrontierExact where

------------------------------------------------------------------------
-- 2B SAME-OBJECT MAX-CUT FRONTIER
--
-- Canonical status after the finite runtime screens and source recut.
--
-- Closed / externally sourced:
--   * three 2B fibres and the local C3 carrier cycle;
--   * self-dual integral Moonshine form with Monster symmetry;
--   * 2B-pure local subgroup and pure order-three transporter;
--   * generic conjugacy -> Tate transport algebra;
--   * M24-duad restriction contains 10a^5 and 10b^5;
--   * bare M22 involution cannot realize Completion10 five-pair phase;
--   * binary-tetrahedral defect meaning is the centralizer 2-adic exponent,
--     with sourced profile 3,3,2,1,1;
--   * transported 30 and its downstream arithmetic remain available.
--
-- Remaining same-object welds:
--
--   A' represent the full sourced integral Monster action on the repo's actual
--      weight-two/Tate carrier and identify the current 4A multiplicity owner
--      with that carrier.  Then the known C3 transport is automatic.
--
--   B' realize one observed 10a or 10b as a genuine subquotient of one actual
--      2B Tate fibre.
--
--   C' identify a larger sourced action/filtration on that Q10 whose binary
--      operator is Completion10.  The bare M22 involution route is dead.
--
--   D  identify the five recognized Q10 modes with the five independently
--      sourced binary-tetrahedral order strata.  The defect invariant itself
--      is no longer open.
--
--   E  only after A'-D promote 30 -> 31 -> 279 to same-object observables.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BPureKleinFourThreeTateFibreExact as Three
import DASHI.Moonshine.OggSSP2BM22RuntimeMaxCutReceiptExact as Runtime
import DASHI.Moonshine.OggSSP2BIntegralMoonshineLocalActionSourceExact as ActionSource
import DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact as DefectSource
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
-- 3. A' source existence is paid; formal same-object acquisition is not.
------------------------------------------------------------------------

externalIntegralLocalActionSourced :
  ActionSource.restrictedLocalActionExistsMathematically
    ActionSource.canonicalIntegralMoonshineLocalActionSource
  ≡ true
externalIntegralLocalActionSourced =
  ActionSource.externalRestrictedLocalActionIsSourced

formalTateCarrierWeldOpen :
  ActionSource.sameObjectTateCarrierWeldPaid
    ActionSource.canonicalIntegralMoonshineLocalActionSource
  ≡ false
formalTateCarrierWeldOpen =
  ActionSource.repoSameObjectTateCarrierWeldStillOpen

------------------------------------------------------------------------
-- 4. D invariant meaning is paid; actual mode recognition is not.
------------------------------------------------------------------------

defectIdentityThree :
  DefectSource.twoAdicCentralizerExponent DefectSource.identity ≡ 3
defectIdentityThree = DefectSource.defectIdentityIsThree

defectMinusOneThree :
  DefectSource.twoAdicCentralizerExponent DefectSource.centralMinusOne ≡ 3
defectMinusOneThree = DefectSource.defectMinusOneIsThree

defectOrderFourTwo :
  DefectSource.twoAdicCentralizerExponent DefectSource.orderFour ≡ 2
defectOrderFourTwo = DefectSource.defectOrderFourIsTwo

defectOrderThreeOne :
  DefectSource.twoAdicCentralizerExponent DefectSource.orderThree ≡ 1
defectOrderThreeOne = DefectSource.defectOrderThreeIsOne

defectOrderSixOne :
  DefectSource.twoAdicCentralizerExponent DefectSource.orderSix ≡ 1
defectOrderSixOne = DefectSource.defectOrderSixIsOne

------------------------------------------------------------------------
-- 5. Three hard formal same-object welds plus the D recognition map.
------------------------------------------------------------------------

data FormalIntegralTateCarrierWeldPaid : Set where
data ActualTateTenSubquotientPaid : Set where
data LargerCompletionActionPaid : Set where
data ActualQ10ModeToOrderStratumRecognitionPaid : Set where

formalIntegralTateCarrierWeldStillOpen :
  FormalIntegralTateCarrierWeldPaid → ⊥
formalIntegralTateCarrierWeldStillOpen ()

actualTenSubquotientStillOpen : ActualTateTenSubquotientPaid → ⊥
actualTenSubquotientStillOpen ()

largerCompletionActionStillOpen : LargerCompletionActionPaid → ⊥
largerCompletionActionStillOpen ()

actualModeDefectRecognitionStillOpen :
  ActualQ10ModeToOrderStratumRecognitionPaid → ⊥
actualModeDefectRecognitionStillOpen ()

------------------------------------------------------------------------
-- 6. Downstream observer arithmetic remains available but unpromoted.
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
-- 7. Canonical status after max-cut.
------------------------------------------------------------------------

record SameObjectMaxCutStatus : Set where
  constructor same-object-max-cut-status
  field
    threeFibreArchitectureClosed : Bool
    localPureC3FiniteElementFound : Bool
    externalIntegralMonsterActionSourced : Bool
    genericConjugacyToTateCompilerClosed : Bool
    thirtyTraceSplitClosed : Bool

    duadTenFactorsObserved : Bool
    tenAIdentified : Bool
    tenBIdentified : Bool
    bareM22CompletionRouteKilled : Bool

    binaryTetrahedralDefectMeaningSourced : Bool
    defectProfileThreeThreeTwoOneOnePaid : Bool

    formalIntegralTateCarrierWeldPaid : Bool
    actualTateTenSubquotientPaid : Bool
    largerCompletionActionPaid : Bool
    actualQ10ModeToDefectStratumRecognitionPaid : Bool

    p31SameObjectPromotionPaid : Bool
    twoSevenNineSameObjectPromotionPaid : Bool
    sideOntologyFrozenUnlessSourceRelevant : Bool
    nextResidual : String

canonicalSameObjectMaxCutStatus : SameObjectMaxCutStatus
canonicalSameObjectMaxCutStatus =
  same-object-max-cut-status
    true true true true true
    true true true true
    true true
    false false false false
    false false true
    "A': weld the sourced full integral Monster action to the current 4A/Tate carrier; B': realize one observed 10a/10b factor as an actual Tate subquotient; C': source the larger Completion10 action; D: identify the actual Q10 Mode5 labels with binary-tetrahedral order strata; only then promote 31/279"
