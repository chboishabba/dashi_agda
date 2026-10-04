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
--   * M22:2 DOES contain the finite Completion10 phase candidate: in both
--     ten-dimensional modules an outer involution class has J2^5 shape and a
--     verified five-swapped-pair basis;
--   * binary-tetrahedral defect meaning is the centralizer 2-adic exponent,
--     with sourced profile 3,3,2,1,1;
--   * defect preservation cuts D from 120 arbitrary bijections to exactly four
--     source-compatible charts, equivalently two independent source choices;
--   * mode27 -> orderFour is forced by the unique depth-2 stratum;
--   * binary-tetrahedral central -1 is NOT a shortcut for Completion10
--     BinaryPhase on the five-mode quotient;
--   * transported 30 and its downstream arithmetic remain available.
--
-- Remaining same-object welds:
--
--   A' represent the full sourced integral Monster action on the repo's actual
--      weight-two/Tate carrier and identify the current 4A multiplicity owner
--      with that carrier.  Then the known C3 transport is automatic.
--
--   B' realize one observed M22:2 ten-module (restricting to 10a/10b) as a
--      genuine subquotient of one actual 2B Tate fibre.  The focused CTblLib
--      class-fusion/Brauer-character screen is now the finite test for the
--      M24-duad semisimplified ingress.
--
--   C' prove the sourced M22:2 outer involution action descends to that SAME
--      Tate subquotient and becomes the Completion10 binary phase.  The finite
--      phase source is no longer open; only the actual-Tate same-object weld is.
--
--   D  source the two remaining orientation decisions:
--        mode09/mode18 <-> identity/centralMinusOne,
--        mode36/mode45 <-> orderThree/orderSix.
--      The orderFour assignment is already forced.
--
--   E  only after A'-D promote 30 -> 31 -> 279 to same-object observables.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Moonshine.OggSSP2BPureKleinFourThreeTateFibreExact as Three
import DASHI.Moonshine.OggSSP2BM22RuntimeMaxCutReceiptExact as Runtime
import DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact as CompletionRuntime
import DASHI.Moonshine.OggSSP2BIntegralMoonshineLocalActionSourceExact as ActionSource
import DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact as DefectSource
import DASHI.Moonshine.OggSSP2BDefectRecognitionAmbiguityExact as DefectAmbiguity
import DASHI.Moonshine.OggSSP2BDefectTwoBitProvenanceSelectorExact as DefectBits
import DASHI.Moonshine.OggSSP2BBinaryTetrahedralCentralSignPhaseNoGoExact as CentralSignNoGo
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

m22d2FiniteCompletionPhaseObserved :
  CompletionRuntime.finiteCompletionPhaseCandidatePaid
    CompletionRuntime.canonicalFiniteM22d2Completion10Receipt
  ≡ true
m22d2FiniteCompletionPhaseObserved =
  CompletionRuntime.finiteCompletionPhaseCandidateIsPaid

m22d2OuterFivePairBasisVerified :
  CompletionRuntime.fiveSwapPairsVerified
    CompletionRuntime.tenAOuterCompletionCandidate
  ≡ true
m22d2OuterFivePairBasisVerified = refl

m22d2OuterMatchCountIsTwo :
  CompletionRuntime.outerJ2x5MatchCount ≡ 2
m22d2OuterMatchCountIsTwo =
  CompletionRuntime.outerJ2x5MatchCountIsTwo

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
-- 4. D invariant meaning is paid; exactly two source choices remain.
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

defectCompatibleChartCountIsFour :
  DefectAmbiguity.defectCompatibleChartCount ≡ 4
defectCompatibleChartCountIsFour =
  DefectAmbiguity.defectCompatibleChartCountIsFour

remainingDefectSourceDecisionCount : Nat
remainingDefectSourceDecisionCount = 2

remainingDefectSourceDecisionCountIsTwo :
  remainingDefectSourceDecisionCount ≡ 2
remainingDefectSourceDecisionCountIsTwo = refl

orderFourAssignmentIsForced :
  (bits : DefectBits.ProvenanceBits) →
  DefectBits.chartFromBits bits Completion.mode27
  ≡ DefectSource.orderFour
orderFourAssignmentIsForced = DefectBits.orderFourIsForced

centralSignShortcutStillKilled :
  CentralSignNoGo.CompletionModePreservingPhaseIsCentralSignOnStrata → ⊥
centralSignShortcutStillKilled =
  CentralSignNoGo.completionModePreservingPhaseIsNotCentralSignOnStrata

------------------------------------------------------------------------
-- 5. Remaining formal same-object welds.
------------------------------------------------------------------------

data FormalIntegralTateCarrierWeldPaid : Set where
data ActualTateTenSubquotientPaid : Set where
data ActualTateCompletionActionPaid : Set where
data ActualQ10ModeToOrderStratumRecognitionPaid : Set where

LargerCompletionActionPaid : Set
LargerCompletionActionPaid = ActualTateCompletionActionPaid

formalIntegralTateCarrierWeldStillOpen :
  FormalIntegralTateCarrierWeldPaid → ⊥
formalIntegralTateCarrierWeldStillOpen ()

actualTenSubquotientStillOpen : ActualTateTenSubquotientPaid → ⊥
actualTenSubquotientStillOpen ()

actualTateCompletionActionStillOpen : ActualTateCompletionActionPaid → ⊥
actualTateCompletionActionStillOpen ()

largerCompletionActionStillOpen : LargerCompletionActionPaid → ⊥
largerCompletionActionStillOpen = actualTateCompletionActionStillOpen

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
-- 7. Canonical status after B'-screen construction / C'/D max-cut.
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
    m22d2OuterCompletionCandidateObserved : Bool
    m22d2OuterFivePairBasisVerified : Bool

    binaryTetrahedralDefectMeaningSourced : Bool
    defectProfileThreeThreeTwoOneOnePaid : Bool
    defectCompatibleChartCount : Nat
    remainingDefectSourceDecisionCount : Nat
    centralSignPhaseShortcutKilled : Bool

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
    true true true true true true
    true true 4 2 true
    false false false false
    false false true
    "B': run the focused 2B-centralizer/M24 2-regular character screen and, if equal, promote the resulting actual Tate semisimplified M22 10a/10b subquotient receipt; C': prove the sourced M22:2 outer J2^5 action acts on that same quotient; D: source exactly two orientation decisions (depth-3 and depth-1); central -1 is ruled out as the Mode5-preserving BinaryPhase shortcut; only then promote 31/279"
