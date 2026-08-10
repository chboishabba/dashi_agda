module DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- DASHI CONTRIBUTION
--
-- Make the remaining Com theorem an operator-realisation problem rather than
-- another shell-arithmetic problem.  A pair product is represented by three
-- nonnegative factors: a left contraction, the cross-fibre overlap, and a
-- right contraction.  If both outer factors are <= 1, the pair product is
-- bounded by the overlap.  Therefore any overlap satisfying the already
-- proved Round-34 half-dyadic envelope gives the required pair-product decay.
--
-- The repository's actual centered (L6,L3) scale calculation is then inserted
-- as a concrete overlap candidate: its two squared Taylor branches obey
--
--   overlap_d <= (1/2) 2^-d.
--
-- Hence the abstract Gram reduction is immediately inhabited by real existing
-- NS arithmetic.  What remains physical is to identify the literal
-- T_q^* T_r and T_q T_r^* norms with such factorized cells.  No operator norm
-- is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Cotlar
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeComCotlarBridgeRound34Exact as Bridge

record GramInterferenceCell (gap : Nat) : Set where
  constructor gram-interference-cell
  field
    leftOuter overlap rightOuter pairProduct : ℚ

    leftOuterNonnegative : 0ℚ ≤ leftOuter
    overlapNonnegative : 0ℚ ≤ overlap
    rightOuterNonnegative : 0ℚ ≤ rightOuter
    pairProductNonnegative : 0ℚ ≤ pairProduct

    leftOuterContraction : leftOuter ≤ 1ℚ
    rightOuterContraction : rightOuter ≤ 1ℚ

    pairProductFactorizationBound :
      pairProduct ≤ leftOuter * overlap * rightOuter

open GramInterferenceCell public

outerContractionsRemove :
  ∀ {gap} (cell : GramInterferenceCell gap) →
  pairProduct cell ≤ overlap cell
outerContractionsRemove cell =
  let
    leftTimesOverlap :
      leftOuter cell * overlap cell ≤ overlap cell
    leftTimesOverlap =
      subst
        (λ upper → leftOuter cell * overlap cell ≤ upper)
        (ℚP.*-identityˡ (overlap cell))
        (L2.nonnegativeProductMonotone
          (leftOuterNonnegative cell)
          (overlapNonnegative cell)
          ℚP.0≤1
          (overlapNonnegative cell)
          (leftOuterContraction cell)
          ℚP.≤-refl)

    factorNN : 0ℚ ≤ leftOuter cell * overlap cell
    factorNN =
      let
        instance
          leftNN = nonNegative (leftOuterNonnegative cell)
          overlapNN = nonNegative (overlapNonnegative cell)
          productNN =
            ℚP.nonNeg*nonNeg⇒nonNeg (leftOuter cell) (overlap cell)
      in
      ℚP.nonNegative⁻¹ (leftOuter cell * overlap cell)

    withRight :
      leftOuter cell * overlap cell * rightOuter cell
      ≤ overlap cell * 1ℚ
    withRight =
      L2.nonnegativeProductMonotone
        factorNN
        (rightOuterNonnegative cell)
        (overlapNonnegative cell)
        ℚP.0≤1
        leftTimesOverlap
        (rightOuterContraction cell)

    endpoint : overlap cell * 1ℚ ≡ overlap cell
    endpoint = ℚP.*-identityʳ (overlap cell)
  in
  ℚP.≤-trans
    (pairProductFactorizationBound cell)
    (subst
      (λ upper →
        leftOuter cell * overlap cell * rightOuter cell ≤ upper)
      endpoint
      withRight)

record HalfDyadicGramCell (gap : Nat) : Set where
  constructor half-dyadic-gram-cell
  field
    gramCell : GramInterferenceCell gap
    overlapHalfDyadic :
      overlap gramCell ≤ Cotlar.directEnvelope Bridge.half gap

open HalfDyadicGramCell public

halfDyadicGramPairDecay :
  ∀ {gap} (cell : HalfDyadicGramCell gap) →
  pairProduct (gramCell cell)
  ≤ Cotlar.directEnvelope Bridge.half gap
halfDyadicGramPairDecay cell =
  ℚP.≤-trans
    (outerContractionsRemove (gramCell cell))
    (overlapHalfDyadic cell)

sixThreeOverlapNonnegative :
  ∀ gap → 0ℚ ≤ SixThree.twoBranchSquaredGap gap
sixThreeOverlapNonnegative gap =
  L2.addNonnegative
    (SixThree.strongBranchSquaredNonnegative gap)
    (SixThree.weakBranchSquaredNonnegative gap)

sixThreeGramCell : Nat → GramInterferenceCell
sixThreeGramCell gap =
  gram-interference-cell
    1ℚ
    (SixThree.twoBranchSquaredGap gap)
    1ℚ
    (SixThree.twoBranchSquaredGap gap)
    ℚP.0≤1
    (sixThreeOverlapNonnegative gap)
    ℚP.0≤1
    (sixThreeOverlapNonnegative gap)
    ℚP.≤-refl
    ℚP.≤-refl
    pairExact
  where
  pairExact :
    SixThree.twoBranchSquaredGap gap
    ≤ 1ℚ * SixThree.twoBranchSquaredGap gap * 1ℚ
  pairExact =
    let
      productIdentity :
        1ℚ * SixThree.twoBranchSquaredGap gap * 1ℚ
        ≡ SixThree.twoBranchSquaredGap gap
      productIdentity =
        trans
          (cong (_* 1ℚ)
            (ℚP.*-identityˡ (SixThree.twoBranchSquaredGap gap)))
          (ℚP.*-identityʳ (SixThree.twoBranchSquaredGap gap))
    in
    subst
      (λ upper → SixThree.twoBranchSquaredGap gap ≤ upper)
      (sym productIdentity)
      ℚP.≤-refl

sixThreeHalfDyadicGramCell : Nat → HalfDyadicGramCell
sixThreeHalfDyadicGramCell gap =
  half-dyadic-gram-cell
    (sixThreeGramCell gap)
    (Bridge.sixThreeSquaredGapFitsCotlarHalf gap)

sixThreeGramCandidatePairDecay :
  ∀ gap →
  pairProduct (sixThreeGramCell gap)
  ≤ Cotlar.directEnvelope Bridge.half gap
sixThreeGramCandidatePairDecay gap =
  halfDyadicGramPairDecay (sixThreeHalfDyadicGramCell gap)

record PhysicalComPairProductGramRealization : Set where
  field
    leftAdjointRightProduct : Nat → Nat → ℚ
    leftRightAdjointProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat

    leftAdjointRightGram :
      ∀ q r → GramInterferenceCell (shellDistance q r)
    leftRightAdjointGram :
      ∀ q r → GramInterferenceCell (shellDistance q r)

    firstProductExact : ∀ q r →
      leftAdjointRightProduct q r
      ≡ pairProduct (leftAdjointRightGram q r)

    secondProductExact : ∀ q r →
      leftRightAdjointProduct q r
      ≡ pairProduct (leftRightAdjointGram q r)

    firstOverlapHalfDyadic : ∀ q r →
      overlap (leftAdjointRightGram q r)
      ≤ Cotlar.directEnvelope Bridge.half (shellDistance q r)

    secondOverlapHalfDyadic : ∀ q r →
      overlap (leftRightAdjointGram q r)
      ≤ Cotlar.directEnvelope Bridge.half (shellDistance q r)

open PhysicalComPairProductGramRealization public

physicalComFirstPairDecayFromGram :
  (realization : PhysicalComPairProductGramRealization) →
  ∀ q r →
  leftAdjointRightProduct realization q r
  ≤ Cotlar.directEnvelope Bridge.half
      (shellDistance realization q r)
physicalComFirstPairDecayFromGram realization q r =
  subst
    (λ lower →
      lower ≤ Cotlar.directEnvelope Bridge.half
        (shellDistance realization q r))
    (sym (firstProductExact realization q r))
    (ℚP.≤-trans
      (outerContractionsRemove
        (leftAdjointRightGram realization q r))
      (firstOverlapHalfDyadic realization q r))

physicalComSecondPairDecayFromGram :
  (realization : PhysicalComPairProductGramRealization) →
  ∀ q r →
  leftRightAdjointProduct realization q r
  ≤ Cotlar.directEnvelope Bridge.half
      (shellDistance realization q r)
physicalComSecondPairDecayFromGram realization q r =
  subst
    (λ lower →
      lower ≤ Cotlar.directEnvelope Bridge.half
        (shellDistance realization q r))
    (sym (secondProductExact realization q r))
    (ℚP.≤-trans
      (outerContractionsRemove
        (leftRightAdjointGram realization q r))
      (secondOverlapHalfDyadic realization q r))

comGramInterferenceReductionClosed : Bool
comGramInterferenceReductionClosed = true

sixThreeGramCandidateClosed : Bool
sixThreeGramCandidateClosed = true

physicalComPairProductGramRealizationConstructed : Bool
physicalComPairProductGramRealizationConstructed = false

comGramInterferenceReductionClosedIsTrue :
  comGramInterferenceReductionClosed ≡ true
comGramInterferenceReductionClosedIsTrue = refl

sixThreeGramCandidateClosedIsTrue :
  sixThreeGramCandidateClosed ≡ true
sixThreeGramCandidateClosedIsTrue = refl

physicalComPairProductGramRealizationConstructedIsFalse :
  physicalComPairProductGramRealizationConstructed ≡ false
physicalComPairProductGramRealizationConstructedIsFalse = refl
