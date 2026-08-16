module DASHI.Physics.Closure.NSTriadKNComTwoBranchFiniteGramRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title/context: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
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
-- ROUND 62 CONTRIBUTION
--
-- Round61 correctly stopped asking the physical Fourier Gram to equal the
-- synthetic six-three model cell.  It still asked the producer to supply an
-- actual GramInterferenceCell and its overlap estimate as primitive fields.
-- This module removes those two fields.
--
-- The normalized physical odd-(P/Q) fibre is represented by TWO explicit
-- finite rational pair families, corresponding to the strong and weak
-- centered-commutator branches.  The repository already proves finite squared
-- Cauchy--Schwarz exactly.  Therefore the only branch-local analytic inputs are
--
--   ||L_s||^2 <= strongGap,   ||R_s||^2 <= 1,
--   ||L_w||^2 <= weakGap,     ||R_w||^2 <= 1.
--
-- Cauchy--Schwarz proves
--
--   <L_s,R_s>^2 + <L_w,R_w>^2
--     <= strongGap + weakGap
--      = twoBranchSquaredGap.
--
-- From this theorem we CONSTRUCT the actual Round61 physical Gram cell with
-- pairProduct equal to the literal normalized fibre quantity and overlap equal
-- to the six-three envelope.  B1/B3 are thus no longer producer assumptions:
-- the remaining B analysis is reduced to explicit normalized fibre extraction
-- plus four one-sided finite norm bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComActiveSixThreeRealizationRound61Exact as Round61
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

record PhysicalOddPQTwoBranchFiniteGramSource : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    strongPairs weakPairs : Nat → Nat → List L2.Pair

    shellDistance : Nat → Nat → Nat
    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q → shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q → shellDistance (suc q) q ≡ suc zero

    inactivePairProductZero : ∀ q r →
      Hat.supportActive support q r ≡ false →
      L2.square (L2.pairDot (strongPairs q r))
        + L2.square (L2.pairDot (weakPairs q r))
      ≡ 0ℚ

    strongLeftMassBound : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.leftNormSquared (strongPairs q r)
      ≤ SixThree.strongBranchSquaredGap (shellDistance q r)

    strongRightContraction : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.rightNormSquared (strongPairs q r) ≤ 1ℚ

    weakLeftMassBound : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.leftNormSquared (weakPairs q r)
      ≤ SixThree.weakBranchSquaredGap (shellDistance q r)

    weakRightContraction : ∀ q r →
      Hat.supportActive support q r ≡ true →
      L2.rightNormSquared (weakPairs q r) ≤ 1ℚ

open PhysicalOddPQTwoBranchFiniteGramSource public

normalizedPairProduct :
  PhysicalOddPQTwoBranchFiniteGramSource → Nat → Nat → ℚ
normalizedPairProduct physical q r =
  L2.square (L2.pairDot (strongPairs physical q r))
  + L2.square (L2.pairDot (weakPairs physical q r))

normalizedPairProductNonnegative :
  (physical : PhysicalOddPQTwoBranchFiniteGramSource) →
  ∀ q r → 0ℚ ≤ normalizedPairProduct physical q r
normalizedPairProductNonnegative physical q r =
  L2.addNonnegative
    (L2.squareNonnegative (L2.pairDot (strongPairs physical q r)))
    (L2.squareNonnegative (L2.pairDot (weakPairs physical q r)))

private
  branchPairBelowBudget :
    (pairs : List L2.Pair) → (budget : ℚ) →
    0ℚ ≤ budget →
    L2.leftNormSquared pairs ≤ budget →
    L2.rightNormSquared pairs ≤ 1ℚ →
    L2.square (L2.pairDot pairs) ≤ budget
  branchPairBelowBudget pairs budget budgetNN leftBound rightBound =
    let
      cauchy = L2.finiteCauchySchwarzSquared pairs
      normProductBound =
        L2.nonnegativeProductMonotone
          (L2.leftNormSquaredNonnegative pairs)
          (L2.rightNormSquaredNonnegative pairs)
          budgetNN ℚP.0≤1 leftBound rightBound
    in
    ℚP.≤-trans cauchy
      (subst
        (λ upper →
          L2.leftNormSquared pairs * L2.rightNormSquared pairs ≤ upper)
        (ℚP.*-identityʳ budget)
        normProductBound)

strongPairBelowStrongGap :
  (physical : PhysicalOddPQTwoBranchFiniteGramSource) → ∀ q r →
  Hat.supportActive (support physical) q r ≡ true →
  L2.square (L2.pairDot (strongPairs physical q r))
  ≤ SixThree.strongBranchSquaredGap (shellDistance physical q r)
strongPairBelowStrongGap physical q r active =
  branchPairBelowBudget
    (strongPairs physical q r)
    (SixThree.strongBranchSquaredGap (shellDistance physical q r))
    (SixThree.strongBranchSquaredNonnegative (shellDistance physical q r))
    (strongLeftMassBound physical q r active)
    (strongRightContraction physical q r active)

weakPairBelowWeakGap :
  (physical : PhysicalOddPQTwoBranchFiniteGramSource) → ∀ q r →
  Hat.supportActive (support physical) q r ≡ true →
  L2.square (L2.pairDot (weakPairs physical q r))
  ≤ SixThree.weakBranchSquaredGap (shellDistance physical q r)
weakPairBelowWeakGap physical q r active =
  branchPairBelowBudget
    (weakPairs physical q r)
    (SixThree.weakBranchSquaredGap (shellDistance physical q r))
    (SixThree.weakBranchSquaredNonnegative (shellDistance physical q r))
    (weakLeftMassBound physical q r active)
    (weakRightContraction physical q r active)

activePairProductBelowSixThree :
  (physical : PhysicalOddPQTwoBranchFiniteGramSource) → ∀ q r →
  Hat.supportActive (support physical) q r ≡ true →
  normalizedPairProduct physical q r
  ≤ SixThree.twoBranchSquaredGap (shellDistance physical q r)
activePairProductBelowSixThree physical q r active =
  ℚP.+-mono-≤
    (strongPairBelowStrongGap physical q r active)
    (weakPairBelowWeakGap physical q r active)

activePhysicalGramCell :
  (physical : PhysicalOddPQTwoBranchFiniteGramSource) → ∀ q r →
  Hat.supportActive (support physical) q r ≡ true →
  Gram.GramInterferenceCell (shellDistance physical q r)
activePhysicalGramCell physical q r active =
  Gram.gram-interference-cell
    1ℚ (SixThree.twoBranchSquaredGap gap) 1ℚ
    (normalizedPairProduct physical q r)
    ℚP.0≤1 (Gram.sixThreeOverlapNonnegative gap) ℚP.0≤1
    (normalizedPairProductNonnegative physical q r)
    ℚP.≤-refl ℚP.≤-refl factorizationBound
  where
  gap = shellDistance physical q r
  factorizationBound :
    normalizedPairProduct physical q r
    ≤ 1ℚ * SixThree.twoBranchSquaredGap gap * 1ℚ
  factorizationBound =
    subst
      (λ upper → normalizedPairProduct physical q r ≤ upper)
      (sym (solve (SixThree.twoBranchSquaredGap gap ∷ [])))
      (activePairProductBelowSixThree physical q r active)

asRound61PhysicalSource :
  PhysicalOddPQTwoBranchFiniteGramSource →
  Round61.PhysicalActiveSixThreeOddPQSource
asRound61PhysicalSource physical = record
  { support = support physical
  ; normalizedPairProduct = normalizedPairProduct physical
  ; normalizedPairProductNonnegative = normalizedPairProductNonnegative physical
  ; shellDistance = shellDistance physical
  ; sameShellDistance = sameShellDistance physical
  ; forwardAdjacentDistance = forwardAdjacentDistance physical
  ; reverseAdjacentDistance = reverseAdjacentDistance physical
  ; inactivePairProductZero = inactivePairProductZero physical
  ; activePhysicalGramCell = activePhysicalGramCell physical
  ; activeProductIsPhysicalGram = λ q r active → refl
  ; activePhysicalOverlapBelowSixThree = λ q r active → ℚP.≤-refl
  }

fullBandwidthOneMassBelow133Over256FromFiniteBranches :
  (physical : PhysicalOddPQTwoBranchFiniteGramSource) → ∀ q →
  Aggregate.normalizedOddPQBandwidthOneMass
    (Round61.asPhysicalNormalizedOddPQSource
      (asRound61PhysicalSource physical)) q
  ≤ Aggregate.bandwidthOneTarget
fullBandwidthOneMassBelow133Over256FromFiniteBranches physical =
  Round61.fullBandwidthOneMassBelow133Over256
    (asRound61PhysicalSource physical)

b1AndB3ReducedToFiniteCauchyBranchBounds : Bool
b1AndB3ReducedToFiniteCauchyBranchBounds = true

b1AndB3ReducedToFiniteCauchyBranchBoundsIsTrue :
  b1AndB3ReducedToFiniteCauchyBranchBounds ≡ true
b1AndB3ReducedToFiniteCauchyBranchBoundsIsTrue = refl
