module DASHI.Physics.Closure.NSTriadKNLuoSixThreeComCotlarBridgeRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Connect the repository's already-proved finite L6--L3 centered-commutator
-- scale arithmetic to the exact Round-34 Cotlar target.
--
-- The earlier module proves that the two squared Taylor branches satisfy
--
--   strong_d + weak_d <= 2 * weak_d,
--
-- with
--
--   weak_d = (1/4) 2^-d.
--
-- Hence, exactly,
--
--   strong_d + weak_d <= (1/2) 2^-d.
--
-- This is the direct Round-34 dyadic envelope with concrete constant C=1/2.
-- Its full symmetric Cotlar shell mass therefore has the exact finite-radius
-- conservation law
--
--   budget_R + 2^-R = 3/2,
--
-- because the generic tail at C=1/2 is exactly 2^-R.  Thus the shell
-- arithmetic needed by the successful finite-exponent commutator route fits
-- inside a cutoff-independent candidate row budget 3/2.
--
-- The theorem is deliberately scalar: it does not identify these coefficients
-- with ||T_q^* T_r|| or ||T_q T_r^*||.  The remaining physical `Com` producer
-- is precisely that operator-realisation estimate on the literal shell family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL
import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Cotlar
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Dyadic

half threeHalves : ℚ
half = Int.+ 1 / 2
threeHalves = Int.+ 3 / 2

weakTwiceIsHalfDyadic :
  ∀ gap →
  SixThree.two * SixThree.weakBranchSquaredGap gap
  ≡ Cotlar.directEnvelope half gap
weakTwiceIsHalfDyadic gap =
  ℚRing.solve-∀
    (HL.highLowDerivativeRatio gap)
    (Cotlar.dyadicWeight gap)

-- The previous identity needs the literal definitions aligned.  This separate
-- theorem records that the high--low ratio is quarter times the same dyadic
-- weight used by Round 34.
highLowRatioIsQuarterDyadic :
  ∀ gap →
  HL.highLowDerivativeRatio gap
  ≡ HL.quarter * Cotlar.dyadicWeight gap
highLowRatioIsQuarterDyadic zero = refl
highLowRatioIsQuarterDyadic (Agda.Builtin.Nat.suc gap)
  rewrite highLowRatioIsQuarterDyadic gap =
  ℚRing.solve-∀ (Cotlar.dyadicWeight gap)

weakTwiceDirectEnvelopeExact :
  ∀ gap →
  SixThree.two * SixThree.weakBranchSquaredGap gap
  ≡ Cotlar.directEnvelope half gap
weakTwiceDirectEnvelopeExact gap =
  trans
    (congTwoWeak gap)
    (ℚRing.solve-∀ (Cotlar.dyadicWeight gap))
  where
  congTwoWeak :
    ∀ selectedGap →
    SixThree.two * SixThree.weakBranchSquaredGap selectedGap
    ≡ SixThree.two * (HL.quarter * Cotlar.dyadicWeight selectedGap)
  congTwoWeak selectedGap =
    Relation.Binary.PropositionalEquality.cong
      (SixThree.two *_)
      (highLowRatioIsQuarterDyadic selectedGap)

sixThreeSquaredGapFitsCotlarHalf :
  ∀ gap →
  SixThree.twoBranchSquaredGap gap
  ≤ Cotlar.directEnvelope half gap
sixThreeSquaredGapFitsCotlarHalf gap =
  subst
    (λ upper → SixThree.twoBranchSquaredGap gap ≤ upper)
    (weakTwiceDirectEnvelopeExact gap)
    (SixThree.twoBranchDominatedByTwiceWeak gap)

sixThreeCotlarRadiusBudget : Nat → ℚ
sixThreeCotlarRadiusBudget radius =
  Cotlar.directRadiusBudget half radius

sixThreeCotlarRadiusBudgetPlusTailExact :
  ∀ radius →
  sixThreeCotlarRadiusBudget radius
    + Cotlar.dyadicWeight radius
  ≡ threeHalves
sixThreeCotlarRadiusBudgetPlusTailExact radius =
  let
    generic = Cotlar.directRadiusBudgetPlusTailExact half radius

    tailMeaning :
      half * Dyadic.two * Cotlar.dyadicWeight radius
      ≡ Cotlar.dyadicWeight radius
    tailMeaning = ℚRing.solve-∀ (Cotlar.dyadicWeight radius)

    endpointMeaning : half * Cotlar.three ≡ threeHalves
    endpointMeaning = ℚRing.solve []
  in
  subst
    (λ tail → sixThreeCotlarRadiusBudget radius + tail ≡ threeHalves)
    tailMeaning
    (subst
      (λ endpoint →
        sixThreeCotlarRadiusBudget radius
          + half * Dyadic.two * Cotlar.dyadicWeight radius
        ≡ endpoint)
      endpointMeaning
      generic)

sixThreeScalarCotlarCandidateClosed : Bool
sixThreeScalarCotlarCandidateClosed = true

sixThreePhysicalOperatorPairDecayConstructed : Bool
sixThreePhysicalOperatorPairDecayConstructed = false

sixThreeScalarCotlarCandidateClosedIsTrue :
  sixThreeScalarCotlarCandidateClosed ≡ true
sixThreeScalarCotlarCandidateClosedIsTrue = refl

sixThreePhysicalOperatorPairDecayConstructedIsFalse :
  sixThreePhysicalOperatorPairDecayConstructed ≡ false
sixThreePhysicalOperatorPairDecayConstructedIsFalse = refl
