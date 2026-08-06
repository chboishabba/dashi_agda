module DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact where

------------------------------------------------------------------------
-- PROVENANCE
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
-- PURPOSE
-- Close the radical-free dyadic arithmetic of the successful finite-exponent
-- (L6,L3) centered-commutator route.  If the low shell is d=gap+2 steps below
-- the output shell, the two unsquared Taylor gains are
--
--   2^(-3d/2),   2^(-d/2).
--
-- Their squares are
--
--   2^(-3d) = (1/64)(1/8)^gap,
--   2^(-d)  = (1/4)(1/2)^gap.
--
-- The strong first branch is pointwise dominated by the weak second branch,
-- while the finite weak-prefix mass is at most 1/2.  Thus the complete
-- two-branch squared gap budget is at most twice the weak kernel and has
-- uniformly bounded finite prefixes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; subst; sym)
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Dyadic

oneEighth oneSixtyFourth two : ℚ
oneEighth = Int.+ 1 / 8
oneSixtyFourth = Int.+ 1 / 64
two = Int.+ 2 / 1

oneEighthNonnegative : 0ℚ ≤ oneEighth
oneEighthNonnegative = toWitness {a? = 0ℚ ≤? oneEighth} _

oneSixtyFourthNonnegative : 0ℚ ≤ oneSixtyFourth
oneSixtyFourthNonnegative =
  toWitness {a? = 0ℚ ≤? oneSixtyFourth} _

oneEighthBelowHalf : oneEighth ≤ HL.half
oneEighthBelowHalf = toWitness {a? = oneEighth ≤? HL.half} _

oneSixtyFourthBelowQuarter : oneSixtyFourth ≤ HL.quarter
oneSixtyFourthBelowQuarter =
  toWitness {a? = oneSixtyFourth ≤? HL.quarter} _

powOneEighthBelowPowHalf :
  (gap : Nat) →
  Geo.pow oneEighth gap ≤ Geo.pow HL.half gap
powOneEighthBelowPowHalf zero = ℚₚ.≤-refl
powOneEighthBelowPowHalf (suc gap) =
  L2.nonnegativeProductMonotone
    oneEighthNonnegative
    (Geo.powNonnegative oneEighth gap oneEighthNonnegative)
    HL.halfNonnegative
    (Geo.powNonnegative HL.half gap HL.halfNonnegative)
    oneEighthBelowHalf
    (powOneEighthBelowPowHalf gap)

strongBranchSquaredGap : Nat → ℚ
strongBranchSquaredGap gap =
  oneSixtyFourth * Geo.pow oneEighth gap

weakBranchSquaredGap : Nat → ℚ
weakBranchSquaredGap = HL.highLowDerivativeRatio

strongBranchSquaredNonnegative :
  (gap : Nat) →
  0ℚ ≤ strongBranchSquaredGap gap
strongBranchSquaredNonnegative gap =
  let
    instance
      leadingIsNonnegative = nonNegative oneSixtyFourthNonnegative
      powerIsNonnegative =
        nonNegative (Geo.powNonnegative oneEighth gap oneEighthNonnegative)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          oneSixtyFourth (Geo.pow oneEighth gap)
  in
  ℚₚ.nonNegative⁻¹ (strongBranchSquaredGap gap)

weakBranchSquaredNonnegative :
  (gap : Nat) →
  0ℚ ≤ weakBranchSquaredGap gap
weakBranchSquaredNonnegative gap =
  let
    instance
      quarterIsNonnegative = nonNegative HL.quarterNonnegative
      powerIsNonnegative =
        nonNegative (Geo.powNonnegative HL.half gap HL.halfNonnegative)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          HL.quarter (Geo.pow HL.half gap)
  in
  ℚₚ.nonNegative⁻¹ (weakBranchSquaredGap gap)

strongBranchDominatedByWeak :
  (gap : Nat) →
  strongBranchSquaredGap gap ≤ weakBranchSquaredGap gap
strongBranchDominatedByWeak gap =
  L2.nonnegativeProductMonotone
    oneSixtyFourthNonnegative
    (Geo.powNonnegative oneEighth gap oneEighthNonnegative)
    HL.quarterNonnegative
    (Geo.powNonnegative HL.half gap HL.halfNonnegative)
    oneSixtyFourthBelowQuarter
    (powOneEighthBelowPowHalf gap)

twoBranchSquaredGap : Nat → ℚ
twoBranchSquaredGap gap =
  strongBranchSquaredGap gap + weakBranchSquaredGap gap

twoBranchDominatedByTwiceWeak :
  (gap : Nat) →
  twoBranchSquaredGap gap ≤ two * weakBranchSquaredGap gap
twoBranchDominatedByTwiceWeak gap =
  let
    summed :
      strongBranchSquaredGap gap + weakBranchSquaredGap gap
      ≤ weakBranchSquaredGap gap + weakBranchSquaredGap gap
    summed =
      ℚₚ.+-mono-≤
        (strongBranchDominatedByWeak gap)
        ℚₚ.≤-refl

    targetMeaning :
      weakBranchSquaredGap gap + weakBranchSquaredGap gap
      ≡ two * weakBranchSquaredGap gap
    targetMeaning = solve (weakBranchSquaredGap gap ∷ [])
  in
  subst
    (λ upper → twoBranchSquaredGap gap ≤ upper)
    targetMeaning
    summed

weakSquaredGapPrefix : Nat → ℚ
weakSquaredGapPrefix = HL.highLowRatioPrefix

weakSquaredGapPrefixBound :
  (cutoff : Nat) →
  weakSquaredGapPrefix cutoff ≤ HL.half
weakSquaredGapPrefixBound = HL.highLowRatioPrefixBound

four : ℚ
four = Int.+ 4 / 1

separationScale : Nat → ℚ
separationScale gap = four * Dyadic.dyadicScale gap

weakGapSeparationCalibration :
  (gap : Nat) →
  weakBranchSquaredGap gap * separationScale gap ≡ 1ℚ
weakGapSeparationCalibration zero = solve []
weakGapSeparationCalibration (suc gap) =
  begin
    weakBranchSquaredGap (suc gap) * separationScale (suc gap)
  ≡⟨ solve
       ( HL.quarter
       ∷ HL.half
       ∷ Geo.pow HL.half gap
       ∷ four
       ∷ Dyadic.two
       ∷ Dyadic.dyadicScale gap
       ∷ []) ⟩
    weakBranchSquaredGap gap * separationScale gap
  ≡⟨ weakGapSeparationCalibration gap ⟩
    1ℚ
  ∎

strongGapSuccessor :
  (gap : Nat) →
  strongBranchSquaredGap (suc gap)
  ≡ oneEighth * strongBranchSquaredGap gap
strongGapSuccessor gap =
  solve
    ( oneSixtyFourth
    ∷ oneEighth
    ∷ Geo.pow oneEighth gap
    ∷ [])

weakGapSuccessor :
  (gap : Nat) →
  weakBranchSquaredGap (suc gap)
  ≡ HL.half * weakBranchSquaredGap gap
weakGapSuccessor gap =
  solve
    ( HL.quarter
    ∷ HL.half
    ∷ Geo.pow HL.half gap
    ∷ [])

strongGapCubeOfWeak :
  (gap : Nat) →
  strongBranchSquaredGap gap
  ≡ weakBranchSquaredGap gap
      * weakBranchSquaredGap gap
      * weakBranchSquaredGap gap
strongGapCubeOfWeak zero = solve []
strongGapCubeOfWeak (suc gap) =
  begin
    strongBranchSquaredGap (suc gap)
  ≡⟨ strongGapSuccessor gap ⟩
    oneEighth * strongBranchSquaredGap gap
  ≡⟨ cong (oneEighth *_) (strongGapCubeOfWeak gap) ⟩
    oneEighth
      * (weakBranchSquaredGap gap
        * weakBranchSquaredGap gap
        * weakBranchSquaredGap gap)
  ≡⟨ solve
       ( oneEighth
       ∷ HL.half
       ∷ weakBranchSquaredGap gap
       ∷ []) ⟩
    (HL.half * weakBranchSquaredGap gap)
      * (HL.half * weakBranchSquaredGap gap)
      * (HL.half * weakBranchSquaredGap gap)
  ≡⟨ cong
       (λ current → current * current * current)
       (Eq.sym (weakGapSuccessor gap)) ⟩
    weakBranchSquaredGap (suc gap)
      * weakBranchSquaredGap (suc gap)
      * weakBranchSquaredGap (suc gap)
  ∎

strongGapCubicSeparationCalibration :
  (gap : Nat) →
  strongBranchSquaredGap gap
    * (separationScale gap
      * separationScale gap
      * separationScale gap)
  ≡ 1ℚ
strongGapCubicSeparationCalibration gap =
  begin
    strongBranchSquaredGap gap
      * (separationScale gap
        * separationScale gap
        * separationScale gap)
  ≡⟨ cong
       (λ strong →
         strong
         * (separationScale gap
           * separationScale gap
           * separationScale gap))
       (strongGapCubeOfWeak gap) ⟩
    (weakBranchSquaredGap gap
      * weakBranchSquaredGap gap
      * weakBranchSquaredGap gap)
      * (separationScale gap
        * separationScale gap
        * separationScale gap)
  ≡⟨ solve
       ( weakBranchSquaredGap gap
       ∷ separationScale gap
       ∷ []) ⟩
    (weakBranchSquaredGap gap * separationScale gap)
      * (weakBranchSquaredGap gap * separationScale gap)
      * (weakBranchSquaredGap gap * separationScale gap)
  ≡⟨ cong
       (λ current → current * current * current)
       (weakGapSeparationCalibration gap) ⟩
    1ℚ * 1ℚ * 1ℚ
  ≡⟨ solve [] ⟩
    1ℚ
  ∎
