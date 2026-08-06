module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowKernelAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Bahouri--Chemin--Danchin title:
-- "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Audit the low-shell kernel used by the critical four-class functional.
-- The high--low derivative transfer produces
--
--   (1/4) (1/2)^gap,
--
-- whereas the old generic low kernel is (1/4)^gap.  The old kernel does not
-- dominate the high--low coefficient for all gaps: at gap=3 it is 1/64 while
-- the derivative coefficient is 1/32.
--
-- The corrected safe envelope retains both low-shell mechanisms.  Its finite
-- prefix is bounded by
--
--   4/3 + 1/2 = 11/6,
--
-- and the complete low/comparable/high kernel by
--
--   11/6 + 5 + 2 = 53/6.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _<_; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalInteractionKernelExact as Critical
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HH

oneSixtyFourth oneThirtySecond elevenSixths fiftyThreeSixths : ℚ
oneSixtyFourth = Int.+ 1 / 64
oneThirtySecond = Int.+ 1 / 32
elevenSixths = Int.+ 11 / 6
fiftyThreeSixths = Int.+ 53 / 6

oldLowKernelWeight : Nat → ℚ
oldLowKernelWeight gap = Geo.pow Geo.quarter gap

highLowDerivativeWeight : Nat → ℚ
highLowDerivativeWeight = HL.highLowDerivativeRatio

oldGapThreeValue :
  oldLowKernelWeight 3 ≡ oneSixtyFourth
oldGapThreeValue = solve []

highLowGapThreeValue :
  highLowDerivativeWeight 3 ≡ oneThirtySecond
highLowGapThreeValue = solve []

oneSixtyFourthBelowOneThirtySecond :
  oneSixtyFourth < oneThirtySecond
oneSixtyFourthBelowOneThirtySecond =
  toWitness {a? = oneSixtyFourth <? oneThirtySecond} _

oldLowKernelFailsToDominateHighLowAtGapThree :
  oldLowKernelWeight 3 < highLowDerivativeWeight 3
oldLowKernelFailsToDominateHighLowAtGapThree =
  subst
    (λ oldValue → oldValue < highLowDerivativeWeight 3)
    oldGapThreeValue
    (subst
      (λ highValue → oneSixtyFourth < highValue)
      highLowGapThreeValue
      oneSixtyFourthBelowOneThirtySecond)

correctedLowKernelPrefix : Nat → ℚ
correctedLowKernelPrefix cutoff =
  Geo.partialSum Geo.quarter cutoff + HL.highLowRatioPrefix cutoff

correctedLowKernelPrefixBound :
  (cutoff : Nat) →
  correctedLowKernelPrefix cutoff ≤ elevenSixths
correctedLowKernelPrefixBound cutoff =
  let
    summed :
      Geo.partialSum Geo.quarter cutoff + HL.highLowRatioPrefix cutoff
      ≤ Geo.fourThirds + HL.half
    summed =
      ℚₚ.+-mono-≤
        (Geo.quarterPartialSumBound cutoff)
        (HL.highLowRatioPrefixBound cutoff)

    targetMeaning :
      Geo.fourThirds + HL.half ≡ elevenSixths
    targetMeaning = solve []
  in
  subst
    (λ upper → correctedLowKernelPrefix cutoff ≤ upper)
    targetMeaning
    summed

correctedCriticalKernelPrefix : Nat → Nat → ℚ
correctedCriticalKernelPrefix lowCutoff highCutoff =
  correctedLowKernelPrefix lowCutoff
  + Critical.five
  + HH.highHighLowGainPrefix highCutoff

correctedCriticalKernelPrefixBound :
  (lowCutoff highCutoff : Nat) →
  correctedCriticalKernelPrefix lowCutoff highCutoff ≤ fiftyThreeSixths
correctedCriticalKernelPrefixBound lowCutoff highCutoff =
  let
    lowAndComparable :
      correctedLowKernelPrefix lowCutoff + Critical.five
      ≤ elevenSixths + Critical.five
    lowAndComparable =
      ℚₚ.+-mono-≤
        (correctedLowKernelPrefixBound lowCutoff)
        ℚₚ.≤-refl

    assembled :
      correctedLowKernelPrefix lowCutoff
        + Critical.five
        + HH.highHighLowGainPrefix highCutoff
      ≤ elevenSixths + Critical.five + HH.two
    assembled =
      ℚₚ.+-mono-≤
        lowAndComparable
        (HH.highHighLowGainPrefixBound highCutoff)

    targetMeaning :
      elevenSixths + Critical.five + HH.two ≡ fiftyThreeSixths
    targetMeaning = solve []
  in
  subst
    (λ upper →
      correctedCriticalKernelPrefix lowCutoff highCutoff ≤ upper)
    targetMeaning
    assembled
