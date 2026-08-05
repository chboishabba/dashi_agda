module DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalInteractionKernelExact where

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
-- Implement the finite summability of the shell-resolved critical kernel.
-- The original generic three-sector kernel has:
--
-- * a quarter-geometric low-shell component;
-- * five comparable shells;
-- * a half-geometric high-shell component;
--
-- and is bounded by 25/3.  Round thirteen identified that this generic low
-- component alone does not dominate the high--low derivative-transfer weight
-- (1/4)(1/2)^gap.  The integrated safe kernel therefore retains both low
-- mechanisms.  Its low prefix is bounded by 11/6, and the complete safe
-- low/comparable/high prefix by
--
--   11/6 + 5 + 2 = 53/6.
--
-- Both the legacy generic theorem and the corrected high--low-safe theorem
-- remain named below so downstream code must choose its intended scope.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL

five twentyFiveThirds elevenSixths fiftyThreeSixths : ℚ
five = Int.+ 5 / 1
twentyFiveThirds = Int.+ 25 / 3
elevenSixths = Int.+ 11 / 6
fiftyThreeSixths = Int.+ 53 / 6

-- Legacy generic low-shell component.  It remains useful for the original
-- quarter-decay lane, but is not by itself a high--low envelope.
lowKernelPrefix : Nat → ℚ
lowKernelPrefix cutoff = Geo.partialSum Geo.quarter cutoff

highKernelPrefix : Nat → ℚ
highKernelPrefix = HH.highHighLowGainPrefix

criticalKernelPrefix : Nat → Nat → ℚ
criticalKernelPrefix lowCutoff highCutoff =
  lowKernelPrefix lowCutoff + five + highKernelPrefix highCutoff

fiveReflexive : five ≤ five
fiveReflexive = toWitness {a? = five ≤? five} _

criticalKernelPrefixBound :
  (lowCutoff highCutoff : Nat) →
  criticalKernelPrefix lowCutoff highCutoff ≤ twentyFiveThirds
criticalKernelPrefixBound lowCutoff highCutoff =
  let
    lowAndComparable :
      lowKernelPrefix lowCutoff + five
      ≤ Geo.fourThirds + five
    lowAndComparable =
      ℚₚ.+-mono-≤
        (Geo.quarterPartialSumBound lowCutoff)
        fiveReflexive

    assembled :
      lowKernelPrefix lowCutoff + five + highKernelPrefix highCutoff
      ≤ Geo.fourThirds + five + HH.two
    assembled =
      ℚₚ.+-mono-≤
        lowAndComparable
        (HH.highHighLowGainPrefixBound highCutoff)

    targetMeaning :
      Geo.fourThirds + five + HH.two ≡ twentyFiveThirds
    targetMeaning = solve []
  in
  subst
    (λ upper → criticalKernelPrefix lowCutoff highCutoff ≤ upper)
    targetMeaning
    assembled

-- Corrected low-shell prefix.  The first term covers the quarter-geometric
-- mechanism and the second the shifted high--low derivative coefficient.
highLowSafeLowKernelPrefix : Nat → ℚ
highLowSafeLowKernelPrefix cutoff =
  lowKernelPrefix cutoff + HL.highLowRatioPrefix cutoff

highLowSafeLowKernelPrefixBound :
  (cutoff : Nat) →
  highLowSafeLowKernelPrefix cutoff ≤ elevenSixths
highLowSafeLowKernelPrefixBound cutoff =
  let
    assembled :
      lowKernelPrefix cutoff + HL.highLowRatioPrefix cutoff
      ≤ Geo.fourThirds + HL.half
    assembled =
      ℚₚ.+-mono-≤
        (Geo.quarterPartialSumBound cutoff)
        (HL.highLowRatioPrefixBound cutoff)

    targetMeaning :
      Geo.fourThirds + HL.half ≡ elevenSixths
    targetMeaning = solve []
  in
  subst
    (λ upper → highLowSafeLowKernelPrefix cutoff ≤ upper)
    targetMeaning
    assembled

highLowSafeCriticalKernelPrefix : Nat → Nat → ℚ
highLowSafeCriticalKernelPrefix lowCutoff highCutoff =
  highLowSafeLowKernelPrefix lowCutoff
  + five
  + highKernelPrefix highCutoff

highLowSafeCriticalKernelPrefixBound :
  (lowCutoff highCutoff : Nat) →
  highLowSafeCriticalKernelPrefix lowCutoff highCutoff ≤ fiftyThreeSixths
highLowSafeCriticalKernelPrefixBound lowCutoff highCutoff =
  let
    lowAndComparable :
      highLowSafeLowKernelPrefix lowCutoff + five
      ≤ elevenSixths + five
    lowAndComparable =
      ℚₚ.+-mono-≤
        (highLowSafeLowKernelPrefixBound lowCutoff)
        fiveReflexive

    assembled :
      highLowSafeLowKernelPrefix lowCutoff
        + five
        + highKernelPrefix highCutoff
      ≤ elevenSixths + five + HH.two
    assembled =
      ℚₚ.+-mono-≤
        lowAndComparable
        (HH.highHighLowGainPrefixBound highCutoff)

    targetMeaning :
      elevenSixths + five + HH.two ≡ fiftyThreeSixths
    targetMeaning = solve []
  in
  subst
    (λ upper →
      highLowSafeCriticalKernelPrefix lowCutoff highCutoff ≤ upper)
    targetMeaning
    assembled
