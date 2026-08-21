module DASHI.Physics.Closure.NSAncientExpandingTorusIncrementDensityRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Theodore von Karman; Leslie Howarth.
-- Title: "On the Statistical Theory of Isotropic Turbulence".
-- Proceedings of the Royal Society A 164 (1938), 192--215.
-- DOI: 10.1098/rspa.1938.0013.
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- Acta Mathematica 203 (2009), 83--105.
-- DOI: 10.1007/s11511-009-0039-6.
--
-- ROUND66 / PERIODIC ANCESTRY OF THE SECOND-ORDER INCREMENT DEFECT
--
-- Round65 proved that under the KNSŠ blow-up the mean-square velocity density
-- over the expanding period cell scales like M^(-2).  Translation invariance
-- of a full periodic cell then forces the cell-averaged second-order increment
-- defect to dilute at the same rate.
--
-- The pointwise algebra is
--
--   (a-b)^2 <= 2 a^2 + 2 b^2,
--
-- because the gap is (a+b)^2.  After averaging over a full period cell, the
-- shifted b-energy equals the unshifted a-energy, so
--
--   mean |u(x+h)-u(x)|^2 <= 4 mean |u(x)|^2.
--
-- This file proves the exact ordered-rational core and the translation-
-- invariant ledger consequence.  Combined with Round65's M^(-2) density
-- factor, every fixed-separation cell-averaged structure defect vanishes in
-- the expanding-torus sequence even though a local nonconstant plateau may
-- survive.  Thus a putative ancient singular profile must live on an
-- asymptotically zero-density exceptional region.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

square : ℚ → ℚ
square x = x * x

pointwiseIncrementSquareBound :
  (a b : ℚ) →
  square (a - b) ≤ (1ℚ + 1ℚ) * square a + (1ℚ + 1ℚ) * square b
pointwiseIncrementSquareBound a b =
  let
    gapNN : 0ℚ ≤ square (a + b)
    gapNN = Order.squareNonnegative (a + b)

    baseBelowBasePlusGap :
      square (a - b)
      ≤ square (a - b) + square (a + b)
    baseBelowBasePlusGap =
      subst
        (λ left → left ≤ square (a - b) + square (a + b))
        (ℚP.+-identityʳ (square (a - b)))
        (ℚP.+-mono-≤ (ℚP.≤-refl) gapNN)
  in
  subst
    (λ upper → square (a - b) ≤ upper)
    (solve (a ∷ b ∷ []))
    baseBelowBasePlusGap

record TranslationInvariantIncrementLedger : Set where
  constructor increment-density-ledger
  field
    originalMeanSquare : ℚ
    shiftedMeanSquare : ℚ
    incrementMeanSquare : ℚ

    pointwiseIntegratedBound :
      incrementMeanSquare
      ≤ (1ℚ + 1ℚ) * originalMeanSquare
        + (1ℚ + 1ℚ) * shiftedMeanSquare

    fullCellShiftInvariance : shiftedMeanSquare ≡ originalMeanSquare

open TranslationInvariantIncrementLedger public

periodicIncrementMeanSquareAtMostFourEnergyDensity :
  (L : TranslationInvariantIncrementLedger) →
  incrementMeanSquare L
    ≤ ((1ℚ + 1ℚ) + (1ℚ + 1ℚ)) * originalMeanSquare L
periodicIncrementMeanSquareAtMostFourEnergyDensity L =
  subst
    (λ shifted →
      incrementMeanSquare L
      ≤ (1ℚ + 1ℚ) * originalMeanSquare L
        + (1ℚ + 1ℚ) * shifted)
    (fullCellShiftInvariance L)
    (subst
      (λ upper → incrementMeanSquare L ≤ upper)
      (solve (originalMeanSquare L ∷ []))
      (pointwiseIntegratedBound L))
