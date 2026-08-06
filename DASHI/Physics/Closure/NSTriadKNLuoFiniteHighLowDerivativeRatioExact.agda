module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact where

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
-- Close the exact dyadic arithmetic in the high--low class.  When the low
-- shell is at least two steps below the comparable high/output shell, moving
-- the derivative onto the low input produces
--
--   lambda_r / lambda_p = 2^(-(p-r)).
--
-- Writing p-r = gap+2, the coefficient is
--
--   (1/4) (1/2)^gap,
--
-- and every finite prefix is bounded by 1/2.  This supplies the summable
-- shell coefficient required by HL2; the continuum product and time-pairing
-- estimates remain separate producer obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _-_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

half quarter two : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4
two = Int.+ 2 / 1

highLowDerivativeRatio : Nat → ℚ
highLowDerivativeRatio gap = quarter * Geo.pow half gap

highLowRatioPrefix : Nat → ℚ
highLowRatioPrefix cutoff =
  quarter * Geo.partialSum half cutoff

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

oneMinusHalfPositive : 0ℚ < 1ℚ - half
oneMinusHalfPositive =
  toWitness {a? = 0ℚ <? 1ℚ - half} _

twoIsGeometricEnvelope :
  (1ℚ - half) * two ≡ 1ℚ
twoIsGeometricEnvelope = solve []

unshiftedHalfPrefixBound :
  (cutoff : Nat) →
  Geo.partialSum half cutoff ≤ two
unshiftedHalfPrefixBound cutoff =
  Geo.geometricPartialSumBound
    half two cutoff
    halfNonnegative
    oneMinusHalfPositive
    twoIsGeometricEnvelope

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative = toWitness {a? = 0ℚ ≤? quarter} _

highLowRatioPrefixBound :
  (cutoff : Nat) →
  highLowRatioPrefix cutoff ≤ half
highLowRatioPrefixBound cutoff =
  let
    scaled :
      quarter * Geo.partialSum half cutoff ≤ quarter * two
    scaled =
      let
        instance
          quarterIsNonnegative = nonNegative quarterNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        quarter
        (unshiftedHalfPrefixBound cutoff)

    endpointMeaning : quarter * two ≡ half
    endpointMeaning = solve []
  in
  subst
    (λ upper → highLowRatioPrefix cutoff ≤ upper)
    endpointMeaning
    scaled
