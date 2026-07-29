module DASHI.Physics.Closure.NSTriadKNMurrayBishopSobolevElevenFourths where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Agda
-- standard-library contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "Fourier Analysis and Nonlinear Partial Differential
-- Equations"; and "Murray--Bishop s = 11/4 Sobolev instance".
-- Venue/year: Springer, 1985 and 2011; Dalhousie University/arXiv, 2022; Agda
-- standard library; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1007/978-3-642-16830-7; the repository instance has no DOI.
-- Source pin: viktorcsimma/bishop commit
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
-- Uses: the exact normalized rational order and its transport into Murray's
-- regular-sequence reals.
-- Relationship: supplies an actual backend value s = 11/4 with
-- 5/2 < s < 3.  Rational normalization also closes the corresponding decay
-- identities 2s-5/2 = 3 and 2s = 11/2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base as Rational
  using (ℚ; 1ℚ; _/_; _+_; _-_; _<_; toℚᵘ)
import Data.Rational.Properties as RationalLaws
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Unit.Base using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness)

import Real as Bishop
import RealProperties as BishopLaws

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier

twoRational threeRational fiveRational : ℚ
twoRational = 1ℚ + 1ℚ
threeRational = twoRational + 1ℚ
fiveRational = (twoRational + twoRational) + 1ℚ

fiveHalves elevenFourths elevenHalves : ℚ
fiveHalves = Int.+ 5 / 2
elevenFourths = Int.+ 11 / 4
elevenHalves = Int.+ 11 / 2

fiveHalvesBelowElevenFourths : fiveHalves < elevenFourths
fiveHalvesBelowElevenFourths =
  toWitness
    {a? = RationalLaws._<?_ fiveHalves elevenFourths}
    tt

elevenFourthsBelowThree : elevenFourths < threeRational
elevenFourthsBelowThree =
  toWitness
    {a? = RationalLaws._<?_ elevenFourths threeRational}
    tt

murrayBishopSobolevExponent : Bishop.ℝ
murrayBishopSobolevExponent =
  Carrier.bishopRationalEmbed elevenFourths

murrayBishopFiveHalvesBelowSobolev :
  Bishop._<_
    (Carrier.bishopRationalEmbed fiveHalves)
    murrayBishopSobolevExponent
murrayBishopFiveHalvesBelowSobolev =
  BishopLaws.p<q⇒p⋆<q⋆
    (toℚᵘ fiveHalves)
    (toℚᵘ elevenFourths)
    (RationalLaws.toℚᵘ-mono-< fiveHalvesBelowElevenFourths)

murrayBishopSobolevBelowThree :
  Bishop._<_
    murrayBishopSobolevExponent
    (Carrier.bishopRationalEmbed threeRational)
murrayBishopSobolevBelowThree =
  BishopLaws.p<q⇒p⋆<q⋆
    (toℚᵘ elevenFourths)
    (toℚᵘ threeRational)
    (RationalLaws.toℚᵘ-mono-< elevenFourthsBelowThree)

lowDecayRational : ℚ
lowDecayRational =
  (elevenFourths + elevenFourths) - fiveHalves

gapDecayRational : ℚ
gapDecayRational = elevenFourths + elevenFourths

lowDecayIsThree : lowDecayRational ≡ threeRational
lowDecayIsThree = solve []

gapDecayIsElevenHalves : gapDecayRational ≡ elevenHalves
gapDecayIsElevenHalves = solve []

record MurrayBishopSobolevElevenFourthsInstance : Set where
  field
    sobolevExponent : Bishop.ℝ
    aboveFiveHalves :
      Bishop._<_
        (Carrier.bishopRationalEmbed fiveHalves)
        sobolevExponent
    belowThree :
      Bishop._<_
        sobolevExponent
        (Carrier.bishopRationalEmbed threeRational)
    lowDecayExact : lowDecayRational ≡ threeRational
    gapDecayExact : gapDecayRational ≡ elevenHalves

open MurrayBishopSobolevElevenFourthsInstance public

murrayBishopSobolevElevenFourthsInstance :
  MurrayBishopSobolevElevenFourthsInstance
murrayBishopSobolevElevenFourthsInstance = record
  { sobolevExponent = murrayBishopSobolevExponent
  ; aboveFiveHalves = murrayBishopFiveHalvesBelowSobolev
  ; belowThree = murrayBishopSobolevBelowThree
  ; lowDecayExact = lowDecayIsThree
  ; gapDecayExact = gapDecayIsElevenHalves
  }

murrayBishopConcreteSobolevIntervalClosed : Bool
murrayBishopConcreteSobolevIntervalClosed = true

murrayBishopConcreteDecayArithmeticClosed : Bool
murrayBishopConcreteDecayArithmeticClosed = true

murrayBishopConcreteSobolevIntervalClosedIsTrue :
  murrayBishopConcreteSobolevIntervalClosed ≡ true
murrayBishopConcreteSobolevIntervalClosedIsTrue = refl

murrayBishopConcreteDecayArithmeticClosedIsTrue :
  murrayBishopConcreteDecayArithmeticClosed ≡ true
murrayBishopConcreteDecayArithmeticClosedIsTrue = refl
