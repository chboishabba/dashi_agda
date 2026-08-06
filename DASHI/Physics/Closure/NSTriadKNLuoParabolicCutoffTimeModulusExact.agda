module DASHI.Physics.Closure.NSTriadKNLuoParabolicCutoffTimeModulusExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Mathematical ingredient: effective joint convergence on a parabolic
-- cutoff/time diagonal.  This repository-original exact theorem has no DOI.
--
-- PURPOSE
-- Replace independent pointwise limits by a computable joint schedule.  If
-- the cutoff error is bounded by 2^{-q} and the terminal-time error by 4^{-n},
-- then choosing q=2n gives
--
--   error(2n,n) <= 2 * 4^{-n}.
--
-- Thus the shell cutoff and approach to the maximal time are coupled at the
-- parabolic rate.  The continuum Navier--Stokes producer must instantiate the
-- error and prove the two component bounds; the diagonal argument itself is
-- closed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat

half : ℚ
half = Int.+ 1 / 2

quarter : ℚ
quarter = Int.+ 1 / 4

two : ℚ
two = Int.+ 2 / 1

record ParabolicCutoffTimeError : Set₁ where
  field
    error : Nat → Nat → ℚ
    separatedBound :
      (cutoff terminalIndex : Nat) →
      error cutoff terminalIndex
      ≤ Geo.pow half cutoff + Geo.pow quarter terminalIndex

open ParabolicCutoffTimeError public

doubleIndex : Nat → Nat
doubleIndex index = index + index

halfPowerSquaredIsQuarterPower :
  (index : Nat) →
  Geo.pow half index * Geo.pow half index
  ≡ Geo.pow quarter index
halfPowerSquaredIsQuarterPower zero = solve []
halfPowerSquaredIsQuarterPower (suc index)
  rewrite halfPowerSquaredIsQuarterPower index =
  solve
    ( Geo.pow half index
    ∷ Geo.pow quarter index
    ∷ [])

halfDoubleIsQuarter :
  (index : Nat) →
  Geo.pow half (doubleIndex index) ≡ Geo.pow quarter index
halfDoubleIsQuarter index =
  trans
    (Heat.powAdd half index index)
    (halfPowerSquaredIsQuarterPower index)

parabolicDiagonalModulus :
  (dataSet : ParabolicCutoffTimeError) →
  (index : Nat) →
  error dataSet (doubleIndex index) index
  ≤ two * Geo.pow quarter index
parabolicDiagonalModulus dataSet index =
  subst
    (λ upper →
      error dataSet (doubleIndex index) index ≤ upper)
    targetMeaning
    (separatedBound dataSet (doubleIndex index) index)
  where
  targetMeaning :
    Geo.pow half (doubleIndex index) + Geo.pow quarter index
    ≡ two * Geo.pow quarter index
  targetMeaning
    rewrite halfDoubleIsQuarter index =
    solve (Geo.pow quarter index ∷ [])

nextParabolicDiagonalModulus :
  (dataSet : ParabolicCutoffTimeError) →
  (index : Nat) →
  error dataSet (doubleIndex (suc index)) (suc index)
  ≤ half * Geo.pow quarter index
nextParabolicDiagonalModulus dataSet index =
  subst
    (λ upper →
      error dataSet (doubleIndex (suc index)) (suc index) ≤ upper)
    (solve (Geo.pow quarter index ∷ []))
    (parabolicDiagonalModulus dataSet (suc index))
