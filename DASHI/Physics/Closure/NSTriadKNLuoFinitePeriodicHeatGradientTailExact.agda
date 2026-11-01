module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicHeatGradientTailExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Prove the exact dyadic shell arithmetic behind the periodic high-frequency
-- heat-gradient estimate.  At one parabolic time unit for the cutoff q, an
-- offset shell q+n pays
--
--   lambda_{q+n} 4^{-n} = lambda_q 2^{-n}.
--
-- Hence every finite high-frequency shell prefix is bounded by
--
--   sum_{n=0}^N lambda_{q+n} 4^{-n} <= 2 lambda_q.
--
-- This is the concrete shell-count/damping component of the desired
-- L1-to-L-infinity estimate.  The continuum theorem must additionally identify
-- Fourier coefficients with normalized T^3 Haar integration, supply the
-- lattice multiplicity/three-dimensional derivative factor tau^{-2}, and
-- replace this parabolic-unit dyadic model by exp(-c tau lambda_q^2).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale

half : ℚ
half = Int.+ 1 / 2

two : ℚ
two = Int.+ 2 / 1

quarter : ℚ
quarter = Int.+ 1 / 4

powProductCollapse :
  (offset : Nat) →
  Geo.pow two offset * Geo.pow quarter offset
  ≡ Geo.pow half offset
powProductCollapse zero = solve []
powProductCollapse (suc offset)
  rewrite powProductCollapse offset =
  solve
    ( Geo.pow two offset
    ∷ Geo.pow quarter offset
    ∷ Geo.pow half offset
    ∷ [])

shellGradientHeatWeight : Nat → Nat → ℚ
shellGradientHeatWeight cutoff offset =
  Scale.dyadicScale (cutoff + offset) * Geo.pow quarter offset

shellGradientHeatWeightMeaning :
  (cutoff offset : Nat) →
  shellGradientHeatWeight cutoff offset
  ≡ Scale.dyadicScale cutoff * Geo.pow half offset
shellGradientHeatWeightMeaning cutoff offset =
  trans
    (cong
      (_* Geo.pow quarter offset)
      (Heat.powAdd two cutoff offset))
    (trans
      (solve
        ( Scale.dyadicScale cutoff
        ∷ Geo.pow two offset
        ∷ Geo.pow quarter offset
        ∷ []
        ))
      (cong
        (Scale.dyadicScale cutoff *_)
        (powProductCollapse offset)))

finiteGradientHeatTail : Nat → Nat → ℚ
finiteGradientHeatTail cutoff zero =
  shellGradientHeatWeight cutoff zero
finiteGradientHeatTail cutoff (suc terminalOffset) =
  shellGradientHeatWeight cutoff (suc terminalOffset)
  + finiteGradientHeatTail cutoff terminalOffset

finiteGradientHeatTailMeaning :
  (cutoff terminalOffset : Nat) →
  finiteGradientHeatTail cutoff terminalOffset
  ≡ Scale.dyadicScale cutoff * Geo.partialSum half terminalOffset
finiteGradientHeatTailMeaning cutoff zero
  rewrite shellGradientHeatWeightMeaning cutoff zero =
  solve (Scale.dyadicScale cutoff ∷ [])
finiteGradientHeatTailMeaning cutoff (suc terminalOffset)
  rewrite shellGradientHeatWeightMeaning cutoff (suc terminalOffset)
        | finiteGradientHeatTailMeaning cutoff terminalOffset =
  solve
    ( Scale.dyadicScale cutoff
    ∷ Geo.pow half (suc terminalOffset)
    ∷ Geo.partialSum half terminalOffset
    ∷ [])

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

oneMinusHalfPositive : 0ℚ < 1ℚ - half
oneMinusHalfPositive = toWitness {a? = 0ℚ <? 1ℚ - half} _

halfBoundIdentity :
  (1ℚ - half) * two ≡ 1ℚ
halfBoundIdentity = refl

halfPartialSumBound :
  (terminalOffset : Nat) →
  Geo.partialSum half terminalOffset ≤ two
halfPartialSumBound terminalOffset =
  Geo.geometricPartialSumBound
    half two terminalOffset
    halfNonnegative oneMinusHalfPositive halfBoundIdentity

dyadicScaleNonnegative :
  (cutoff : Nat) →
  0ℚ ≤ Scale.dyadicScale cutoff
dyadicScaleNonnegative cutoff =
  Geo.powNonnegative two cutoff
    (toWitness {a? = 0ℚ ≤? two} _)

finiteGradientHeatTailBound :
  (cutoff terminalOffset : Nat) →
  finiteGradientHeatTail cutoff terminalOffset
  ≤ two * Scale.dyadicScale cutoff
finiteGradientHeatTailBound cutoff terminalOffset =
  subst
    (λ lower → lower ≤ two * Scale.dyadicScale cutoff)
    (sym (finiteGradientHeatTailMeaning cutoff terminalOffset))
    (subst
      (λ upper →
        Scale.dyadicScale cutoff
          * Geo.partialSum half terminalOffset
        ≤ upper)
      (solve (Scale.dyadicScale cutoff ∷ []))
      scaled)
  where
  scaled :
    Scale.dyadicScale cutoff * Geo.partialSum half terminalOffset
    ≤ Scale.dyadicScale cutoff * two
  scaled =
    let
      instance
        cutoffNonnegative =
          nonNegative (dyadicScaleNonnegative cutoff)
    in
    ℚₚ.*-monoˡ-≤-nonNeg
      (Scale.dyadicScale cutoff)
      (halfPartialSumBound terminalOffset)
