module DASHI.Physics.Closure.NSTriadKNCherevanWindowScaleNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- PURPOSE
-- Separate the source's wave-packet window lambda^-1/2 from the parabolic
-- Navier--Stokes window lambda^-2.  They are not the same scaling after a
-- harmless change of notation.  At lambda=4:
--
--   lambda^-1/2 = 1/2,
--   lambda^-2   = 1/16,
--
-- so the former is eight parabolic windows long.  Over the wave-packet
-- window the heat exponent t lambda^2 equals 8, whereas it equals 1 on the
-- parabolic window.  A heat-to-wave argument must therefore prove a genuine
-- operator estimate; it cannot identify the two time geometries.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

lambda lambdaSquared : ℚ
lambda = Int.+ 4 / 1
lambdaSquared = lambda * lambda

wavePacketWindow parabolicWindow : ℚ
wavePacketWindow = Int.+ 1 / 2
parabolicWindow = Int.+ 1 / 16

parabolicWindowIsStrictlyShorter :
  parabolicWindow < wavePacketWindow
parabolicWindowIsStrictlyShorter =
  toWitness {a? = parabolicWindow ℚₚ.<? wavePacketWindow} _

waveWindowToParabolicRatio : ℚ
waveWindowToParabolicRatio =
  (Int.+ 8 / 1) * parabolicWindow

waveWindowIsEightParabolicWindows :
  wavePacketWindow ≡ waveWindowToParabolicRatio
waveWindowIsEightParabolicWindows = solve []

heatExponentOnWaveWindow heatExponentOnParabolicWindow : ℚ
heatExponentOnWaveWindow = wavePacketWindow * lambdaSquared
heatExponentOnParabolicWindow = parabolicWindow * lambdaSquared

waveWindowHeatExponentIsEight :
  heatExponentOnWaveWindow ≡ Int.+ 8 / 1
waveWindowHeatExponentIsEight = solve []

parabolicHeatExponentIsOne :
  heatExponentOnParabolicWindow ≡ Int.+ 1 / 1
parabolicHeatExponentIsOne = solve []
