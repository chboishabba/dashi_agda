module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointHeatSemigroupExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Audrey Terras.
-- Title: "Fourier Analysis on Finite Groups and Applications".
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Put a genuine spectral heat semigroup on the exact eight-point torus.  The
-- zero mode is undamped.  Modes of Hamming weight one, two and three receive
-- one-step factors 1/2, 1/4 and 1/8.  The semigroup law is derived, and every
-- nonzero mode is bounded by the common high-frequency factor (1/2)^n.
--
-- This gives a concrete periodic finite-quotient heat model connected to the
-- normalized Haar carrier.  The continuum torus estimate with the
-- tau^{-2} prefactor remains a separate analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointTorusHaarExact as Torus
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat
import DASHI.Physics.Closure.NSTriadKNLuoFiniteArbitraryPolynomialAbsorptionExact as Power
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

oneEighth : ℚ
oneEighth = Int.+ 1 / 8

modeBase : Torus.BitTorus3 → ℚ
modeBase (Torus.bit3 false false false) = Int.+ 1 / 1
modeBase (Torus.bit3 false false true) = Heat.half
modeBase (Torus.bit3 false true false) = Heat.half
modeBase (Torus.bit3 true false false) = Heat.half
modeBase (Torus.bit3 false true true) = Geo.quarter
modeBase (Torus.bit3 true false true) = Geo.quarter
modeBase (Torus.bit3 true true false) = Geo.quarter
modeBase (Torus.bit3 true true true) = oneEighth

heatMultiplier : Torus.BitTorus3 → Nat → ℚ
heatMultiplier mode time = Geo.pow (modeBase mode) time

heatMultiplierSemigroup :
  (mode : Torus.BitTorus3) →
  (oldSteps newSteps : Nat) →
  heatMultiplier mode (oldSteps + newSteps)
  ≡ heatMultiplier mode oldSteps * heatMultiplier mode newSteps
heatMultiplierSemigroup mode = Heat.powAdd (modeBase mode)

data NonzeroMode : Torus.BitTorus3 → Set where
  nz001 : NonzeroMode Torus.p001
  nz010 : NonzeroMode Torus.p010
  nz011 : NonzeroMode Torus.p011
  nz100 : NonzeroMode Torus.p100
  nz101 : NonzeroMode Torus.p101
  nz110 : NonzeroMode Torus.p110
  nz111 : NonzeroMode Torus.p111

modeBaseNonnegative :
  (mode : Torus.BitTorus3) →
  0ℚ ≤ modeBase mode
modeBaseNonnegative (Torus.bit3 false false false) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p000} _
modeBaseNonnegative (Torus.bit3 false false true) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p001} _
modeBaseNonnegative (Torus.bit3 false true false) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p010} _
modeBaseNonnegative (Torus.bit3 false true true) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p011} _
modeBaseNonnegative (Torus.bit3 true false false) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p100} _
modeBaseNonnegative (Torus.bit3 true false true) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p101} _
modeBaseNonnegative (Torus.bit3 true true false) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p110} _
modeBaseNonnegative (Torus.bit3 true true true) =
  toWitness {a? = 0ℚ ≤? modeBase Torus.p111} _

modeBaseBelowHalf :
  ∀ {mode} →
  NonzeroMode mode →
  modeBase mode ≤ Heat.half
modeBaseBelowHalf nz001 = ℚₚ.≤-refl
modeBaseBelowHalf nz010 = ℚₚ.≤-refl
modeBaseBelowHalf nz100 = ℚₚ.≤-refl
modeBaseBelowHalf nz011 =
  toWitness {a? = Geo.quarter ≤? Heat.half} _
modeBaseBelowHalf nz101 =
  toWitness {a? = Geo.quarter ≤? Heat.half} _
modeBaseBelowHalf nz110 =
  toWitness {a? = Geo.quarter ≤? Heat.half} _
modeBaseBelowHalf nz111 =
  toWitness {a? = oneEighth ≤? Heat.half} _

nonzeroHeatDampingBound :
  ∀ {mode} →
  NonzeroMode mode →
  (time : Nat) →
  heatMultiplier mode time ≤ Heat.heatDamping time
nonzeroHeatDampingBound {mode} nonzero time =
  Power.powerMonotone
    (modeBase mode)
    Heat.half
    (modeBaseNonnegative mode)
    (toWitness {a? = 0ℚ ≤? Heat.half} _)
    (modeBaseBelowHalf nonzero)
    time
