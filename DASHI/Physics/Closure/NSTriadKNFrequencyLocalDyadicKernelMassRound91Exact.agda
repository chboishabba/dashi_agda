module DASHI.Physics.Closure.NSTriadKNFrequencyLocalDyadicKernelMassRound91Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- In the proof of the frequency-local nonlinear estimate, I, II and III are
-- reduced after cubic reweighting to geometric gap kernels with exponents
--
--   2(1-epsilon)/3,  2(2+epsilon)/3,  (1-epsilon)/3.
--
-- ROUND91 / EXACT RATIONAL SUBCRITICAL CALIBRATION
--
-- Choose one admissible subcritical exponent indirectly by fixing
--
--   rho = 2^{-(1-epsilon)/3} = 4/5.
--
-- This corresponds to a unique epsilon in (0,1), because
-- 2^{-1/3} < 4/5 < 1.  The formal shell arithmetic itself needs only rho.
-- The three gap ratios are then
--
--   I   : rho^2          = 16/25,
--   II  : 1/(4 rho^2)   = 25/64,
--   III : rho            = 4/5.
--
-- Their finite geometric masses obey, uniformly in cutoff,
--
--   sum (16/25)^d <= 25/9,
--   sum (25/64)^d <= 64/39,
--   sum (4/5)^d   <= 5.
--
-- The III ledger includes at most one p=q+1 neighbour.  Its weight is
-- rho^{-1}=5/4, hence the full near-plus-low III row mass is <=25/4.
-- No continuum theorem, critical smallness, or viscosity assumption occurs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

rho iRatio iiRatio iiiRatio iiiNear
  iMass iiMass iiiMass iiiFullMass : ℚ
rho = Int.+ 4 / 5
iRatio = Int.+ 16 / 25
iiRatio = Int.+ 25 / 64
iiiRatio = rho
iiiNear = Int.+ 5 / 4
iMass = Int.+ 25 / 9
iiMass = Int.+ 64 / 39
iiiMass = Int.+ 5 / 1
iiiFullMass = Int.+ 25 / 4

iRatioMeaning : iRatio ≡ rho * rho
iRatioMeaning = refl

iiRatioMeaning : (Int.+ 4 / 1) * (rho * rho) * iiRatio ≡ 1ℚ
iiRatioMeaning = refl

iiiRatioMeaning : iiiRatio ≡ rho
iiiRatioMeaning = refl

iiiNearReciprocalMeaning : rho * iiiNear ≡ 1ℚ
iiiNearReciprocalMeaning = refl

rhoNonnegative : 0ℚ ≤ rho
rhoNonnegative = toWitness {a? = 0ℚ ≤? rho} _
iRatioNonnegative : 0ℚ ≤ iRatio
iRatioNonnegative = toWitness {a? = 0ℚ ≤? iRatio} _
iiRatioNonnegative : 0ℚ ≤ iiRatio
iiRatioNonnegative = toWitness {a? = 0ℚ ≤? iiRatio} _
iiiRatioNonnegative : 0ℚ ≤ iiiRatio
iiiRatioNonnegative = rhoNonnegative

oneMinusIPositive : 0ℚ < 1ℚ - iRatio
oneMinusIPositive = toWitness {a? = 0ℚ <? (1ℚ - iRatio)} _
oneMinusIIPositive : 0ℚ < 1ℚ - iiRatio
oneMinusIIPositive = toWitness {a? = 0ℚ <? (1ℚ - iiRatio)} _
oneMinusIIIPositive : 0ℚ < 1ℚ - iiiRatio
oneMinusIIIPositive = toWitness {a? = 0ℚ <? (1ℚ - iiiRatio)} _

iMassIdentity : (1ℚ - iRatio) * iMass ≡ 1ℚ
iMassIdentity = refl

iiMassIdentity : (1ℚ - iiRatio) * iiMass ≡ 1ℚ
iiMassIdentity = refl

iiiMassIdentity : (1ℚ - iiiRatio) * iiiMass ≡ 1ℚ
iiiMassIdentity = refl

iKernelMassBound : ∀ cutoff → Geo.partialSum iRatio cutoff ≤ iMass
iKernelMassBound cutoff =
  Geo.geometricPartialSumBound
    iRatio iMass cutoff
    iRatioNonnegative oneMinusIPositive iMassIdentity

iiKernelMassBound : ∀ cutoff → Geo.partialSum iiRatio cutoff ≤ iiMass
iiKernelMassBound cutoff =
  Geo.geometricPartialSumBound
    iiRatio iiMass cutoff
    iiRatioNonnegative oneMinusIIPositive iiMassIdentity

iiiKernelMassBound : ∀ cutoff → Geo.partialSum iiiRatio cutoff ≤ iiiMass
iiiKernelMassBound cutoff =
  Geo.geometricPartialSumBound
    iiiRatio iiiMass cutoff
    iiiRatioNonnegative oneMinusIIIPositive iiiMassIdentity

iiiNearPlusKernelMassBound : ∀ cutoff →
  iiiNear + Geo.partialSum iiiRatio cutoff ≤ iiiFullMass
iiiNearPlusKernelMassBound cutoff =
  let
    raw = ℚP.+-monoʳ-≤ iiiNear (iiiKernelMassBound cutoff)
    endpoint : iiiNear + iiiMass ≡ iiiFullMass
    endpoint = refl
  in
  subst
    (λ upper → iiiNear + Geo.partialSum iiiRatio cutoff ≤ upper)
    endpoint raw

-- Combined conservative coefficient useful after the 3xy^2 <= x^3+2y^3
-- Young split.  If row and column masses are each bounded by the same kernel
-- mass M, the 1/3 and 2/3 charges sum back to M.  Thus each of I,II,III costs
-- at most its kernel mass in the ideal symmetric finite ledger.  Their total
-- conservative mass is the exact rational below.
combinedMass : ℚ
combinedMass = Int.+ 4993 / 468

combinedMassMeaning :
  iMass + iiMass + iiiFullMass ≡ combinedMass
combinedMassMeaning = solve []

round91FrequencyLocalIKernelMassClosed : Bool
round91FrequencyLocalIKernelMassClosed = true
round91FrequencyLocalIIKernelMassClosed : Bool
round91FrequencyLocalIIKernelMassClosed = true
round91FrequencyLocalIIIKernelMassClosed : Bool
round91FrequencyLocalIIIKernelMassClosed = true
round91FrequencyLocalCombinedConservativeMassClosed : Bool
round91FrequencyLocalCombinedConservativeMassClosed = true

round91FrequencyLocalCombinedConservativeMassClosedIsTrue :
  round91FrequencyLocalCombinedConservativeMassClosed ≡ true
round91FrequencyLocalCombinedConservativeMassClosedIsTrue = refl
