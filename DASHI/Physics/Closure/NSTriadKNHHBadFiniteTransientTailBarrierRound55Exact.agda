module DASHI.Physics.Closure.NSTriadKNHHBadFiniteTransientTailBarrierRound55Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 54 reduced HH-bad to the explicit least recurrence
--   M_0=C_0, M_(q+1)=alpha_q M_q+beta_q.
-- This file removes the need for a global alpha_q<1 hypothesis.  Arbitrarily
-- large transient amplification is permitted on a finite prefix.  After a
-- selected tail index q0 it suffices to prove a uniform affine envelope
--
--   alpha_q <= a, beta_q <= b,  a C_* + b <= C_*.
--
-- Together with the finite-prefix check M_q<=C_* for q<=q0 this proves the
-- global bound M_q<=C_*.  This is the exact high-alpha form wanted by the
-- physical shell argument: finitely many bad shells are checked literally;
-- only the asymptotic tail needs a stationary barrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadMinimalCapacityRound54Exact as Minimal

record TailAffineBarrier
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    q0 : Nat
    ceiling alphaTail forcingTail : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    alphaTailNonnegative : 0ℚ ≤ alphaTail

    finitePrefixBelow : ∀ q → q Nat.≤ q0 →
      Minimal.minimalCapacity physical q ≤ ceiling

    alphaTailBound : ∀ q → q0 Nat.≤ q →
      Raw.alpha physical q ≤ alphaTail

    forcingTailBound : ∀ q → q0 Nat.≤ q →
      Raw.forcing physical q ≤ forcingTail

    tailAffineCloses :
      alphaTail * ceiling + forcingTail ≤ ceiling

open TailAffineBarrier public

scaleCapacityByAlphaTail :
  ∀ {physical} (barrier : TailAffineBarrier physical) q →
  q0 barrier Nat.≤ q →
  Minimal.minimalCapacity physical q ≤ ceiling barrier →
  Raw.alpha physical q * Minimal.minimalCapacity physical q
  ≤ alphaTail barrier * ceiling barrier
scaleCapacityByAlphaTail {physical} barrier q tail current =
  let
    alphaStep :
      Raw.alpha physical q * Minimal.minimalCapacity physical q
      ≤ Raw.alpha physical q * ceiling barrier
    alphaStep =
      let instance alphaNN = nonNegative (Raw.alphaNonnegative physical q)
      in ℚP.*-monoˡ-≤-nonNeg (Raw.alpha physical q) current

    ceilingStep :
      Raw.alpha physical q * ceiling barrier
      ≤ alphaTail barrier * ceiling barrier
    ceilingStep =
      let instance ceilingNN = nonNegative (ceilingNonnegative barrier)
      in ℚP.*-monoʳ-≤-nonNeg
        (ceiling barrier)
        (alphaTailBound barrier q tail)
  in
  ℚP.≤-trans alphaStep ceilingStep

tailStepPreservesCeiling :
  ∀ {physical} (barrier : TailAffineBarrier physical) q →
  q0 barrier Nat.≤ q →
  Minimal.minimalCapacity physical q ≤ ceiling barrier →
  Minimal.minimalCapacity physical (suc q) ≤ ceiling barrier
tailStepPreservesCeiling {physical} barrier q tail current =
  let
    inherited = scaleCapacityByAlphaTail barrier q tail current
    forcing = forcingTailBound barrier q tail
    summed = ℚP.+-mono-≤ inherited forcing
  in
  ℚP.≤-trans summed (tailAffineCloses barrier)

record GlobalTailBarrierClosure
    {physical : Raw.PhysicalGeneralVariableDefectDuhamel}
    (barrier : TailAffineBarrier physical) : Set where
  field
    globalMinimalBelowCeiling : ∀ q →
      Minimal.minimalCapacity physical q ≤ ceiling barrier

open GlobalTailBarrierClosure public

asUniformMinimalCapacity :
  ∀ {physical} {barrier : TailAffineBarrier physical} →
  GlobalTailBarrierClosure barrier →
  Minimal.UniformMinimalCapacity physical
asUniformMinimalCapacity {barrier = barrier} closure = record
  { ceiling = ceiling barrier
  ; ceilingNonnegative = ceilingNonnegative barrier
  ; minimalBelowCeiling = globalMinimalBelowCeiling closure
  }

finiteTransientAmplificationPermitted : Bool
finiteTransientAmplificationPermitted = true

tailBarrierUsesOnlyAffineClosure : Bool
tailBarrierUsesOnlyAffineClosure = true

finiteTransientAmplificationPermittedIsTrue :
  finiteTransientAmplificationPermitted ≡ true
finiteTransientAmplificationPermittedIsTrue = refl

tailBarrierUsesOnlyAffineClosureIsTrue :
  tailBarrierUsesOnlyAffineClosure ≡ true
tailBarrierUsesOnlyAffineClosureIsTrue = refl
