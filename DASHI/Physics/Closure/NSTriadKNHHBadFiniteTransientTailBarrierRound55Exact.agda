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
-- This file permits arbitrarily large finite-prefix amplification.  After a
-- selected q0 it suffices to prove
--   alpha_q <= a, beta_q <= b, a C_* + b <= C_*.
-- A complete Nat split/induction below then proves M_q<=C_* for every q; there
-- is no residual "global barrier" witness and no global alpha_q<1 hypothesis.
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

data TailAt (start : Nat) : Nat → Set where
  atStart : TailAt start start
  atStep : ∀ {q} → TailAt start q → TailAt start (suc q)

tailAtOrder : ∀ {start q} → TailAt start q → start Nat.≤ q
tailAtOrder atStart = Nat.s≤s⁻¹ (Nat.s≤s Nat.z≤n)
tailAtOrder (atStep witness) = Nat.≤-step (tailAtOrder witness)

-- A total structural split of Nat at a selected boundary.  This is arithmetic,
-- not an analytic assumption.
data PrefixOrTail (start q : Nat) : Set where
  prefix : q Nat.≤ start → PrefixOrTail start q
  tail : TailAt start q → PrefixOrTail start q

tailFromZero : ∀ q → TailAt zero q
tailFromZero zero = atStart
tailFromZero (suc q) = atStep (tailFromZero q)

liftTailSuc : ∀ {start q} → TailAt start q → TailAt (suc start) (suc q)
liftTailSuc atStart = atStart
liftTailSuc (atStep witness) = atStep (liftTailSuc witness)

splitPrefixOrTail : ∀ start q → PrefixOrTail start q
splitPrefixOrTail zero q = tail (tailFromZero q)
splitPrefixOrTail (suc start) zero = prefix Nat.z≤n
splitPrefixOrTail (suc start) (suc q) with splitPrefixOrTail start q
... | prefix proof = prefix (Nat.s≤s proof)
... | tail witness = tail (liftTailSuc witness)

scaleCapacityByAlphaTail :
  ∀ {physical} (barrier : TailAffineBarrier physical) q →
  q0 barrier Nat.≤ q →
  Minimal.minimalCapacity physical q ≤ ceiling barrier →
  Raw.alpha physical q * Minimal.minimalCapacity physical q
  ≤ alphaTail barrier * ceiling barrier
scaleCapacityByAlphaTail {physical} barrier q tailOrder current =
  let
    alphaStep =
      let instance alphaNN = nonNegative (Raw.alphaNonnegative physical q)
      in ℚP.*-monoˡ-≤-nonNeg (Raw.alpha physical q) current
    ceilingStep =
      let instance ceilingNN = nonNegative (ceilingNonnegative barrier)
      in ℚP.*-monoʳ-≤-nonNeg
        (ceiling barrier)
        (alphaTailBound barrier q tailOrder)
  in
  ℚP.≤-trans alphaStep ceilingStep

tailStepPreservesCeiling :
  ∀ {physical} (barrier : TailAffineBarrier physical) q →
  q0 barrier Nat.≤ q →
  Minimal.minimalCapacity physical q ≤ ceiling barrier →
  Minimal.minimalCapacity physical (suc q) ≤ ceiling barrier
tailStepPreservesCeiling {physical} barrier q tailOrder current =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (scaleCapacityByAlphaTail barrier q tailOrder current)
      (forcingTailBound barrier q tailOrder))
    (tailAffineCloses barrier)

tailCapacityBelow :
  ∀ {physical} (barrier : TailAffineBarrier physical) {q} →
  TailAt (q0 barrier) q →
  Minimal.minimalCapacity physical q ≤ ceiling barrier
tailCapacityBelow barrier atStart =
  finitePrefixBelow barrier (q0 barrier) (tailAtOrder atStart)
tailCapacityBelow barrier (atStep {q} witness) =
  tailStepPreservesCeiling barrier q
    (tailAtOrder witness)
    (tailCapacityBelow barrier witness)

globalMinimalBelowCeiling :
  ∀ {physical} (barrier : TailAffineBarrier physical) q →
  Minimal.minimalCapacity physical q ≤ ceiling barrier
globalMinimalBelowCeiling barrier q with splitPrefixOrTail (q0 barrier) q
... | prefix proof = finitePrefixBelow barrier q proof
... | tail witness = tailCapacityBelow barrier witness

asUniformMinimalCapacity :
  ∀ {physical} → TailAffineBarrier physical → Minimal.UniformMinimalCapacity physical
asUniformMinimalCapacity barrier = record
  { ceiling = ceiling barrier
  ; ceilingNonnegative = ceilingNonnegative barrier
  ; minimalBelowCeiling = globalMinimalBelowCeiling barrier
  }

finiteTransientAmplificationPermitted : Bool
finiteTransientAmplificationPermitted = true

tailBarrierGlobalInductionClosed : Bool
tailBarrierGlobalInductionClosed = true

finiteTransientAmplificationPermittedIsTrue :
  finiteTransientAmplificationPermitted ≡ true
finiteTransientAmplificationPermittedIsTrue = refl

tailBarrierGlobalInductionClosedIsTrue :
  tailBarrierGlobalInductionClosed ≡ true
tailBarrierGlobalInductionClosedIsTrue = refl
