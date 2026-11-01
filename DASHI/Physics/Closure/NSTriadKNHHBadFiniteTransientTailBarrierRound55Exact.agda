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
-- Round 55 permits arbitrarily large finite-prefix amplification.  Round 56
-- sharpens the asymptotic test further: a varying shellwise depletion
--
--   alpha_q = 1-sigma_q,   beta_q <= sigma_q C_*
--
-- preserves C_* directly.  Thus no uniform tail contraction constant is
-- required once the literal NS Duhamel terms are in hand.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

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
tailAtOrder atStart = NatP.≤-refl
tailAtOrder (atStep witness) = NatP.≤-step (tailAtOrder witness)

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
  finitePrefixBelow barrier (q0 barrier) NatP.≤-refl
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

------------------------------------------------------------------------
-- ROUND 56: variable shellwise depletion test.
------------------------------------------------------------------------

record ShellwiseDepletionTail
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    depletionStart : Nat
    depletionCeiling : ℚ
    sigma : Nat → ℚ

    depletionCeilingNonnegative : 0ℚ ≤ depletionCeiling
    sigmaNonnegative : ∀ q → 0ℚ ≤ sigma q

    finiteDepletionPrefixBelow : ∀ q → q Nat.≤ depletionStart →
      Minimal.minimalCapacity physical q ≤ depletionCeiling

    alphaIsOneMinusSigma : ∀ q → depletionStart Nat.≤ q →
      Raw.alpha physical q ≡ 1ℚ - sigma q

    forcingBelowDepletion : ∀ q → depletionStart Nat.≤ q →
      Raw.forcing physical q ≤ sigma q * depletionCeiling

open ShellwiseDepletionTail public

scaleCapacityByPhysicalAlpha :
  ∀ {physical} (depletion : ShellwiseDepletionTail physical) q →
  Minimal.minimalCapacity physical q ≤ depletionCeiling depletion →
  Raw.alpha physical q * Minimal.minimalCapacity physical q
  ≤ Raw.alpha physical q * depletionCeiling depletion
scaleCapacityByPhysicalAlpha {physical} depletion q current =
  let instance alphaNN = nonNegative (Raw.alphaNonnegative physical q)
  in ℚP.*-monoˡ-≤-nonNeg (Raw.alpha physical q) current

depletionBalanceIdentity :
  ∀ {physical} (depletion : ShellwiseDepletionTail physical) q →
  depletionStart depletion Nat.≤ q →
  Raw.alpha physical q * depletionCeiling depletion
    + sigma depletion q * depletionCeiling depletion
  ≡ depletionCeiling depletion
depletionBalanceIdentity {physical} depletion q tailOrder =
  trans
    (cong
      (λ alphaQ →
        alphaQ * depletionCeiling depletion
          + sigma depletion q * depletionCeiling depletion)
      (alphaIsOneMinusSigma depletion q tailOrder))
    (solve (sigma depletion q ∷ depletionCeiling depletion ∷ []))

depletionStepPreservesCeiling :
  ∀ {physical} (depletion : ShellwiseDepletionTail physical) q →
  depletionStart depletion Nat.≤ q →
  Minimal.minimalCapacity physical q ≤ depletionCeiling depletion →
  Minimal.minimalCapacity physical (suc q) ≤ depletionCeiling depletion
depletionStepPreservesCeiling {physical} depletion q tailOrder current =
  let
    inherited = scaleCapacityByPhysicalAlpha depletion q current
    produced = forcingBelowDepletion depletion q tailOrder
    summed = ℚP.+-mono-≤ inherited produced
  in
  subst
    (λ upper →
      Minimal.minimalCapacity physical (suc q) ≤ upper)
    (depletionBalanceIdentity depletion q tailOrder)
    summed

depletionTailBelow :
  ∀ {physical} (depletion : ShellwiseDepletionTail physical) {q} →
  TailAt (depletionStart depletion) q →
  Minimal.minimalCapacity physical q ≤ depletionCeiling depletion
depletionTailBelow depletion atStart =
  finiteDepletionPrefixBelow depletion
    (depletionStart depletion) NatP.≤-refl
depletionTailBelow depletion (atStep {q} witness) =
  depletionStepPreservesCeiling depletion q
    (tailAtOrder witness)
    (depletionTailBelow depletion witness)

globalMinimalBelowDepletionCeiling :
  ∀ {physical} (depletion : ShellwiseDepletionTail physical) q →
  Minimal.minimalCapacity physical q ≤ depletionCeiling depletion
globalMinimalBelowDepletionCeiling depletion q
  with splitPrefixOrTail (depletionStart depletion) q
... | prefix proof = finiteDepletionPrefixBelow depletion q proof
... | tail witness = depletionTailBelow depletion witness

depletionAsUniformMinimalCapacity :
  ∀ {physical} →
  ShellwiseDepletionTail physical → Minimal.UniformMinimalCapacity physical
depletionAsUniformMinimalCapacity depletion = record
  { ceiling = depletionCeiling depletion
  ; ceilingNonnegative = depletionCeilingNonnegative depletion
  ; minimalBelowCeiling = globalMinimalBelowDepletionCeiling depletion
  }

finiteTransientAmplificationPermitted : Bool
finiteTransientAmplificationPermitted = true

tailBarrierGlobalInductionClosed : Bool
tailBarrierGlobalInductionClosed = true

shellwiseDepletionCapacityClosed : Bool
shellwiseDepletionCapacityClosed = true

noUniformTailContractionConstantRequired : Bool
noUniformTailContractionConstantRequired = true

finiteTransientAmplificationPermittedIsTrue :
  finiteTransientAmplificationPermitted ≡ true
finiteTransientAmplificationPermittedIsTrue = refl

tailBarrierGlobalInductionClosedIsTrue :
  tailBarrierGlobalInductionClosed ≡ true
tailBarrierGlobalInductionClosedIsTrue = refl

shellwiseDepletionCapacityClosedIsTrue :
  shellwiseDepletionCapacityClosed ≡ true
shellwiseDepletionCapacityClosedIsTrue = refl

noUniformTailContractionConstantRequiredIsTrue :
  noUniformTailContractionConstantRequired ≡ true
noUniformTailContractionConstantRequiredIsTrue = refl
