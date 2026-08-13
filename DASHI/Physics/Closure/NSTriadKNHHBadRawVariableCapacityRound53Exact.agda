module DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact where

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
-- Round 52's master consumer accepts an arbitrary nonnegative shell
-- supersolution.  This file connects that consumer directly to the literal
-- inherited/generated/leakage Duhamel shape WITHOUT re-introducing alpha<=1.
-- It also proves the exact headroom form for a variable capacity
--
--   M_q = C_* - d_q.
--
-- The physical analytic task is now only to prove the component transfer
-- inequalities and a capacity/headroom inequality for the actual Duhamel
-- constituents.  No strict contraction or raw summability hypothesis remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact as Barrier

record PhysicalGeneralVariableDefectDuhamel : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate inherited generated leakage : Nat → ℚ
    alpha forcing : Nat → ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    inheritedNonnegative : ∀ q → 0ℚ ≤ inherited q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q

    successorDecomposition : ∀ q →
      defectRate (suc q) ≡ inherited q + generated q + leakage q

    inheritedTransfer : ∀ q →
      inherited q ≤ alpha q * Sharp.half * defectRate q

    generatedLeakageTransfer : ∀ q →
      generated q + leakage q
      ≤ Threshold.threshold parameter
        * Sharp.inverseDyadicScale (suc q) * forcing q

open PhysicalGeneralVariableDefectDuhamel public

normalizedDefect : PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizedDefect physical q =
  Threshold.thresholdInverse (parameter physical)
    * Sharp.dyadicScale q
    * defectRate physical q

normalizationFactor : PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizationFactor physical q =
  Threshold.thresholdInverse (parameter physical) * Sharp.dyadicScale q

normalizationFactorNonnegative :
  (physical : PhysicalGeneralVariableDefectDuhamel) →
  ∀ q → 0ℚ ≤ normalizationFactor physical q
normalizationFactorNonnegative physical q =
  let instance
    inverseNNI = nonNegative
      (Threshold.thresholdInverseNonnegative (parameter physical))
    scaleNNI = nonNegative (Scale.dyadicScaleNonnegative q)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg
        (Threshold.thresholdInverse (parameter physical))
        (Sharp.dyadicScale q)
  in ℚP.nonNegative⁻¹ (normalizationFactor physical q)

componentTransfer :
  (physical : PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  defectRate physical (suc q)
  ≤ alpha physical q * Sharp.half * defectRate physical q
    + Threshold.threshold (parameter physical)
      * Sharp.inverseDyadicScale (suc q) * forcing physical q
componentTransfer physical q =
  let
    summed :
      inherited physical q + (generated physical q + leakage physical q)
      ≤ alpha physical q * Sharp.half * defectRate physical q
        + Threshold.threshold (parameter physical)
          * Sharp.inverseDyadicScale (suc q) * forcing physical q
    summed =
      ℚP.+-mono-≤
        (inheritedTransfer physical q)
        (generatedLeakageTransfer physical q)

    sourceMeaning :
      defectRate physical (suc q)
      ≡ inherited physical q + (generated physical q + leakage physical q)
    sourceMeaning =
      trans
        (successorDecomposition physical q)
        (solve
          ( inherited physical q
          ∷ generated physical q
          ∷ leakage physical q
          ∷ []))
  in
  subst
    (λ source →
      source
      ≤ alpha physical q * Sharp.half * defectRate physical q
        + Threshold.threshold (parameter physical)
          * Sharp.inverseDyadicScale (suc q) * forcing physical q)
    (sym sourceMeaning)
    summed

normalizedInheritedIdentity :
  (physical : PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  normalizationFactor physical (suc q)
    * (alpha physical q * Sharp.half * defectRate physical q)
  ≡ alpha physical q * normalizedDefect physical q
normalizedInheritedIdentity physical q =
  solve
    ( Threshold.thresholdInverse (parameter physical)
    ∷ Sharp.dyadicScale q
    ∷ alpha physical q
    ∷ defectRate physical q
    ∷ [])

normalizedForcingIdentity :
  (physical : PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  normalizationFactor physical (suc q)
    * (Threshold.threshold (parameter physical)
      * Sharp.inverseDyadicScale (suc q) * forcing physical q)
  ≡ forcing physical q
normalizedForcingIdentity physical q =
  let
    inverse = Threshold.thresholdInverse (parameter physical)
    threshold = Threshold.threshold (parameter physical)
    dyadic = Sharp.dyadicScale (suc q)
    inverseDyadic = Sharp.inverseDyadicScale (suc q)
    beta = forcing physical q

    regroup :
      (inverse * dyadic) * (threshold * inverseDyadic * beta)
      ≡ (inverse * threshold) * (inverseDyadic * dyadic) * beta
    regroup = solve (inverse ∷ threshold ∷ dyadic ∷ inverseDyadic ∷ beta ∷ [])

    cancelThreshold :
      (inverse * threshold) * (inverseDyadic * dyadic) * beta
      ≡ 1ℚ * (inverseDyadic * dyadic) * beta
    cancelThreshold =
      cong (λ product → product * (inverseDyadic * dyadic) * beta)
        (Threshold.inverseMeaning (parameter physical))

    cancelDyadic :
      1ℚ * (inverseDyadic * dyadic) * beta
      ≡ 1ℚ * 1ℚ * beta
    cancelDyadic =
      cong (λ product → 1ℚ * product * beta)
        (Sharp.inverseDyadicReciprocal (suc q))

    finish : 1ℚ * 1ℚ * beta ≡ beta
    finish = solve (beta ∷ [])
  in trans regroup (trans cancelThreshold (trans cancelDyadic finish))

normalizedRecurrence :
  (physical : PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  normalizedDefect physical (suc q)
  ≤ alpha physical q * normalizedDefect physical q + forcing physical q
normalizedRecurrence physical q =
  let
    factor = normalizationFactor physical (suc q)
    scaled :
      factor * defectRate physical (suc q)
      ≤ factor
        * (alpha physical q * Sharp.half * defectRate physical q
          + Threshold.threshold (parameter physical)
            * Sharp.inverseDyadicScale (suc q) * forcing physical q)
    scaled =
      let instance factorNNI =
        nonNegative (normalizationFactorNonnegative physical (suc q))
      in ℚP.*-monoˡ-≤-nonNeg factor (componentTransfer physical q)

    rhsMeaning :
      factor
        * (alpha physical q * Sharp.half * defectRate physical q
          + Threshold.threshold (parameter physical)
            * Sharp.inverseDyadicScale (suc q) * forcing physical q)
      ≡ alpha physical q * normalizedDefect physical q + forcing physical q
    rhsMeaning =
      trans
        (solve
          ( factor
          ∷ alpha physical q
          ∷ defectRate physical q
          ∷ Threshold.threshold (parameter physical)
          ∷ Sharp.inverseDyadicScale (suc q)
          ∷ forcing physical q
          ∷ []))
        (cong₂ _+_
          (normalizedInheritedIdentity physical q)
          (normalizedForcingIdentity physical q))
  in
  subst
    (λ right → normalizedDefect physical (suc q) ≤ right)
    rhsMeaning
    scaled

asGeneralBarrierRecurrence :
  PhysicalGeneralVariableDefectDuhamel → Barrier.GeneralHHBadRecurrence
asGeneralBarrierRecurrence physical = record
  { profile = normalizedDefect physical
  ; alpha = alpha physical
  ; forcing = forcing physical
  ; profileNonnegative = λ q →
      let instance
        inverseNNI = nonNegative
          (Threshold.thresholdInverseNonnegative (parameter physical))
        scaleNNI = nonNegative (Scale.dyadicScaleNonnegative q)
        defectNNI = nonNegative (defectRateNonnegative physical q)
        firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse (parameter physical))
          (Sharp.dyadicScale q)
        totalNNI = ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse (parameter physical) * Sharp.dyadicScale q)
          (defectRate physical q)
      in ℚP.nonNegative⁻¹ (normalizedDefect physical q)
  ; alphaNonnegative = alphaNonnegative physical
  ; forcingNonnegative = forcingNonnegative physical
  ; recurrence = normalizedRecurrence physical
  }

record RawVariableCapacity
    (physical : PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    capacity : Nat → ℚ
    capacityNonnegative : ∀ q → 0ℚ ≤ capacity q
    baseBelowCapacity : normalizedDefect physical zero ≤ capacity zero
    capacityInvariant : ∀ q →
      alpha physical q * capacity q + forcing physical q
      ≤ capacity (suc q)

open RawVariableCapacity public

rawVariableCapacityAsShellSupersolution :
  ∀ {physical} →
  RawVariableCapacity physical →
  Barrier.ShellSupersolution (asGeneralBarrierRecurrence physical)
rawVariableCapacityAsShellSupersolution capacityData = record
  { barrier = capacity capacityData
  ; barrierNonnegative = capacityNonnegative capacityData
  ; baseBelowBarrier = baseBelowCapacity capacityData
  ; barrierSupersolution = capacityInvariant capacityData
  }

physicalHHBadRawVariableCapacityInvariant :
  ∀ {physical} →
  (capacityData : RawVariableCapacity physical) →
  ∀ q → normalizedDefect physical q ≤ capacity capacityData q
physicalHHBadRawVariableCapacityInvariant {physical} capacityData =
  Barrier.profileBelowAnyShellBarrier
    (asGeneralBarrierRecurrence physical)
    (rawVariableCapacityAsShellSupersolution capacityData)

record RawHeadroomCapacity
    (physical : PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    ceiling : ℚ
    headroom : Nat → ℚ
    capacityNonnegative : ∀ q → 0ℚ ≤ ceiling - headroom q
    baseBelowHeadroomCapacity :
      normalizedDefect physical zero ≤ ceiling - headroom zero
    headroomUpdate : ∀ q →
      forcing physical q + headroom (suc q)
      ≤ (ceiling - alpha physical q * ceiling)
          + alpha physical q * headroom q

open RawHeadroomCapacity public

headroomUpdateIsCapacityInvariant :
  ∀ {physical} (headroomData : RawHeadroomCapacity physical) q →
  alpha physical q * (ceiling headroomData - headroom headroomData q)
    + forcing physical q
  ≤ ceiling headroomData - headroom headroomData (suc q)
headroomUpdateIsCapacityInvariant {physical} headroomData q =
  let
    alphaQ = alpha physical q
    c = ceiling headroomData
    d = headroom headroomData q
    dNext = headroom headroomData (suc q)
    beta = forcing physical q
    shift = alphaQ * c - alphaQ * d - dNext

    shifted :
      shift + (beta + dNext)
      ≤ shift + ((c - alphaQ * c) + alphaQ * d)
    shifted = ℚP.+-monoʳ-≤ shift (headroomUpdate headroomData q)

    leftMeaning :
      shift + (beta + dNext)
      ≡ alphaQ * (c - d) + beta
    leftMeaning = solve (alphaQ ∷ c ∷ d ∷ dNext ∷ beta ∷ [])

    rightMeaning :
      shift + ((c - alphaQ * c) + alphaQ * d)
      ≡ c - dNext
    rightMeaning = solve (alphaQ ∷ c ∷ d ∷ dNext ∷ [])
  in
  subst
    (λ left → left ≤ c - dNext)
    leftMeaning
    (subst
      (λ right → shift + (beta + dNext) ≤ right)
      rightMeaning
      shifted)

rawHeadroomAsVariableCapacity :
  ∀ {physical} →
  RawHeadroomCapacity physical → RawVariableCapacity physical
rawHeadroomAsVariableCapacity headroomData = record
  { capacity = λ q → ceiling headroomData - headroom headroomData q
  ; capacityNonnegative = capacityNonnegative headroomData
  ; baseBelowCapacity = baseBelowHeadroomCapacity headroomData
  ; capacityInvariant = headroomUpdateIsCapacityInvariant headroomData
  }

physicalHHBadRawHeadroomInvariant :
  ∀ {physical} →
  (headroomData : RawHeadroomCapacity physical) →
  ∀ q →
  normalizedDefect physical q
  ≤ ceiling headroomData - headroom headroomData q
physicalHHBadRawHeadroomInvariant headroomData =
  physicalHHBadRawVariableCapacityInvariant
    (rawHeadroomAsVariableCapacity headroomData)

rawVariableCapacityAllowsTransientAmplification : Bool
rawVariableCapacityAllowsTransientAmplification = true

physicalGeneralDuhamelConstructed : Bool
physicalGeneralDuhamelConstructed = false

rawVariableCapacityAllowsTransientAmplificationIsTrue :
  rawVariableCapacityAllowsTransientAmplification ≡ true
rawVariableCapacityAllowsTransientAmplificationIsTrue = refl
