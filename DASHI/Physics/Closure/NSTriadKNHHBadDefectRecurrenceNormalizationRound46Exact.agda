module DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 45 identified C_q as the scale-neutral HH-bad observable.  This file
-- proves the exact normalization suggested by the physical defect programme.
-- If B_q is the time-integrated directional-defect rate and
--
--   B_(q+1) <= (alpha/2) B_q + delta 2^(-(q+1)) beta,
--
-- then
--
--   C_q := delta^(-1) 2^q B_q
--
-- obeys
--
--   C_(q+1) <= alpha C_q + beta.
--
-- The factor 1/2 is therefore exactly the contraction needed to compensate
-- the next dyadic normalization.  No PDE recurrence is asserted here: the
-- theorem says precisely what one-shell physical defect transfer would close
-- the normalized-profile lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale

record PhysicalDefectShellRecurrence
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    defectRate : Nat → ℚ
    alpha beta : ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta

    oneShellDefectTransfer : ∀ q →
      defectRate (suc q)
      ≤ alpha * Sharp.half * defectRate q
        + Threshold.threshold parameter
          * Sharp.inverseDyadicScale (suc q) * beta

open PhysicalDefectShellRecurrence public

normalizedDefectProfile :
  ∀ {parameter} →
  PhysicalDefectShellRecurrence parameter → Nat → ℚ
normalizedDefectProfile {parameter} recurrence q =
  Threshold.thresholdInverse parameter
    * Sharp.dyadicScale q
    * defectRate recurrence q

normalizationFactor :
  ∀ {parameter} →
  PhysicalDefectShellRecurrence parameter → Nat → ℚ
normalizationFactor {parameter} recurrence q =
  Threshold.thresholdInverse parameter * Sharp.dyadicScale q

normalizationFactorNonnegative :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  0ℚ ≤ normalizationFactor recurrence q
normalizationFactorNonnegative {parameter} recurrence q =
  let
    instance
      inverseNNI = nonNegative (Threshold.thresholdInverseNonnegative parameter)
      scaleNNI = nonNegative (Scale.dyadicScaleNonnegative q)
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse parameter)
          (Sharp.dyadicScale q)
  in
  ℚP.nonNegative⁻¹ (normalizationFactor recurrence q)

normalizedFirstTermIdentity :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  normalizationFactor recurrence (suc q)
    * (alpha recurrence * Sharp.half * defectRate recurrence q)
  ≡ alpha recurrence * normalizedDefectProfile recurrence q
normalizedFirstTermIdentity recurrence q =
  solve
    ( Threshold.thresholdInverse _
    ∷ Sharp.dyadicScale q
    ∷ alpha recurrence
    ∷ defectRate recurrence q
    ∷ [])

normalizedForcingIdentity :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  normalizationFactor recurrence (suc q)
    * (Threshold.threshold parameter
      * Sharp.inverseDyadicScale (suc q)
      * beta recurrence)
  ≡ beta recurrence
normalizedForcingIdentity {parameter} recurrence q
  rewrite Threshold.inverseMeaning parameter
        | Sharp.inverseDyadicReciprocal (suc q) =
  solve (beta recurrence ∷ [])

normalizedDefectRecurrence :
  ∀ {parameter}
    (recurrence : PhysicalDefectShellRecurrence parameter) q →
  normalizedDefectProfile recurrence (suc q)
  ≤ alpha recurrence * normalizedDefectProfile recurrence q
    + beta recurrence
normalizedDefectRecurrence recurrence q =
  let
    factor = normalizationFactor recurrence (suc q)
    factorNN = normalizationFactorNonnegative recurrence (suc q)

    scaled :
      factor * defectRate recurrence (suc q)
      ≤ factor
        * (alpha recurrence * Sharp.half * defectRate recurrence q
          + Threshold.threshold _
            * Sharp.inverseDyadicScale (suc q) * beta recurrence)
    scaled =
      let instance factorNNI = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg factor
        (oneShellDefectTransfer recurrence q)

    distribute :
      factor
        * (alpha recurrence * Sharp.half * defectRate recurrence q
          + Threshold.threshold _
            * Sharp.inverseDyadicScale (suc q) * beta recurrence)
      ≡
      factor * (alpha recurrence * Sharp.half * defectRate recurrence q)
      + factor * (Threshold.threshold _
        * Sharp.inverseDyadicScale (suc q) * beta recurrence)
    distribute = solve
      ( factor
      ∷ alpha recurrence
      ∷ defectRate recurrence q
      ∷ Threshold.threshold _
      ∷ Sharp.inverseDyadicScale (suc q)
      ∷ beta recurrence
      ∷ [])

    rhsIdentity :
      factor
        * (alpha recurrence * Sharp.half * defectRate recurrence q
          + Threshold.threshold _
            * Sharp.inverseDyadicScale (suc q) * beta recurrence)
      ≡ alpha recurrence * normalizedDefectProfile recurrence q
        + beta recurrence
    rhsIdentity =
      trans distribute
        (trans
          (cong₂ _+_
            (normalizedFirstTermIdentity recurrence q)
            (normalizedForcingIdentity recurrence q))
          refl)
  in
  subst
    (λ right →
      normalizedDefectProfile recurrence (suc q) ≤ right)
    rhsIdentity
    scaled
  where
  open import Relation.Binary.PropositionalEquality using (cong₂)

hhBadDefectRecurrenceNormalizationClosed : Bool
hhBadDefectRecurrenceNormalizationClosed = true

hhBadDefectRecurrenceNormalizationClosedIsTrue :
  hhBadDefectRecurrenceNormalizationClosed ≡ true
hhBadDefectRecurrenceNormalizationClosedIsTrue = refl
