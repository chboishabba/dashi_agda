module DASHI.Physics.Closure.NSTriadKNHHBadVariableDuhamelToWeightedGreenRound51Exact where

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
-- Move Route C all the way back to the physical inherited/generated/leakage
-- decomposition.  Allow shell-dependent coefficients alpha_q and beta_q:
--
--   B_(q+1) = I_q + G_q + L_q,
--   I_q <= (alpha_q/2) B_q,
--   G_q + L_q <= delta_* 2^(-(q+1)) beta_q.
--
-- Exact dyadic normalization then gives
--
--   C_(q+1) <= alpha_q C_q + beta_q,
--   C_q = delta_*^-1 2^q B_q.
--
-- Hence the literal Duhamel calculation can output its ACTUAL shellwise
-- alpha_q,beta_q directly into the weighted-Green theorem; it need not first be
-- compressed to a uniform zeta, constant beta, or raw summability regime.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green

record PhysicalVariableDefectDuhamel : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate inherited generated leakage : Nat → ℚ
    alpha forcing : Nat → ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    inheritedNonnegative : ∀ q → 0ℚ ≤ inherited q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    alphaAtMostOne : ∀ q → alpha q ≤ Data.Rational.Base.1ℚ
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q

    successorDecomposition : ∀ q →
      defectRate (suc q) ≡ inherited q + generated q + leakage q

    inheritedTransfer : ∀ q →
      inherited q ≤ alpha q * Sharp.half * defectRate q

    generatedLeakageTransfer : ∀ q →
      generated q + leakage q
      ≤ Threshold.threshold parameter
        * Sharp.inverseDyadicScale (suc q) * forcing q

open PhysicalVariableDefectDuhamel public

normalizedVariableDefect : PhysicalVariableDefectDuhamel → Nat → ℚ
normalizedVariableDefect physical q =
  Threshold.thresholdInverse (parameter physical)
    * Sharp.dyadicScale q
    * defectRate physical q

normalizationFactor : PhysicalVariableDefectDuhamel → Nat → ℚ
normalizationFactor physical q =
  Threshold.thresholdInverse (parameter physical) * Sharp.dyadicScale q

normalizationFactorNonnegative :
  (physical : PhysicalVariableDefectDuhamel) →
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

componentBoundsGiveVariableShellTransfer :
  (physical : PhysicalVariableDefectDuhamel) →
  ∀ q →
  defectRate physical (suc q)
  ≤ alpha physical q * Sharp.half * defectRate physical q
    + Threshold.threshold (parameter physical)
      * Sharp.inverseDyadicScale (suc q) * forcing physical q
componentBoundsGiveVariableShellTransfer physical q =
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
    sourceMeaning
    summed

normalizedInheritedIdentity :
  (physical : PhysicalVariableDefectDuhamel) →
  ∀ q →
  normalizationFactor physical (suc q)
    * (alpha physical q * Sharp.half * defectRate physical q)
  ≡ alpha physical q * normalizedVariableDefect physical q
normalizedInheritedIdentity physical q =
  solve
    ( Threshold.thresholdInverse (parameter physical)
    ∷ Sharp.dyadicScale q
    ∷ alpha physical q
    ∷ defectRate physical q
    ∷ [])

normalizedForcingIdentity :
  (physical : PhysicalVariableDefectDuhamel) →
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
      ≡ Data.Rational.Base.1ℚ * (inverseDyadic * dyadic) * beta
    cancelThreshold =
      cong (λ product → product * (inverseDyadic * dyadic) * beta)
        (Threshold.inverseMeaning (parameter physical))

    cancelDyadic :
      Data.Rational.Base.1ℚ * (inverseDyadic * dyadic) * beta
      ≡ Data.Rational.Base.1ℚ * Data.Rational.Base.1ℚ * beta
    cancelDyadic =
      cong (λ product → Data.Rational.Base.1ℚ * product * beta)
        (Sharp.inverseDyadicReciprocal (suc q))

    finish :
      Data.Rational.Base.1ℚ * Data.Rational.Base.1ℚ * beta ≡ beta
    finish = solve (beta ∷ [])
  in trans regroup (trans cancelThreshold (trans cancelDyadic finish))

normalizedVariableRecurrence :
  (physical : PhysicalVariableDefectDuhamel) →
  ∀ q →
  normalizedVariableDefect physical (suc q)
  ≤ alpha physical q * normalizedVariableDefect physical q
    + forcing physical q
normalizedVariableRecurrence physical q =
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
      in ℚP.*-monoˡ-≤-nonNeg factor
        (componentBoundsGiveVariableShellTransfer physical q)

    rhsDistributed :
      factor
        * (alpha physical q * Sharp.half * defectRate physical q
          + Threshold.threshold (parameter physical)
            * Sharp.inverseDyadicScale (suc q) * forcing physical q)
      ≡ alpha physical q * normalizedVariableDefect physical q
        + forcing physical q
    rhsDistributed =
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
    (λ right →
      normalizedVariableDefect physical (suc q) ≤ right)
    rhsDistributed
    scaled

asWeightedGreenRecurrence :
  PhysicalVariableDefectDuhamel → Green.VariableGreenRecurrence
asWeightedGreenRecurrence physical = record
  { profile = normalizedVariableDefect physical
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
      in ℚP.nonNegative⁻¹ (normalizedVariableDefect physical q)
  ; alphaNonnegative = alphaNonnegative physical
  ; alphaAtMostOne = alphaAtMostOne physical
  ; forcingNonnegative = forcingNonnegative physical
  ; recurrence = normalizedVariableRecurrence physical
  }

variableDuhamelFeedsWeightedGreenExactly : Bool
variableDuhamelFeedsWeightedGreenExactly = true

physicalVariableDuhamelConstructed : Bool
physicalVariableDuhamelConstructed = false

variableDuhamelFeedsWeightedGreenExactlyIsTrue :
  variableDuhamelFeedsWeightedGreenExactly ≡ true
variableDuhamelFeedsWeightedGreenExactlyIsTrue = refl
