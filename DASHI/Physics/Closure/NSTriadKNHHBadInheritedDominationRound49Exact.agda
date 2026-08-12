module DASHI.Physics.Closure.NSTriadKNHHBadInheritedDominationRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Exact-equality factorization is stronger than the recurrence consumer needs.
-- It is enough to dominate the successor inherited term by a dyadic model,
-- contract that model coefficient, and dominate the predecessor model by the
-- actual predecessor defect.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale

record InheritedDomination (parameter : Threshold.PositiveThreshold) : Set where
  field
    inherited totalDefect coefficient : Nat → ℚ
    alpha : ℚ
    alphaNonnegative : 0ℚ ≤ alpha
    coefficientNonnegative : ∀ q → 0ℚ ≤ coefficient q
    inheritedUpper : ∀ q →
      inherited (suc q) ≤ Threshold.threshold parameter
        * Sharp.inverseDyadicScale (suc q) * coefficient (suc q)
    coefficientTransfer : ∀ q →
      coefficient (suc q) ≤ alpha * coefficient q
    predecessorModelBelow : ∀ q →
      Threshold.threshold parameter * Sharp.inverseDyadicScale q * coefficient q
      ≤ totalDefect q

open InheritedDomination public

model : ∀ {parameter} → InheritedDomination parameter → Nat → ℚ
model {parameter} d q = Threshold.threshold parameter
  * Sharp.inverseDyadicScale q * coefficient d q

modelHalfTransfer : ∀ {parameter} (d : InheritedDomination parameter) q →
  model d (suc q) ≤ alpha d * Sharp.half * model d q
modelHalfTransfer {parameter} d q =
  let
    prefactor = Threshold.threshold parameter * Sharp.half * Sharp.inverseDyadicScale q
    prefactorNN : 0ℚ ≤ prefactor
    prefactorNN =
      let instance
        a = nonNegative (Threshold.thresholdNonnegative parameter)
        b = nonNegative Scale.halfNonnegative
        ab = ℚP.nonNeg*nonNeg⇒nonNeg (Threshold.threshold parameter) Sharp.half
        c = nonNegative (Floor.inverseDyadicScaleNonnegative q)
        abc = ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.threshold parameter * Sharp.half) (Sharp.inverseDyadicScale q)
      in ℚP.nonNegative⁻¹ prefactor
    scaled =
      let instance p = nonNegative prefactorNN
      in ℚP.*-monoˡ-≤-nonNeg prefactor (coefficientTransfer d q)
    leftMeaning : prefactor * coefficient d (suc q) ≡ model d (suc q)
    leftMeaning = solve (Threshold.threshold parameter ∷ Sharp.inverseDyadicScale q ∷ coefficient d (suc q) ∷ [])
    rightMeaning : prefactor * (alpha d * coefficient d q) ≡ alpha d * Sharp.half * model d q
    rightMeaning = solve (Threshold.threshold parameter ∷ Sharp.inverseDyadicScale q ∷ alpha d ∷ coefficient d q ∷ [])
  in subst (λ l → l ≤ alpha d * Sharp.half * model d q) leftMeaning
       (subst (λ r → prefactor * coefficient d (suc q) ≤ r) rightMeaning scaled)

inheritedHalfFromDomination : ∀ {parameter} (d : InheritedDomination parameter) q →
  inherited d (suc q) ≤ alpha d * Sharp.half * totalDefect d q
inheritedHalfFromDomination d q =
  let
    factorNN : 0ℚ ≤ alpha d * Sharp.half
    factorNN =
      let instance
        a = nonNegative (alphaNonnegative d)
        b = nonNegative Scale.halfNonnegative
        ab = ℚP.nonNeg*nonNeg⇒nonNeg (alpha d) Sharp.half
      in ℚP.nonNegative⁻¹ (alpha d * Sharp.half)
    modelToPhysical =
      let instance f = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg (alpha d * Sharp.half) (predecessorModelBelow d q)
  in ℚP.≤-trans (inheritedUpper d q)
       (ℚP.≤-trans (modelHalfTransfer d q) modelToPhysical)

hhBadInheritedEqualityRelaxedToDomination : Bool
hhBadInheritedEqualityRelaxedToDomination = true
physicalInheritedDominationConstructed : Bool
physicalInheritedDominationConstructed = false

hhBadInheritedEqualityRelaxedToDominationIsTrue : hhBadInheritedEqualityRelaxedToDomination ≡ true
hhBadInheritedEqualityRelaxedToDominationIsTrue = refl
physicalInheritedDominationConstructedIsFalse : physicalInheritedDominationConstructed ≡ false
physicalInheritedDominationConstructedIsFalse = refl
