module DASHI.Physics.YangMills.BalabanStrongCouplingWeightedWassersteinRateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- SOURCE FORMULAS
--
-- Assumption 1.1 uses the direct Bakry--Emery rate
--
--   K_S = C_Ric,N - 8 N |beta| (d-1).
--
-- Lemma 5.1 and equation (5.15) use the different weighted-Wasserstein
-- contraction rate
--
--   K~_S(a) = C_Ric,N - (4 + 4 sqrt(a)) N |beta| (d-1),  a > 1.
--
-- Writing s=sqrt(a), their exact relation is
--
--   K~_S(s^2) = K_S - 4(s-1)N|beta|(d-1).
--
-- DASHI CONTRIBUTION
--
-- Prove this relation over exact rationals for both SO and SU families.  Give a
-- constructive rational weight choice: if an inverse of
--
--   4 N |beta| (d-1)
--
-- is supplied, choose
--
--   s = 1 + (K_S/2) / (4 N |beta| (d-1)).
--
-- The resulting weighted rate is exactly K_S/2.  Positivity is derived from
-- positivity of K_S and the inverse scale, rather than inserted as a separate
-- weighted-rate receipt.  A concrete SU(2), d=4, |beta|=1/96 regression uses
-- s=2, a=4 and obtains K~_S=1/4.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; _<_; Positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.YangMills.BalabanStrongCouplingGroupRicciConstantsExact as Group

weightedDistanceParameter : ℚ → ℚ
weightedDistanceParameter weightSqrt = weightSqrt * weightSqrt

weightedWassersteinRate :
  Group.ClassicalGaugeFamily → ℚ → ℚ → ℚ → ℚ → ℚ
weightedWassersteinRate family rankN betaMagnitude dMinusOne weightSqrt =
  Group.ricciConstant family rankN
    - ((+ 4 / 1) + (+ 4 / 1) * weightSqrt)
        * rankN * betaMagnitude * dMinusOne

weightLoss : ℚ → ℚ → ℚ → ℚ → ℚ
weightLoss rankN betaMagnitude dMinusOne weightSqrt =
  (+ 4 / 1) * (weightSqrt - 1ℚ)
    * rankN * betaMagnitude * dMinusOne

weightedRateIsBakryRateMinusWeightLoss :
  ∀ family rankN betaMagnitude dMinusOne weightSqrt →
  weightedWassersteinRate
    family rankN betaMagnitude dMinusOne weightSqrt
  ≡ Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
      - weightLoss rankN betaMagnitude dMinusOne weightSqrt
weightedRateIsBakryRateMinusWeightLoss
    family rankN betaMagnitude dMinusOne weightSqrt =
  solve (Group.ricciConstant family rankN
    ∷ rankN ∷ betaMagnitude ∷ dMinusOne ∷ weightSqrt ∷ [])

interactionScale : ℚ → ℚ → ℚ → ℚ
interactionScale rankN betaMagnitude dMinusOne =
  (+ 4 / 1) * rankN * betaMagnitude * dMinusOne

canonicalWeightSqrt : ℚ → ℚ → ℚ
canonicalWeightSqrt bakryRate inverseInteractionScale =
  1ℚ + (+ 1 / 2) * bakryRate * inverseInteractionScale

canonicalWeightParameter : ℚ → ℚ → ℚ
canonicalWeightParameter bakryRate inverseInteractionScale =
  weightedDistanceParameter
    (canonicalWeightSqrt bakryRate inverseInteractionScale)

canonicalWeightIncrementExact :
  ∀ bakryRate inverseInteractionScale →
  canonicalWeightSqrt bakryRate inverseInteractionScale - 1ℚ
  ≡ (+ 1 / 2) * bakryRate * inverseInteractionScale
canonicalWeightIncrementExact bakryRate inverseInteractionScale =
  solve (bakryRate ∷ inverseInteractionScale ∷ [])

canonicalWeightedRateFactored :
  ∀ family rankN betaMagnitude dMinusOne inverseInteractionScale →
  weightedWassersteinRate
    family rankN betaMagnitude dMinusOne
    (canonicalWeightSqrt
      (Group.bakryEmeryRate family rankN betaMagnitude dMinusOne)
      inverseInteractionScale)
  ≡ Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
      - (+ 1 / 2)
        * Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
        * (inverseInteractionScale
          * interactionScale rankN betaMagnitude dMinusOne)
canonicalWeightedRateFactored
    family rankN betaMagnitude dMinusOne inverseInteractionScale =
  solve
    ( Group.ricciConstant family rankN
    ∷ rankN ∷ betaMagnitude ∷ dMinusOne
    ∷ inverseInteractionScale ∷ [])

canonicalWeightedRateIsHalfBakry :
  ∀ family rankN betaMagnitude dMinusOne inverseInteractionScale →
  inverseInteractionScale
    * interactionScale rankN betaMagnitude dMinusOne
  ≡ 1ℚ →
  weightedWassersteinRate
    family rankN betaMagnitude dMinusOne
    (canonicalWeightSqrt
      (Group.bakryEmeryRate family rankN betaMagnitude dMinusOne)
      inverseInteractionScale)
  ≡ (+ 1 / 2)
      * Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
canonicalWeightedRateIsHalfBakry
    family rankN betaMagnitude dMinusOne inverseInteractionScale inverseLaw =
  trans
    (canonicalWeightedRateFactored
      family rankN betaMagnitude dMinusOne inverseInteractionScale)
    (subst
      (λ selected →
        Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
          - (+ 1 / 2)
            * Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
            * selected
        ≡ (+ 1 / 2)
            * Group.bakryEmeryRate family rankN betaMagnitude dMinusOne)
      (sym inverseLaw)
      (solve
        (Group.bakryEmeryRate family rankN betaMagnitude dMinusOne ∷ [])))

record PositiveWeightSelection
    (family : Group.ClassicalGaugeFamily)
    (rankN betaMagnitude dMinusOne : ℚ) : Set where
  constructor positiveWeightSelection
  field
    selectedWeightSqrt : ℚ
    selectedWeightParameter : ℚ
    parameterIsSquare :
      selectedWeightParameter
      ≡ weightedDistanceParameter selectedWeightSqrt
    weightIncrementPositive : 0ℚ < selectedWeightSqrt - 1ℚ
    weightedRatePositive :
      0ℚ < weightedWassersteinRate
        family rankN betaMagnitude dMinusOne selectedWeightSqrt

open PositiveWeightSelection public

positiveBakryRateChoosesPositiveWeight :
  ∀ family rankN betaMagnitude dMinusOne inverseInteractionScale →
  .{{Positive
      (Group.bakryEmeryRate family rankN betaMagnitude dMinusOne)}} →
  .{{Positive inverseInteractionScale}} →
  inverseInteractionScale
    * interactionScale rankN betaMagnitude dMinusOne
  ≡ 1ℚ →
  PositiveWeightSelection family rankN betaMagnitude dMinusOne
positiveBakryRateChoosesPositiveWeight
    family rankN betaMagnitude dMinusOne inverseInteractionScale inverseLaw =
  let
    bakry = Group.bakryEmeryRate family rankN betaMagnitude dMinusOne
    selected = canonicalWeightSqrt bakry inverseInteractionScale
    parameter = weightedDistanceParameter selected

    instance
      halfPositive : Positive (+ 1 / 2)
      halfPositive = ℚP.normalize-pos 1 2

      bakryTimesInversePositive : Positive (bakry * inverseInteractionScale)
      bakryTimesInversePositive =
        ℚP.pos*pos⇒pos bakry inverseInteractionScale

      incrementPositive :
        Positive ((+ 1 / 2) * (bakry * inverseInteractionScale))
      incrementPositive =
        ℚP.pos*pos⇒pos (+ 1 / 2) (bakry * inverseInteractionScale)

      halfBakryPositive : Positive ((+ 1 / 2) * bakry)
      halfBakryPositive = ℚP.pos*pos⇒pos (+ 1 / 2) bakry

    incrementOrder :
      0ℚ < (+ 1 / 2) * bakry * inverseInteractionScale
    incrementOrder =
      subst
        (λ chosen → 0ℚ < chosen)
        (solve (bakry ∷ inverseInteractionScale ∷ []))
        (ℚP.positive⁻¹ ((+ 1 / 2) * (bakry * inverseInteractionScale)))

    selectedIncrementPositive : 0ℚ < selected - 1ℚ
    selectedIncrementPositive =
      subst
        (λ chosen → 0ℚ < chosen)
        (sym (canonicalWeightIncrementExact bakry inverseInteractionScale))
        incrementOrder

    selectedRatePositive :
      0ℚ < weightedWassersteinRate
        family rankN betaMagnitude dMinusOne selected
    selectedRatePositive =
      subst
        (λ chosen → 0ℚ < chosen)
        (sym
          (canonicalWeightedRateIsHalfBakry
            family rankN betaMagnitude dMinusOne
            inverseInteractionScale inverseLaw))
        (ℚP.positive⁻¹ ((+ 1 / 2) * bakry))
  in
  positiveWeightSelection
    selected parameter refl
    selectedIncrementPositive selectedRatePositive

configuredWeightSqrt : ℚ
configuredWeightSqrt = + 2 / 1

configuredWeightParameter : ℚ
configuredWeightParameter = weightedDistanceParameter configuredWeightSqrt

configuredWeightParameterExact :
  configuredWeightParameter ≡ + 4 / 1
configuredWeightParameterExact = solve []

configuredSU2WeightedContractionRateExact :
  weightedWassersteinRate
    Group.specialUnitaryFamily
    (+ 2 / 1) (+ 1 / 96) (+ 3 / 1)
    configuredWeightSqrt
  ≡ + 1 / 4
configuredSU2WeightedContractionRateExact = solve []

configuredInteractionScaleInverse : ℚ
configuredInteractionScaleInverse = + 4 / 1

configuredInteractionScaleInverseLaw :
  configuredInteractionScaleInverse
    * interactionScale (+ 2 / 1) (+ 1 / 96) (+ 3 / 1)
  ≡ 1ℚ
configuredInteractionScaleInverseLaw = solve []

configuredCanonicalWeightSqrtExact :
  canonicalWeightSqrt
    (Group.bakryEmeryRate
      Group.specialUnitaryFamily
      (+ 2 / 1) (+ 1 / 96) (+ 3 / 1))
    configuredInteractionScaleInverse
  ≡ configuredWeightSqrt
configuredCanonicalWeightSqrtExact = solve []
