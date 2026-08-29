module DASHI.Physics.YangMills.BalabanMarkedReplacementMultiplicityAbsorptionExact where

------------------------------------------------------------------------
-- ROUND72: REPLACEMENT-POSITION MULTIPLICITY RETAINS POSITIVE TREE DECAY
--
-- SOURCE CALIBRATION
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- CMP 109 (1987), 249--301. DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", CMP 116(1) (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- DASHI CONTRIBUTION
--
-- The noncommutative marked product telescope has one summand per possible
-- replacement position.  If a tree with n factors has dyadic ordinary decay
-- (1/2)^n, this introduces at worst n copies.  Prove exactly
--
--       n (1/2)^n <= 2 (3/4)^n.
--
-- Therefore summing over the marked factor cannot destroy exponential tree
-- localization: it only weakens the geometric rate 1/2 -> 3/4 and costs the
-- finite constant 2.  The discrepancy-distance factor carried by the one
-- marked term is untouched.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Weighted
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half : ℚ
half = + 1 / 2

two : ℚ
two = + 2 / 1

halfNonnegative : 0ℚ ≤ half
halfNonnegative = Geo.halfNonnegative

twoNonnegative : 0ℚ ≤ two
twoNonnegative =
  let
    instance
      selected : NonNegative two
      selected = ℚP.normalize-nonNeg 2 1
  in
  ℚP.nonNegative⁻¹ two

halfBelowThreeQuarters : half ≤ Weighted.threeQuarters
halfBelowThreeQuarters =
  let
    slack = Weighted.threeQuarters - half
    slackNonnegative : 0ℚ ≤ slack
    slackNonnegative =
      let
        instance
          selected : NonNegative slack
          selected = ℚP.normalize-nonNeg 1 4
      in
      ℚP.nonNegative⁻¹ slack

    shifted : half + 0ℚ ≤ half + slack
    shifted = ℚP.+-mono-≤ ℚP.≤-refl slackNonnegative
  in
  subst
    (λ right → half ≤ right)
    (ℚRing.solve [])
    (subst
      (λ left → left ≤ half + slack)
      (sym (ℚP.+-identityʳ half))
      shifted)

halfPowerBelowThreeQuarterPower : ∀ n →
  Geo.halfPower n ≤ Weighted.threeQuartersPower n
halfPowerBelowThreeQuarterPower zero = ℚP.≤-refl
halfPowerBelowThreeQuarterPower (suc n) =
  let
    induction = halfPowerBelowThreeQuarterPower n

    scaledHalf :
      half * Geo.halfPower n
      ≤ half * Weighted.threeQuartersPower n
    scaledHalf = Norm.scaleNonnegative half halfNonnegative induction

    scaledBaseRaw :
      Weighted.threeQuartersPower n * half
      ≤ Weighted.threeQuartersPower n * Weighted.threeQuarters
    scaledBaseRaw = Norm.scaleNonnegative
      (Weighted.threeQuartersPower n)
      (Weighted.threeQuartersPowerNonnegative n)
      halfBelowThreeQuarters

    scaledBase :
      half * Weighted.threeQuartersPower n
      ≤ Weighted.threeQuartersPower n * Weighted.threeQuarters
    scaledBase =
      subst
        (λ left → left
          ≤ Weighted.threeQuartersPower n * Weighted.threeQuarters)
        (ℚRing.solve-∀ (Weighted.threeQuartersPower n))
        scaledBaseRaw
  in
  ℚP.≤-trans scaledHalf scaledBase

replacementMultiplicityCost : Nat → ℚ
replacementMultiplicityCost n =
  Sums.natAsRational n * Geo.halfPower n

replacementMultiplicityAbsorbed : ∀ n →
  replacementMultiplicityCost n
  ≤ two * Weighted.threeQuartersPower n
replacementMultiplicityAbsorbed zero =
  subst
    (λ right → 0ℚ ≤ right)
    (ℚRing.solve [])
    twoNonnegative
replacementMultiplicityAbsorbed (suc n) =
  let
    induction = replacementMultiplicityAbsorbed n

    halfScaledInduction :
      half * replacementMultiplicityCost n
      ≤ half * (two * Weighted.threeQuartersPower n)
    halfScaledInduction = Norm.scaleNonnegative
      half halfNonnegative induction

    powerComparison = halfPowerBelowThreeQuarterPower n
    halfScaledPower :
      half * Geo.halfPower n
      ≤ half * Weighted.threeQuartersPower n
    halfScaledPower = Norm.scaleNonnegative
      half halfNonnegative powerComparison

    combined :
      half * Geo.halfPower n
        + half * replacementMultiplicityCost n
      ≤
      half * Weighted.threeQuartersPower n
        + half * (two * Weighted.threeQuartersPower n)
    combined = ℚP.+-mono-≤ halfScaledPower halfScaledInduction

    normalized :
      replacementMultiplicityCost (suc n)
      ≤ two * Weighted.threeQuartersPower (suc n)
    normalized =
      subst
        (λ left → left ≤ two * Weighted.threeQuartersPower (suc n))
        (ℚRing.solve-∀
          (Sums.natAsRational n)
          (Geo.halfPower n))
        (subst
          (λ right →
            half * Geo.halfPower n
              + half * replacementMultiplicityCost n
            ≤ right)
          (ℚRing.solve-∀ (Weighted.threeQuartersPower n))
          combined)
  in
  normalized

markedReplacementMultiplicityAbsorptionLevel : ProofLevel
markedReplacementMultiplicityAbsorptionLevel = machineChecked

-- Physical seam: relate the number of replaceable factors in each actual
-- CMP109 differentiated tree term to the tree-length index used by the dyadic
-- coarsening.  Once factorCount <= treeLength is established source-natively,
-- the theorem above absorbs the entire telescope multiplicity while retaining
-- a positive 3/4 tree rate.
physicalCMP109FactorCountBelowTreeLengthLevel : ProofLevel
physicalCMP109FactorCountBelowTreeLengthLevel = conditional
