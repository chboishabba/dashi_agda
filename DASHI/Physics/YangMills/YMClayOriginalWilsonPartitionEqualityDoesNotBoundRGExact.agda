module DASHI.Physics.YangMills.YMClayOriginalWilsonPartitionEqualityDoesNotBoundRGExact where

-- P0.F exact adversarial control: finite interacting Haar disintegration
-- or equal partition functions NEVER by itself bounds the effective
-- coarse Wilson density by the bare Wilson density. Both normalized
-- measures can be strictly positive and have the SAME total mass.
--
-- Source analogy (not a substitute for the original SU(N) objects):
-- a two-point normalized Haar quadrature with effective densities
--       w_eff(+)=3/2, w_eff(-)=1/2
-- and bare densities
--       w_bare(+)=w_bare(-)=1
-- has Z_eff=Z_bare=1, while the effective interaction still differs
-- from the bare one by 1/2 at every cutoff.  No UV-decay follows.
--
-- The original YMClayOriginalWilsonPhysicalF19PartitionExact theorem
-- is stronger than a chosen-probability equality: it identifies a
-- genuine original 1024-link Wilson density under native blocking.
-- This example isolates why a NEW UNIFORM PHYSICAL ESTIMATE is needed
-- for its desired P0.F bound, even if the full partition identity
-- is kernel accepted.
--
-- All results here are exact rational arithmetic, with no axioms,
-- no postulates, and no claims about E1/D1/D2/N1/G1.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; _<_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Integer.Base using (+_)
open import Relation.Binary.PropositionalEquality using (_≢_)

bareDensity effectiveDensity : Bool → ℚ
bareDensity true = 1ℚ
bareDensity false = 1ℚ
effectiveDensity true = (+ 3 / 2)
effectiveDensity false = (+ 1 / 2)

twoPointHaarIntegral : (Bool → ℚ) → ℚ
twoPointHaarIntegral density =
  (density true + density false) * (+ 1 / 2)

bareAndEffectivePartitionsIdentical :
  twoPointHaarIntegral bareDensity
  ≡ twoPointHaarIntegral effectiveDensity
bareAndEffectivePartitionsIdentical = ℚRing.solve-∀

barePartitionIsOne :
  twoPointHaarIntegral bareDensity ≡ 1ℚ
barePartitionIsOne = ℚRing.solve-∀

effectivePartitionIsOne :
  twoPointHaarIntegral effectiveDensity ≡ 1ℚ
effectivePartitionIsOne = ℚRing.solve-∀

barePositive : ∀ sign → 0ℚ < bareDensity sign
barePositive true =
  let instance positive : Positive 1ℚ
      positive = ℚP.normalize-pos 1 1
  in ℚP.positive⁻¹ 1ℚ
barePositive false =
  let instance positive : Positive 1ℚ
      positive = ℚP.normalize-pos 1 1
  in ℚP.positive⁻¹ 1ℚ

effectivePositive : ∀ sign → 0ℚ < effectiveDensity sign
effectivePositive true =
  let instance positive : Positive (+ 3 / 2)
      positive = ℚP.normalize-pos 3 2
  in ℚP.positive⁻¹ (+ 3 / 2)
effectivePositive false =
  let instance positive : Positive (+ 1 / 2)
      positive = ℚP.normalize-pos 1 2
  in ℚP.positive⁻¹ (+ 1 / 2)

effectiveMinusBareAtPlusExact :
  effectiveDensity true - bareDensity true ≡ (+ 1 / 2)
effectiveMinusBareAtPlusExact = ℚRing.solve-∀

effectiveMinusBareAtMinusExact :
  bareDensity false - effectiveDensity false ≡ (+ 1 / 2)
effectiveMinusBareAtMinusExact = ℚRing.solve-∀

effectiveDensityNotBareAtPlus :
  effectiveDensity true ≢ bareDensity true
effectiveDensityNotBareAtPlus ()

-- Even an arbitrarily long sequence of exact equal-partition blocking
-- operations does not entail any decay toward the bare Wilson density:
-- the same strictly-positive counterexample can persist at every scale.
effectiveAtScale : Nat → Bool → ℚ
effectiveAtScale cutoff = effectiveDensity

scaleUniformFixedDefect :
  ∀ cutoff →
  effectiveAtScale cutoff true - bareDensity true ≡ (+ 1 / 2)
scaleUniformFixedDefect cutoff = effectiveMinusBareAtPlusExact

-- The theorem is a non-implication about the DATA supplied by partition
-- identities, not a refutation of P0.F's hoped-for physical estimate.
-- P0.F must exploit Wilson-specific cluster/covariance/spectral bounds.

-- P0.F asks for actual normalized marked moment control. Equality
-- of partition functions not only fails to control pointwise density:
-- it also fails for F, G and FG simultaneously, even when all are
-- nonconstant bounded tests under positive, normalized measures.

selectedNonconstantTest : Bool → ℚ
selectedNonconstantTest true = 1ℚ
selectedNonconstantTest false = 0ℚ

twoPointWeightedMarkedNumerator : (Bool → ℚ) → (Bool → ℚ) → ℚ
twoPointWeightedMarkedNumerator density observable =
  ((density true * observable true) + (density false * observable false))
    * (+ 1 / 2)

bareSelectedMomentExact :
  twoPointWeightedMarkedNumerator bareDensity selectedNonconstantTest
    ≡ (+ 1 / 2)
bareSelectedMomentExact = ℚRing.solve-∀

effectiveSelectedMomentExact :
  twoPointWeightedMarkedNumerator effectiveDensity selectedNonconstantTest
    ≡ (+ 3 / 4)
effectiveSelectedMomentExact = ℚRing.solve-∀

-- Both partition functions are exactly 1, so these are ALREADY
-- the normalized test expectations on the two-point Haar model.
fixedNormalizedMomentDefect :
  twoPointWeightedMarkedNumerator
    effectiveDensity selectedNonconstantTest
  -
  twoPointWeightedMarkedNumerator
    bareDensity selectedNonconstantTest
  ≡ (+ 1 / 4)
fixedNormalizedMomentDefect = ℚRing.solve-∀

selectedTestProductIsSame :
  ∀ sign →
  selectedNonconstantTest sign * selectedNonconstantTest sign
    ≡ selectedNonconstantTest sign
selectedTestProductIsSame true = ℚRing.solve-∀
selectedTestProductIsSame false = ℚRing.solve-∀

-- Choosing F=G=selectedNonconstantTest shows the same 1/4
-- defect for all three F,G,FG moment targets. No three-moment
-- contraction estimate follows from the exact same-partition weld.
threeMarkedMomentsDoNotDecayAtEveryScale :
  ∀ cutoff →
  twoPointWeightedMarkedNumerator
    (effectiveAtScale cutoff) selectedNonconstantTest
  -
  twoPointWeightedMarkedNumerator
    bareDensity selectedNonconstantTest
  ≡ (+ 1 / 4)
threeMarkedMomentsDoNotDecayAtEveryScale cutoff =
  fixedNormalizedMomentDefect
