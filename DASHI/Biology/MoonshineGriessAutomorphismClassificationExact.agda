module DASHI.Biology.MoonshineGriessAutomorphismClassificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Robert L. Griess Jr.,
-- "The Friendly Giant".
-- DOI: 10.1007/BF01389186.
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- Chongying Dong, Robert L. Griess Jr. and Ching Hung Lam,
-- "Uniqueness Results for the Moonshine Vertex Operator Algebra".
-- DOI: 10.1353/ajm.2007.0009.
--
-- DASHI CONTRIBUTION
--
-- Formalize two exact bridges explaining the role of the Griess algebra.
--
-- 1. A bijective multiplicative map of a unital commutative algebra fixes its
--    unit; preservation of the unit need not be postulated independently.
--
-- 2. A grading-preserving VOA automorphism that preserves the mode-one product
--    restricts to an automorphism of the weight-two Griess product.
--
-- We also record the normalization: for the raw product u star v = u_1 v on
-- V_2, omega star v = 2v, so the algebra unit is omega/2, not omega.  These
-- facts explain how the 196884-dimensional algebra gives a concrete Monster
-- construction and a faithful finite algebraic object for classification,
-- without claiming that this module constructs the Monster or completes its
-- classification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record UnitalCommutativeAlgebra : Set₁ where
  field
    Carrier : Set
    unit : Carrier
    multiply : Carrier → Carrier → Carrier
    leftIdentity : ∀ value → multiply unit value ≡ value
    commutative : ∀ left right →
      multiply left right ≡ multiply right left

open UnitalCommutativeAlgebra public

rightIdentity :
  (algebra : UnitalCommutativeAlgebra) →
  ∀ value → multiply algebra value (unit algebra) ≡ value
rightIdentity algebra value =
  trans
    (commutative algebra value (unit algebra))
    (leftIdentity algebra value)

record MultiplicativeBijection
    (algebra : UnitalCommutativeAlgebra) : Set where
  field
    map inverse : Carrier algebra → Carrier algebra
    mapMultiplicative : ∀ left right →
      map (multiply algebra left right)
      ≡ multiply algebra (map left) (map right)
    rightInverse : ∀ value → map (inverse value) ≡ value

open MultiplicativeBijection public

automorphismFixesUnit :
  (algebra : UnitalCommutativeAlgebra) →
  (automorphism : MultiplicativeBijection algebra) →
  map automorphism (unit algebra) ≡ unit algebra
automorphismFixesUnit algebra automorphism =
  let
    mappedUnitTimesUnit :
      multiply algebra
        (map automorphism (unit algebra))
        (unit algebra)
      ≡ unit algebra
    mappedUnitTimesUnit =
      trans
        (cong
          (multiply algebra (map automorphism (unit algebra)))
          (sym (rightInverse automorphism (unit algebra))))
        (trans
          (sym
            (mapMultiplicative automorphism
              (unit algebra)
              (inverse automorphism (unit algebra))))
          (trans
            (cong (map automorphism)
              (leftIdentity algebra
                (inverse automorphism (unit algebra))))
            (rightInverse automorphism (unit algebra))))
  in
  trans
    (sym (rightIdentity algebra (map automorphism (unit algebra))))
    mappedUnitTimesUnit

------------------------------------------------------------------------
-- Exact omega/2 normalization regression.
------------------------------------------------------------------------

rawOmegaFirstProduct : ℚ → ℚ
rawOmegaFirstProduct value = (+ 2 / 1) * value

halfOmegaActsAsUnit :
  (value : ℚ) →
  (+ 1 / 2) * rawOmegaFirstProduct value ≡ value
halfOmegaActsAsUnit value = solve (value ∷ [])

------------------------------------------------------------------------
-- Restriction of VOA automorphisms to the Griess product.
------------------------------------------------------------------------

record WeightTwoModeData : Set₁ where
  field
    WeightTwo : Set
    conformalVector : WeightTwo
    firstProduct : WeightTwo → WeightTwo → WeightTwo

open WeightTwoModeData public

record WeightTwoVOAAutomorphism (dataSet : WeightTwoModeData) : Set where
  field
    weightTwoMap weightTwoInverse :
      WeightTwo dataSet → WeightTwo dataSet
    leftInverse : ∀ value →
      weightTwoInverse (weightTwoMap value) ≡ value
    rightInverseWeightTwo : ∀ value →
      weightTwoMap (weightTwoInverse value) ≡ value
    conformalVectorFixed :
      weightTwoMap (conformalVector dataSet)
      ≡ conformalVector dataSet
    firstProductPreserved : ∀ left right →
      weightTwoMap (firstProduct dataSet left right)
      ≡ firstProduct dataSet
          (weightTwoMap left) (weightTwoMap right)

open WeightTwoVOAAutomorphism public

record GriessProductAutomorphism (dataSet : WeightTwoModeData) : Set where
  constructor griessProductAutomorphism
  field
    griessMap griessInverse :
      WeightTwo dataSet → WeightTwo dataSet
    griessLeftInverse : ∀ value →
      griessInverse (griessMap value) ≡ value
    griessRightInverse : ∀ value →
      griessMap (griessInverse value) ≡ value
    griessProductPreserved : ∀ left right →
      griessMap (firstProduct dataSet left right)
      ≡ firstProduct dataSet (griessMap left) (griessMap right)

restrictVOAAutomorphismToGriess :
  ∀ dataSet →
  WeightTwoVOAAutomorphism dataSet →
  GriessProductAutomorphism dataSet
restrictVOAAutomorphismToGriess dataSet automorphism =
  griessProductAutomorphism
    (weightTwoMap automorphism)
    (weightTwoInverse automorphism)
    (leftInverse automorphism)
    (rightInverseWeightTwo automorphism)
    (firstProductPreserved automorphism)

record GriessClassificationAuthorityBoundary : Set where
  constructor griessClassificationAuthorityBoundary
  field
    everyGriessAutomorphismExtendsToVOA : Set
    converseExtensionRequiresSeparateTheorem :
      everyGriessAutomorphismExtendsToVOA → Set

    finiteAlgebraLemmasClassifyMonster : Set
    finiteAlgebraLemmasDoNotClassifyMonster :
      finiteAlgebraLemmasClassifyMonster → Set

canonicalGriessClassificationAuthorityBoundary :
  GriessClassificationAuthorityBoundary
canonicalGriessClassificationAuthorityBoundary =
  griessClassificationAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
