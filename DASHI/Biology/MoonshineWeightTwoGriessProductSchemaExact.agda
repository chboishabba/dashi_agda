module DASHI.Biology.MoonshineWeightTwoGriessProductSchemaExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Robert L. Griess Jr.,
-- "The Friendly Giant".
-- DOI: 10.1007/BF01389186.
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- Chongying Dong, Robert L. Griess Jr. and Ching Hung Lam,
-- "Uniqueness Results for the Moonshine Vertex Operator Algebra".
-- DOI: 10.1353/ajm.2007.0009.
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- DASHI CONTRIBUTION
-- Keep the first-product/Griess structure on the full 196884-dimensional
-- weight-two carrier C omega plus the 196883-dimensional Monster constituent.
-- The exact mode-grade closure u_1 v in V_2 is imported.  No concrete product,
-- Jacobi identity, invariant bilinear form or Monster action is fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)

import DASHI.Biology.FiniteGradedModeCarrierExact as Mode
import DASHI.Biology.MoonshineVacuumConformalLineBoundaryExact as Grade

data WeightTwoCoordinate : Set where
  conformalCoordinate : WeightTwoCoordinate
  monsterCoordinate : Fin 196883 → WeightTwoCoordinate

fullWeightTwoDimension : Nat
fullWeightTwoDimension = 1 + 196883

fullWeightTwoDimensionExact : fullWeightTwoDimension ≡ 196884
fullWeightTwoDimensionExact = refl

monsterConstituentDimension : Nat
monsterConstituentDimension = 196883

weightTwoFirstProductGradeCertificate : Mode.ModeGradeCertificate
weightTwoFirstProductGradeCertificate = Mode.weightTwoFirstModeClosure

weightTwoFirstProductClosesInWeightTwo :
  Mode.outputWeight weightTwoFirstProductGradeCertificate ≡ 2
weightTwoFirstProductClosesInWeightTwo = refl

record FullWeightTwoFirstProductSchema : Set₁ where
  constructor fullWeightTwoFirstProductSchema
  field
    Carrier : Set
    conformalVector : Carrier
    firstProduct : Carrier → Carrier → Carrier
    commutative :
      ∀ left right →
      firstProduct left right ≡ firstProduct right left

open FullWeightTwoFirstProductSchema public

data GriessProductDomain : Set where
  fullWeightTwoSpace : GriessProductDomain
  monsterConstituentOnly : GriessProductDomain

literatureGriessProductDomain : GriessProductDomain
literatureGriessProductDomain = fullWeightTwoSpace

record GriessProductBoundary : Set where
  constructor griessProductBoundary
  field
    constituentOnlyIsDeclaredFullGriessAlgebra : Set
    constituentOnlyIsNotDeclaredFullGriessAlgebra :
      constituentOnlyIsDeclaredFullGriessAlgebra → Set

    concreteFirstProductConstructed : Set
    concreteFirstProductNotConstructed : concreteFirstProductConstructed → Set

    monsterActionByVOAAutomorphismsConstructed : Set
    monsterActionNotConstructed :
      monsterActionByVOAAutomorphismsConstructed → Set

canonicalGriessProductBoundary : GriessProductBoundary
canonicalGriessProductBoundary =
  griessProductBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)

weightTwoDimensionAgreesWithGradeBoundary :
  fullWeightTwoDimension ≡ Grade.weightTwoDimension
weightTwoDimensionAgreesWithGradeBoundary = refl
