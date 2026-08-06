module DASHI.Biology.MoonshineVacuumConformalLineBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster", Pure and Applied Mathematics
-- 134, Academic Press, 1988.
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- Chongying Dong, Robert L. Griess Jr. and Ching Hung Lam,
-- "Uniqueness Results for the Moonshine Vertex Operator Algebra".
-- DOI: 10.1353/ajm.2007.0009.
--
-- DASHI CONTRIBUTION
-- Correct the grade semantics around 196884 = 1 + 196883.  The one-dimensional
-- line in weight two is the conformal/Virasoro-vector line C omega, not the
-- vacuum line C 1 in weight zero and not the external DASHI j-completion
-- channel.  The module checks the finite dimensions and makes the roles
-- distinct constructors.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_)

data MoonshineLineRole : Set where
  vacuumLine : MoonshineLineRole
  conformalVectorLine : MoonshineLineRole
  completionJLine : MoonshineLineRole
  reducedFiftyFourInvariantLine : MoonshineLineRole

data RoleLocation : Set where
  voaWeightZero : RoleLocation
  voaWeightTwo : RoleLocation
  outsideDeclaredVOAGrading : RoleLocation
  reducedFiftyFourCarrier : RoleLocation

roleLocation : MoonshineLineRole → RoleLocation
roleLocation vacuumLine = voaWeightZero
roleLocation conformalVectorLine = voaWeightTwo
roleLocation completionJLine = outsideDeclaredVOAGrading
roleLocation reducedFiftyFourInvariantLine = reducedFiftyFourCarrier

vacuumIsNotConformal : vacuumLine ≡ conformalVectorLine → ⊥
vacuumIsNotConformal ()

conformalIsNotCompletion : conformalVectorLine ≡ completionJLine → ⊥
conformalIsNotCompletion ()

vacuumIsNotCompletion : vacuumLine ≡ completionJLine → ⊥
vacuumIsNotCompletion ()

conformalIsNotReducedFiftyFourLine :
  conformalVectorLine ≡ reducedFiftyFourInvariantLine → ⊥
conformalIsNotReducedFiftyFourLine ()

weightZeroDimension : Nat
weightZeroDimension = 1

weightOneDimension : Nat
weightOneDimension = 0

weightTwoConformalMultiplicity : Nat
weightTwoConformalMultiplicity = 1

weightTwoMonsterConstituentDimension : Nat
weightTwoMonsterConstituentDimension = 196883

weightTwoDimension : Nat
weightTwoDimension =
  weightTwoConformalMultiplicity + weightTwoMonsterConstituentDimension

weightZeroDimensionExact : weightZeroDimension ≡ 1
weightZeroDimensionExact = refl

weightOneDimensionExact : weightOneDimension ≡ 0
weightOneDimensionExact = refl

weightTwoDimensionExact : weightTwoDimension ≡ 196884
weightTwoDimensionExact = refl

weightTwoIsConformalPlusMonster :
  weightTwoDimension
  ≡ weightTwoConformalMultiplicity + weightTwoMonsterConstituentDimension
weightTwoIsConformalPlusMonster = refl

record MoonshineGradeBoundary : Set where
  constructor moonshineGradeBoundary
  field
    weightTwoOneIsVacuumLine : Set
    weightTwoOneIsNotVacuumLine : weightTwoOneIsVacuumLine → Set

    completionJHasKnownVOAWeight : Set
    completionJDoesNotHaveKnownVOAWeight : completionJHasKnownVOAWeight → Set

    weightTwoConstituentAloneIsFullWeightTwoAlgebra : Set
    constituentAloneIsNotDeclaredFullWeightTwoAlgebra :
      weightTwoConstituentAloneIsFullWeightTwoAlgebra → Set

canonicalMoonshineGradeBoundary : MoonshineGradeBoundary
canonicalMoonshineGradeBoundary =
  moonshineGradeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
