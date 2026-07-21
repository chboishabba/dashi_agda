module DASHI.Algebra.Jacobian.CounterexampleRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Jacobian.CollisionImpliesNonInjective as Collision
import DASHI.Algebra.Jacobian.InvertibilityStrata as Strata
import DASHI.Algebra.Jacobian.FibreBranching as Fibre
import DASHI.Algebra.Jacobian.ThreeDimensionalCounterexample as Three

------------------------------------------------------------------------
-- A finite kernel regression exercises the logical promotion independently of
-- the external sparse-polynomial computation.

data WitnessPoint : Set where
  p₀ p₁ p₂ : WitnessPoint

data CommonImage : Set where
  q : CommonImage

witnessMap : WitnessPoint → CommonImage
witnessMap p₀ = q
witnessMap p₁ = q
witnessMap p₂ = q

p₀NotP₁ : Collision.Not (p₀ ≡ p₁)
p₀NotP₁ ()

p₀NotP₂ : Collision.Not (p₀ ≡ p₂)
p₀NotP₂ ()

p₁NotP₂ : Collision.Not (p₁ ≡ p₂)
p₁NotP₂ ()

canonicalTriple : Collision.ThreePointCollision witnessMap
canonicalTriple =
  record
    { Collision.first = p₀
    ; Collision.second = p₁
    ; Collision.third = p₂
    ; Collision.firstSecondDistinct = p₀NotP₁
    ; Collision.firstThirdDistinct = p₀NotP₂
    ; Collision.secondThirdDistinct = p₁NotP₂
    ; Collision.firstSecondImage = refl
    ; Collision.firstThirdImage = refl
    }

kernelNoninjectivityRegression :
  Collision.Not (Collision.Injective witnessMap)
kernelNoninjectivityRegression =
  Collision.threePointCollisionImpliesNonInjective canonicalTriple

localDoesNotPromoteGlobal :
  Strata.localImpliesGlobalInverse Strata.canonicalPromotionBoundary ≡ false
localDoesNotPromoteGlobal = refl

imageDoesNotSelectUniqueSource :
  Fibre.imageDeterminesUniqueSource Fibre.canonicalReconstructionBoundary ≡ false
imageDoesNotSelectUniqueSource = refl

dimensionTwoRemainsOpen :
  Three.dimensionTwoResolved Three.canonicalCounterexampleReceipt ≡ false
dimensionTwoRemainsOpen = refl

logicalKernelPromotionPresent :
  Three.collisionImpliesNoninjectiveKernelProved Three.canonicalKernelStatus ≡ true
logicalKernelPromotionPresent = refl

polynomialExpansionStillExternal :
  Three.sparsePolynomialExpansionKernelChecked Three.canonicalKernelStatus ≡ false
polynomialExpansionStillExternal = refl
