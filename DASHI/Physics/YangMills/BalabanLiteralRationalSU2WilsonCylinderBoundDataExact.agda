{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact where

------------------------------------------------------------------------
-- CONCRETE WILSON-CYLINDER BOUND AUTHORITY FOR THE RATIONAL SU(2) CARRIER
--
-- Unlike the historical T5 `BoundedObservable` predicate, this bound is
-- quantitative and inspectable:
--
--   Bound F M := 0 <= M  ×  forall U, |F U| <= M.
--
-- Literal path Wilson observables have M=1; identity has M=1; multiplication
-- multiplies the majorants.  Hence the generic finite-product compiler can now
-- construct explicit bounds for every finite Wilson cylinder.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson

QuantitativeBound :
  ∀ {n} → Wilson.RationalWilsonObservable n → ℚ → Set
QuantitativeBound observable majorant =
  (0ℚ ≤ majorant)
  × (∀ configuration → ∣ observable configuration ∣ ≤ majorant)

quantitativeOneBound :
  ∀ {n} → QuantitativeBound (Wilson.oneObservable {n}) 1ℚ
quantitativeOneBound =
  Wilson.oneNonnegative , Wilson.oneObservablePointwiseUnitBounded

quantitativeWilsonPathBound :
  ∀ {n} (path : Wilson.RationalWilsonPath n) →
  QuantitativeBound (Wilson.literalWilsonPathObservable path) 1ℚ
quantitativeWilsonPathBound path =
  Wilson.oneNonnegative , Wilson.literalWilsonPathPointwiseUnitBounded path

multiplyMajorantNonnegative :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
multiplyMajorantNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = nonNegative leftNN

      rightNonnegative : NonNegative right
      rightNonnegative = nonNegative rightNN

      productNonnegative : NonNegative (left * right)
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

quantitativeMultiplyBound :
  ∀ {n}
    (left right : Wilson.RationalWilsonObservable n)
    leftBound rightBound →
  QuantitativeBound left leftBound →
  QuantitativeBound right rightBound →
  QuantitativeBound
    (Wilson.multiplyObservable left right)
    (leftBound * rightBound)
quantitativeMultiplyBound left right leftBound rightBound
    leftProof rightProof =
  multiplyMajorantNonnegative (proj₁ leftProof) (proj₁ rightProof)
  ,
  λ configuration →
    Wilson.absoluteProductBound
      (proj₂ leftProof configuration)
      (proj₂ rightProof configuration)
      (proj₁ leftProof)
      (proj₁ rightProof)

literalRationalSU2WilsonCylinderBounds :
  ∀ {n} →
  T5.WilsonCylinderBoundData
    (Wilson.RationalWilsonPath n)
    (Wilson.RationalWilsonObservable n)
    ℚ
literalRationalSU2WilsonCylinderBounds = record
  { T5.WilsonCylinderBoundData.loopObservable =
      Wilson.literalWilsonPathObservable
  ; T5.WilsonCylinderBoundData.multiplyObservable =
      Wilson.multiplyObservable
  ; T5.WilsonCylinderBoundData.identityObservable =
      Wilson.oneObservable
  ; T5.WilsonCylinderBoundData.Bound =
      QuantitativeBound
  ; T5.WilsonCylinderBoundData.one = 1ℚ
  ; T5.WilsonCylinderBoundData.groupRank = 1ℚ
  ; T5.WilsonCylinderBoundData.multiplyScalar = _*_
  ; T5.WilsonCylinderBoundData.wilsonLoopObservableUniformBound =
      quantitativeWilsonPathBound
  ; T5.WilsonCylinderBoundData.multiplyBound =
      quantitativeMultiplyBound
  ; T5.WilsonCylinderBoundData.identityBound =
      quantitativeOneBound
  }

finiteLiteralWilsonCylinderBound :
  ∀ {n} paths →
  QuantitativeBound
    (T5.productLoopObservable
      (literalRationalSU2WilsonCylinderBounds {n}) paths)
    (T5.productLoopBound
      (literalRationalSU2WilsonCylinderBounds {n}) paths)
finiteLiteralWilsonCylinderBound {n} paths =
  T5.finiteProductWilsonObservableUniformBound
    (literalRationalSU2WilsonCylinderBounds {n}) paths

literalRationalSU2WilsonCylinderBoundDataLevel : ProofLevel
literalRationalSU2WilsonCylinderBoundDataLevel = machineChecked
