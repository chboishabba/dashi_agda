module DASHI.Physics.YangMills.BalabanSU2RationalAdjointRadiusExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact
  using
    ( RationalUnitQuaternion
    ; realPart; imagI; imagJ; imagK; unitNormExact
    ; squareℚ; quaternionNormSq
    )

------------------------------------------------------------------------
-- Literal rational adjoint rotation.
------------------------------------------------------------------------

record RationalVec3 : Set where
  constructor rationalVec3
  field
    x y z : ℚ

open RationalVec3 public

twoℚ fourℚ : ℚ
twoℚ = 1ℚ + 1ℚ
fourℚ = twoℚ * twoℚ

row00 row01 row02 row10 row11 row12 row20 row21 row22 :
  RationalUnitQuaternion → ℚ
row00 q =
  squareℚ (realPart q) + squareℚ (imagI q)
  - squareℚ (imagJ q) - squareℚ (imagK q)
row01 q = twoℚ * (imagI q * imagJ q - realPart q * imagK q)
row02 q = twoℚ * (imagI q * imagK q + realPart q * imagJ q)
row10 q = twoℚ * (imagI q * imagJ q + realPart q * imagK q)
row11 q =
  squareℚ (realPart q) - squareℚ (imagI q)
  + squareℚ (imagJ q) - squareℚ (imagK q)
row12 q = twoℚ * (imagJ q * imagK q - realPart q * imagI q)
row20 q = twoℚ * (imagI q * imagK q - realPart q * imagJ q)
row21 q = twoℚ * (imagJ q * imagK q + realPart q * imagI q)
row22 q =
  squareℚ (realPart q) - squareℚ (imagI q)
  - squareℚ (imagJ q) + squareℚ (imagK q)

rotateX rotateY rotateZ : RationalUnitQuaternion → RationalVec3 → ℚ
rotateX q v = row00 q * x v + row01 q * y v + row02 q * z v
rotateY q v = row10 q * x v + row11 q * y v + row12 q * z v
rotateZ q v = row20 q * x v + row21 q * y v + row22 q * z v

rotate : RationalUnitQuaternion → RationalVec3 → RationalVec3
rotate q v = rationalVec3 (rotateX q v) (rotateY q v) (rotateZ q v)

vectorNormSq : RationalVec3 → ℚ
vectorNormSq v = squareℚ (x v) + squareℚ (y v) + squareℚ (z v)

imaginaryNormSq : RationalUnitQuaternion → ℚ
imaginaryNormSq q =
  squareℚ (imagI q) + squareℚ (imagJ q) + squareℚ (imagK q)

imaginaryDot : RationalUnitQuaternion → RationalVec3 → ℚ
imaginaryDot q v = imagI q * x v + imagJ q * y v + imagK q * z v

unitDefect : RationalUnitQuaternion → ℚ
unitDefect q = quaternionNormSq q - 1ℚ

adjointDisplacementSq : RationalUnitQuaternion → RationalVec3 → ℚ
adjointDisplacementSq q v =
  squareℚ (rotateX q v - x v)
  + squareℚ (rotateY q v - y v)
  + squareℚ (rotateZ q v - z v)

adjointMain : RationalUnitQuaternion → RationalVec3 → ℚ
adjointMain q v =
  fourℚ *
    (imaginaryNormSq q * vectorNormSq v
      - squareℚ (imaginaryDot q v))

------------------------------------------------------------------------
-- Exact polynomial identities, including the off-unit defect term.
------------------------------------------------------------------------

adjointDisplacementWithUnitDefectExact : ∀ q v →
  adjointDisplacementSq q v
  ≡ adjointMain q v
    + squareℚ (unitDefect q) * vectorNormSq v
adjointDisplacementWithUnitDefectExact q v =
  ℚRing.solve-∀

unitDefectVanishes : ∀ q → unitDefect q ≡ 0ℚ
unitDefectVanishes q =
  trans
    (cong (λ normValue → normValue - 1ℚ) (unitNormExact q))
    (ℚRing.solve-∀)

adjointDisplacementUnitExact : ∀ q v →
  adjointDisplacementSq q v ≡ adjointMain q v
adjointDisplacementUnitExact q v =
  trans
    (adjointDisplacementWithUnitDefectExact q v)
    (trans
      (cong
        (λ defect → adjointMain q v + squareℚ defect * vectorNormSq v)
        (unitDefectVanishes q))
      (ℚRing.solve-∀))

adjointMainPlusDiscardedSquareExact : ∀ q v →
  adjointMain q v + fourℚ * squareℚ (imaginaryDot q v)
  ≡ fourℚ * (imaginaryNormSq q * vectorNormSq v)
adjointMainPlusDiscardedSquareExact q v =
  ℚRing.solve-∀

adjointDisplacementPlusDiscardedSquareExact : ∀ q v →
  adjointDisplacementSq q v
    + fourℚ * squareℚ (imaginaryDot q v)
  ≡ fourℚ * (imaginaryNormSq q * vectorNormSq v)
adjointDisplacementPlusDiscardedSquareExact q v =
  trans
    (cong
      (λ displacement → displacement
        + fourℚ * squareℚ (imaginaryDot q v))
      (adjointDisplacementUnitExact q v))
    (adjointMainPlusDiscardedSquareExact q v)

------------------------------------------------------------------------
-- Ordered small-radius consequence.
------------------------------------------------------------------------

record RationalAdjointRadiusOrder : Set₁ where
  field
    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    baseBelowBasePlusNonnegative : ∀ base remainder →
      0ℚ ≤ remainder → base ≤ base + remainder
    discardedSquareNonnegative : ∀ q v →
      0ℚ ≤ fourℚ * squareℚ (imaginaryDot q v)
    scaleImaginaryMonotone : ∀ {left right} v →
      left ≤ right →
      fourℚ * (left * vectorNormSq v)
      ≤ fourℚ * (right * vectorNormSq v)

open RationalAdjointRadiusOrder public

adjointDisplacementBelowImaginaryRadius :
  (order : RationalAdjointRadiusOrder) → ∀ q v →
  adjointDisplacementSq q v
  ≤ fourℚ * (imaginaryNormSq q * vectorNormSq v)
adjointDisplacementBelowImaginaryRadius order q v =
  subst
    (λ right → adjointDisplacementSq q v ≤ right)
    (adjointDisplacementPlusDiscardedSquareExact q v)
    (baseBelowBasePlusNonnegative order
      (adjointDisplacementSq q v)
      (fourℚ * squareℚ (imaginaryDot q v))
      (discardedSquareNonnegative order q v))

adjointDisplacementRadiusBound :
  (order : RationalAdjointRadiusOrder) →
  ∀ q v radius →
  imaginaryNormSq q ≤ squareℚ radius →
  adjointDisplacementSq q v
  ≤ fourℚ * (squareℚ radius * vectorNormSq v)
adjointDisplacementRadiusBound order q v radius radiusBound =
  transitive order
    (adjointDisplacementBelowImaginaryRadius order q v)
    (scaleImaginaryMonotone order v radiusBound)

su2RationalAdjointDisplacementIdentityLevel : ProofLevel
su2RationalAdjointDisplacementIdentityLevel = machineChecked

su2RationalAdjointRadiusReductionLevel : ProofLevel
su2RationalAdjointRadiusReductionLevel = machineChecked

su2PhysicalLinkRadiusProducerLevel : ProofLevel
su2PhysicalLinkRadiusProducerLevel = conditional
