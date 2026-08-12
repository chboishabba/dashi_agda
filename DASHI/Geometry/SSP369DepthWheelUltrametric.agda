module DASHI.Geometry.SSP369DepthWheelUltrametric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_∸_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Foundations.SSPPrimeLaneUnitAction as Action
import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel as Wheel

------------------------------------------------------------------------
-- The existing refinement tree and existing 369 ultrametric use different
-- depth-indexed address types.  Give the bridge explicitly rather than
-- identifying them by name.

refDigitToMetricDigit : Ref.Lane369Digit → U369.Digit369
refDigitToMetricDigit Ref.digit-3 = U369.digit3
refDigitToMetricDigit Ref.digit-6 = U369.digit6
refDigitToMetricDigit Ref.digit-9 = U369.digit9

snocVec :
  ∀ {A : Set} {n : Nat} →
  Vec A n → A → Vec A (suc n)
snocVec [] value = value ∷ []
snocVec (x ∷ xs) value = x ∷ snocVec xs value

refAddressToMetricAddress :
  ∀ {d : Nat} →
  Ref.Lane369Address d → U369.Address d
refAddressToMetricAddress Ref.root = []
refAddressToMetricAddress (Ref.extend path digit) =
  snocVec
    (refAddressToMetricAddress path)
    (refDigitToMetricDigit digit)

------------------------------------------------------------------------
-- Corresponding C3 wheel on the metric carrier.

rotateMetricDigitOnce : U369.Digit369 → U369.Digit369
rotateMetricDigitOnce U369.digit3 = U369.digit6
rotateMetricDigitOnce U369.digit6 = U369.digit9
rotateMetricDigitOnce U369.digit9 = U369.digit3

rotateMetricDigitThree :
  (digit : U369.Digit369) →
  rotateMetricDigitOnce
    (rotateMetricDigitOnce
      (rotateMetricDigitOnce digit))
  ≡ digit
rotateMetricDigitThree U369.digit3 = refl
rotateMetricDigitThree U369.digit6 = refl
rotateMetricDigitThree U369.digit9 = refl

refDigitRotationCommutesWithAdapter :
  (digit : Ref.Lane369Digit) →
  refDigitToMetricDigit (Action.rotateLane369DigitOnce digit)
  ≡ rotateMetricDigitOnce (refDigitToMetricDigit digit)
refDigitRotationCommutesWithAdapter Ref.digit-3 = refl
refDigitRotationCommutesWithAdapter Ref.digit-6 = refl
refDigitRotationCommutesWithAdapter Ref.digit-9 = refl

rotateMetricAddress :
  ∀ {d : Nat} →
  U369.Address d → U369.Address d
rotateMetricAddress [] = []
rotateMetricAddress (digit ∷ rest) =
  rotateMetricDigitOnce digit ∷ rotateMetricAddress rest

rotateMetricAddressThree :
  ∀ {d : Nat} (address : U369.Address d) →
  rotateMetricAddress
    (rotateMetricAddress
      (rotateMetricAddress address))
  ≡ address
rotateMetricAddressThree [] = refl
rotateMetricAddressThree (digit ∷ rest)
  rewrite rotateMetricDigitThree digit
        | rotateMetricAddressThree rest = refl

rotateMetricAddressSnoc :
  ∀ {d : Nat}
    (address : U369.Address d)
    (digit : U369.Digit369) →
  rotateMetricAddress (snocVec address digit)
  ≡ snocVec (rotateMetricAddress address) (rotateMetricDigitOnce digit)
rotateMetricAddressSnoc [] digit = refl
rotateMetricAddressSnoc (x ∷ xs) digit
  rewrite rotateMetricAddressSnoc xs digit = refl

refAddressWheelCommutesWithAdapter :
  ∀ {d : Nat} (address : Ref.Lane369Address d) →
  refAddressToMetricAddress (Wheel.p7AddressWheel address)
  ≡ rotateMetricAddress (refAddressToMetricAddress address)
refAddressWheelCommutesWithAdapter Ref.root = refl
refAddressWheelCommutesWithAdapter (Ref.extend path digit)
  rewrite refAddressWheelCommutesWithAdapter path
        | rotateMetricAddressSnoc
            (refAddressToMetricAddress path)
            (refDigitToMetricDigit digit)
        | refDigitRotationCommutesWithAdapter digit = refl

------------------------------------------------------------------------
-- Hard geometric result: digitwise wheel rotation preserves common-prefix
-- agreement exactly, hence preserves the already-proved 369 ultrametric.

agreementDepthWheelInvariant :
  ∀ {d : Nat} (left right : U369.Address d) →
  U369.agreementDepth
    (rotateMetricAddress left)
    (rotateMetricAddress right)
  ≡ U369.agreementDepth left right
agreementDepthWheelInvariant [] [] = refl
agreementDepthWheelInvariant (U369.digit3 ∷ xs) (U369.digit3 ∷ ys) =
  cong suc (agreementDepthWheelInvariant xs ys)
agreementDepthWheelInvariant (U369.digit6 ∷ xs) (U369.digit6 ∷ ys) =
  cong suc (agreementDepthWheelInvariant xs ys)
agreementDepthWheelInvariant (U369.digit9 ∷ xs) (U369.digit9 ∷ ys) =
  cong suc (agreementDepthWheelInvariant xs ys)
agreementDepthWheelInvariant (U369.digit3 ∷ xs) (U369.digit6 ∷ ys) = refl
agreementDepthWheelInvariant (U369.digit3 ∷ xs) (U369.digit9 ∷ ys) = refl
agreementDepthWheelInvariant (U369.digit6 ∷ xs) (U369.digit3 ∷ ys) = refl
agreementDepthWheelInvariant (U369.digit6 ∷ xs) (U369.digit9 ∷ ys) = refl
agreementDepthWheelInvariant (U369.digit9 ∷ xs) (U369.digit3 ∷ ys) = refl
agreementDepthWheelInvariant (U369.digit9 ∷ xs) (U369.digit6 ∷ ys) = refl

distanceWheelInvariant :
  ∀ {d : Nat} (left right : U369.Address d) →
  U369.distance
    (rotateMetricAddress left)
    (rotateMetricAddress right)
  ≡ U369.distance left right
distanceWheelInvariant {d} left right =
  cong (λ agreement → d ∸ agreement)
    (agreementDepthWheelInvariant left right)

------------------------------------------------------------------------
-- Pull the metric back along the explicit refinement-address adapter.  The
-- actual p7 address wheel is therefore an isometry for this pulled-back metric.

refinementAddressDistance :
  ∀ {d : Nat} →
  Ref.Lane369Address d → Ref.Lane369Address d → Nat
refinementAddressDistance left right =
  U369.distance
    (refAddressToMetricAddress left)
    (refAddressToMetricAddress right)

p7RefinementAddressWheelIsometry :
  ∀ {d : Nat}
    (left right : Ref.Lane369Address d) →
  refinementAddressDistance
    (Wheel.p7AddressWheel left)
    (Wheel.p7AddressWheel right)
  ≡ refinementAddressDistance left right
p7RefinementAddressWheelIsometry left right
  rewrite refAddressWheelCommutesWithAdapter left
        | refAddressWheelCommutesWithAdapter right =
  distanceWheelInvariant
    (refAddressToMetricAddress left)
    (refAddressToMetricAddress right)
