{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact where

------------------------------------------------------------------------
-- E1 NO-GO: ADDITIVE FIRST-VARIATION LINEARITY DOES NOT FORCE COVARIANCE.
--
-- R142/R143 linearity gives zero/additivity of a first-variation functional.
-- That algebra alone cannot produce the marked B4 naturality theorem.  The
-- finite F2 countermodel below has an additive linear functional and a linear
-- coordinate-swap symmetry, but the functional is not swap invariant.
--
-- Therefore E1 still needs either the direct R144 signed-readout covariance or
-- an actual source/change-of-variables naturality theorem that compiles to it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)

data Bit : Set where
  zeroBit : Bit
  oneBit : Bit

xor : Bit → Bit → Bit
xor zeroBit right = right
xor oneBit zeroBit = oneBit
xor oneBit oneBit = zeroBit

Vector2 : Set
Vector2 = Bit × Bit

zeroVector : Vector2
zeroVector = zeroBit , zeroBit

addVector : Vector2 → Vector2 → Vector2
addVector (left₁ , right₁) (left₂ , right₂) =
  xor left₁ left₂ , xor right₁ right₂

linearReadout : Vector2 → Bit
linearReadout = proj₁

swapCoordinates : Vector2 → Vector2
swapCoordinates (left , right) = right , left

linearReadoutZero : linearReadout zeroVector ≡ zeroBit
linearReadoutZero = refl

linearReadoutAdd : ∀ left right →
  linearReadout (addVector left right)
  ≡ xor (linearReadout left) (linearReadout right)
linearReadoutAdd (left₁ , right₁) (left₂ , right₂) = refl

swapPreservesAddition : ∀ left right →
  swapCoordinates (addVector left right)
  ≡ addVector (swapCoordinates left) (swapCoordinates right)
swapPreservesAddition (left₁ , right₁) (left₂ , right₂) = refl

zeroBitNotOneBit : zeroBit ≡ oneBit → ⊥
zeroBitNotOneBit ()

linearReadoutNotSwapInvariant :
  (∀ vector →
    linearReadout (swapCoordinates vector) ≡ linearReadout vector) →
  ⊥
linearReadoutNotSwapInvariant invariant =
  zeroBitNotOneBit
    (invariant (oneBit , zeroBit))

additiveFirstVariationLinearityForcesSymmetryCovariance : Bool
additiveFirstVariationLinearityForcesSymmetryCovariance = false

sourceNaturalityOrDirectCovarianceStillRequired : Bool
sourceNaturalityOrDirectCovarianceStillRequired = true

r142LinearityIsNotAnE1CovarianceProducerByItself : Bool
r142LinearityIsNotAnE1CovarianceProducerByItself = true
