module DASHI.Physics.Closure.NSTriadKNPositivePartCancellationNoGo where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- A constructive obstruction to identifying a positive-part kernel with
-- the exact signed transfer.
--
-- SignedNat stores an exact formal difference positive - negative.  Balance
-- is equality of the two sides.  Two opposite nonzero transfers balance
-- exactly, while their positive parts do not.
------------------------------------------------------------------------

record SignedNat : Set where
  constructor signed
  field
    positive negative : Nat

open SignedNat public

signedZero : SignedNat
signedZero = signed zero zero

signedAdd : SignedNat → SignedNat → SignedNat
signedAdd x y =
  signed
    (positive x + positive y)
    (negative x + negative y)

Balanced : SignedNat → Set
Balanced x = positive x ≡ negative x

positivePart : SignedNat → Nat
positivePart = positive

forwardUnit backwardUnit : SignedNat
forwardUnit = signed (suc zero) zero
backwardUnit = signed zero (suc zero)

oppositeUnitsCancelExactly :
  Balanced (signedAdd forwardUnit backwardUnit)
oppositeUnitsCancelExactly = refl

positivePartsOfOppositeUnits :
  positivePart forwardUnit + positivePart backwardUnit ≡ suc zero
positivePartsOfOppositeUnits = refl

positivePartsDoNotCancel :
  positivePart forwardUnit + positivePart backwardUnit ≡ zero → ⊥
positivePartsDoNotCancel ()

record CancellationPreservingMajorant : Set₁ where
  field
    majorant : SignedNat → Nat

    exactBalancePreserved :
      ∀ x y →
      Balanced (signedAdd x y) →
      majorant x + majorant y ≡ zero

open CancellationPreservingMajorant public

positivePartCannotPreserveAllSignedCancellations :
  (certificate : CancellationPreservingMajorant) →
  majorant certificate ≡ positivePart →
  ⊥
positivePartCannotPreserveAllSignedCancellations certificate refl =
  positivePartsDoNotCancel
    (exactBalancePreserved certificate
      forwardUnit backwardUnit oppositeUnitsCancelExactly)

------------------------------------------------------------------------
-- Consequence for Stage 3.
--
-- A positive kernel can still be a valid upper majorant.  It cannot be
-- called the exact signed Navier--Stokes transfer unless an additional
-- theorem proves that no cancellation relevant to the target estimate was
-- discarded.
------------------------------------------------------------------------

data KernelRole : Set where
  exactSignedOperator positiveMajorantOperator : KernelRole

positivePartRole : KernelRole
positivePartRole = positiveMajorantOperator

positivePartCancellationObstructionImplemented : Bool
positivePartCancellationObstructionImplemented = true

positivePartCancellationObstructionImplementedIsTrue :
  positivePartCancellationObstructionImplemented ≡ true
positivePartCancellationObstructionImplementedIsTrue = refl

positivePartMayBeExactWithoutExtraProof : Bool
positivePartMayBeExactWithoutExtraProof = false

positivePartMayBeExactWithoutExtraProofIsFalse :
  positivePartMayBeExactWithoutExtraProof ≡ false
positivePartMayBeExactWithoutExtraProofIsFalse = refl
