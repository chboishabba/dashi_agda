module DASHI.Algebra.LocalInverseVsGlobalInverse where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational using (ℚ)

open import DASHI.Core.OperatorTypes using (Invertible)
open import Verification.JacobianCounterexampleKernel as J
  using
    ( Point3
    ; F
    ; _≢_
    ; zeroQ
    ; invertibleImpliesInjective
    ; F-notInjective
    ; jacobianDeterminantAt
    ; alpogePolynomialMap
    ; jacobianEverywhereNonzero
    ; pZero
    ; pPositive
    ; pNegative
    )

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- Local inverse charts carry neighbourhood data and round-trip laws only on
-- that neighbourhood.  A global inverse is the repository's explicit
-- two-sided Invertible witness.

record LocalInverseAt
    {X : Set}
    (f : X → X)
    (centre : X)
    : Set₁ where
  field
    Neighbourhood : X → Set
    centreIncluded : Neighbourhood centre
    localInverse : X → X
    leftLocal :
      (x : X) → Neighbourhood x →
      localInverse (f x) ≡ x
    rightLocal :
      (y : X) → Neighbourhood y →
      f (localInverse y) ≡ y

GlobalInverse : ∀ {X : Set} → (X → X) → Set
GlobalInverse = Invertible

noGlobalInverseForF : ¬ GlobalInverse F
noGlobalInverseForF global =
  F-notInjective (invertibleImpliesInjective global)

record ComplexInverseFunctionAuthority : Set₁ where
  field
    locallyInvertibleFromNonzeroJacobian :
      (f : Point3 → Point3) →
      (determinantAt : Point3 → ℚ) →
      ((p : Point3) → determinantAt p ≢ zeroQ) →
      (p : Point3) →
      LocalInverseAt f p

record AllLocalButNoGlobal : Set₁ where
  constructor allLocalButNoGlobal
  field
    map : Point3 → Point3
    everyPointHasLocalInverse : (p : Point3) → LocalInverseAt map p
    noSingleGlobalInverse : ¬ GlobalInverse map

alpogeAllLocalButNoGlobal :
  ComplexInverseFunctionAuthority →
  AllLocalButNoGlobal
alpogeAllLocalButNoGlobal authority =
  allLocalButNoGlobal
    F
    (ComplexInverseFunctionAuthority.locallyInvertibleFromNonzeroJacobian
      authority
      F
      (jacobianDeterminantAt alpogePolynomialMap)
      jacobianEverywhereNonzero)
    noGlobalInverseForF

------------------------------------------------------------------------
-- A sheet label restores the information erased by the visible target.

data SheetLabel : Set where
  negativeSheet centralSheet positiveSheet : SheetLabel

record SheetedSource : Set where
  constructor sheetedSource
  field
    visiblePoint : Point3
    sheet : SheetLabel

sheetedNegative sheetedCentral sheetedPositive : SheetedSource
sheetedNegative = sheetedSource pNegative negativeSheet
sheetedCentral = sheetedSource pZero centralSheet
sheetedPositive = sheetedSource pPositive positiveSheet

record LocalGlobalInverseReceipt : Set where
  constructor mkLocalGlobalInverseReceipt
  field
    globalInverseRefutedByCollision : Bool
    localInverseTheoremFabricatedInCore : Bool
    localInverseTheoremFabricatedInCoreIsFalse :
      localInverseTheoremFabricatedInCore ≡ false
    inverseFunctionAuthorityNamed : Bool
    sheetLabelNeededForDisplayedFibre : Bool
    localRoundTripsPromotedToGlobalRoundTrip : Bool
    localRoundTripsPromotedToGlobalRoundTripIsFalse :
      localRoundTripsPromotedToGlobalRoundTrip ≡ false
    interpretation : String

localGlobalInverseReceipt : LocalGlobalInverseReceipt
localGlobalInverseReceipt =
  mkLocalGlobalInverseReceipt
    true
    false refl
    true true
    false refl
    "nonzero Jacobian supports local inverse charts through an explicit inverse-function authority, while the exact collision kernel-refutes any single global inverse; recovering a displayed preimage requires sheet information"
