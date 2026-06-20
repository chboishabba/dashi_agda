module DASHI.Physics.Closure.NSTypeIHAreaUniformizationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Conditional type-I H_area uniformization receipt.
--
-- This module records the Cauchy-Schwarz route
--
--   |Omega_K| >= ||Q+||_1^2 / ||Q||_2^2
--
-- the type-I scaling picture that keeps the ratio bounded below, the
-- isoperimetric consequence H^2(boundary Omega_K) >= A0, and the explicit
-- limitation that this route does not close under type-II blow-up.

record NSTypeIHAreaUniformizationReceipt : Set where
  constructor mkNSTypeIHAreaUniformizationReceipt
  field
    lowerBoundShape :
      String

    typeIScalingStatement :
      String

    dependencyStatement :
      String

    isoperimetricStatement :
      String

    typeIILimitationStatement :
      String

    conditionalOnly :
      Bool

    conditionalOnlyIsTrue :
      conditionalOnly ≡ true

    theoremPromotion :
      Bool

    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

open NSTypeIHAreaUniformizationReceipt public

canonicalNSTypeIHAreaUniformizationReceipt :
  NSTypeIHAreaUniformizationReceipt
canonicalNSTypeIHAreaUniformizationReceipt =
  mkNSTypeIHAreaUniformizationReceipt
    "|Omega_K| >= ||Q+||_1^2 / ||Q||_2^2 by the recorded Cauchy-Schwarz lower-bound shape."
    "Under type I scaling, the numerator and denominator are both recorded at order (T*-t)^(-2), so the ratio stays bounded below by a positive constant."
    "The lower bound depends on the initial enstrophy/energy token E0 and the type-I constant C0."
    "Isoperimetric consequence recorded: H^2(boundary Omega_K) >= A0 > 0."
    "Type-II limitation recorded explicitly: the same scaling comparison does not close under type-II blow-up."
    true
    refl
    false
    refl
    false
    refl

