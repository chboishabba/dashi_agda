module DASHI.Analysis.RiemannG21MathlibOddMomentPositivityReceiptBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- External theorem inventory for strict positivity of the odd first moment
--
--   N1(y) = integral_0^{L/2} u phi(u) sinh(yu) du,
--
-- at y>0.
--
-- The companion taper proves phi=1 on a nontrivial central plateau under the
-- paper parameter regime, as well as phi>=0 and compact support.  On any
-- positive subinterval of that plateau, u>0 and sinh(yu)>0, so the integrand
-- is strictly positive.
--
-- Mathlib provides positive-integral criteria including:
--
--   MeasureTheory.integral_pos_iff_support_of_nonneg
--   intervalIntegral.intervalIntegral_pos_of_pos_on
--   intervalIntegral.integral_pos_iff_support_of_nonneg_ae
--
-- This module records the intended specialization only; no Lean proof term is
-- counted as imported into Agda.
------------------------------------------------------------------------

record OddMomentPositivityReceipt : Set where
  constructor oddMomentPositivityReceipt
  field
    companionPlateauTheorem : String
    companionNonnegativeTheorem : String
    mathlibIntegralPosTheorem : String
    mathlibIntervalPosTheorem : String
    mathlibIntervalSupportPosTheorem : String
    targetReading : String

canonicalOddMomentPositivityReceipt : OddMomentPositivityReceipt
canonicalOddMomentPositivityReceipt =
  oddMomentPositivityReceipt
    "Zeta23.Taper.phi_eq_one"
    "Zeta23.Taper.phi_nonneg"
    "MeasureTheory.integral_pos_iff_support_of_nonneg"
    "intervalIntegral.intervalIntegral_pos_of_pos_on"
    "intervalIntegral.integral_pos_iff_support_of_nonneg_ae"
    "For y>0 and a positive-length plateau inside (0,L/2), prove N1(y)>0 from positivity of u*phi(u)*sinh(yu)."

record OddMomentPositivityBoundary : Set where
  constructor oddMomentPositivityBoundary
  field
    plateauSourceTheoremLocated : Bool
    plateauSourceTheoremLocatedIsTrue : plateauSourceTheoremLocated ≡ true
    positiveIntegralTheoremsLocated : Bool
    positiveIntegralTheoremsLocatedIsTrue : positiveIntegralTheoremsLocated ≡ true
    specializedLeanN1PositivityProofPresent : Bool
    specializedLeanN1PositivityProofPresentIsFalse :
      specializedLeanN1PositivityProofPresent ≡ false
    n1PositivityDerivedInAgda : Bool
    n1PositivityDerivedInAgdaIsFalse : n1PositivityDerivedInAgda ≡ false

canonicalOddMomentPositivityBoundary : OddMomentPositivityBoundary
canonicalOddMomentPositivityBoundary =
  oddMomentPositivityBoundary true refl true refl false refl false refl
