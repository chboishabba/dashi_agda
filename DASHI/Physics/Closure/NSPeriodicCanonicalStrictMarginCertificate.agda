module DASHI.Physics.Closure.NSPeriodicCanonicalStrictMarginCertificate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero; _+_)

import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact canonical strict-margin certificate at denominator eight.
--
-- The selected near Young payments consume 1/4.  The two radius-eight tail
-- budgets consume at most 1/8 + 1/8 = 1/4.  Thus only 1/2 of the normalized
-- viscous budget is assigned, leaving an exact positive margin of 1/2.
--
-- This is the scalar certificate required by the strict-margin adapter.  The
-- remaining analysis must prove that the literal near/far terms fit these
-- already-certified shares.
------------------------------------------------------------------------

canonicalNearPayment canonicalFarLowPayment canonicalFarHighPayment : Nat
canonicalNearPayment = Dyadic.quarterᴰ
canonicalFarLowPayment = Dyadic.epsilonLowAtEight
canonicalFarHighPayment = Dyadic.epsilonHighAtEight

canonicalTotalNonlinearPayment canonicalStrictMargin
  canonicalViscosityBudget : Nat
canonicalTotalNonlinearPayment =
  canonicalNearPayment + canonicalFarLowPayment + canonicalFarHighPayment
canonicalStrictMargin = Dyadic.halfᴰ
canonicalViscosityBudget = Dyadic.oneᴰ

canonicalNearPaymentIsQuarter :
  canonicalNearPayment ≡ Dyadic.quarterᴰ
canonicalNearPaymentIsQuarter = refl

canonicalTailPaymentIsQuarter :
  canonicalFarLowPayment + canonicalFarHighPayment ≡ Dyadic.quarterᴰ
canonicalTailPaymentIsQuarter = refl

canonicalTotalPaymentIsHalf :
  canonicalTotalNonlinearPayment ≡ Dyadic.halfᴰ
canonicalTotalPaymentIsHalf = refl

canonicalPaymentPlusMarginIsViscosity :
  canonicalTotalNonlinearPayment + canonicalStrictMargin
  ≡ canonicalViscosityBudget
canonicalPaymentPlusMarginIsViscosity = refl

canonicalStrictMarginPositive :
  Dyadic._≤ᴺ_ (suc zero) canonicalStrictMargin
canonicalStrictMarginPositive = Dyadic.halfPositiveᴰ

record CanonicalStrictMarginCertificate : Set where
  field
    near-is-quarter : canonicalNearPayment ≡ Dyadic.quarterᴰ
    tails-are-quarter :
      canonicalFarLowPayment + canonicalFarHighPayment ≡ Dyadic.quarterᴰ
    total-is-half : canonicalTotalNonlinearPayment ≡ Dyadic.halfᴰ
    payment-plus-margin-is-viscosity :
      canonicalTotalNonlinearPayment + canonicalStrictMargin
      ≡ canonicalViscosityBudget
    strict-margin-positive :
      Dyadic._≤ᴺ_ (suc zero) canonicalStrictMargin

canonicalStrictMarginCertificate : CanonicalStrictMarginCertificate
canonicalStrictMarginCertificate = record
  { near-is-quarter = canonicalNearPaymentIsQuarter
  ; tails-are-quarter = canonicalTailPaymentIsQuarter
  ; total-is-half = canonicalTotalPaymentIsHalf
  ; payment-plus-margin-is-viscosity = canonicalPaymentPlusMarginIsViscosity
  ; strict-margin-positive = canonicalStrictMarginPositive
  }

------------------------------------------------------------------------
-- Status: the scalar positivity problem is closed for the canonical shares.
-- The frontier is now the cutoff-uniform analytic fit of the actual near,
-- far-low, and far-high terms into 1/4, 1/8, and 1/8 respectively.
------------------------------------------------------------------------

canonicalStrictMarginCertificateLevel : ProofLevel
canonicalStrictMarginCertificateLevel = machineChecked
