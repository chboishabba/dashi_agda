module DASHI.Analysis.RiemannG21LeanHyperbolicMonotonicityReceiptBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Paired cross-prover receipt for the two elementary G21 scaled-hyperbolic
-- monotonicity leaves.
--
-- Lean source repository:
--   chboishabba/dashi_lean4
-- branch:
--   agent/rh-improved-zero-free-donor-20261016
-- head containing both source-written candidates:
--   8d8826d6e96dd9c301a092b04346d0b600fdae34
--
-- Files:
--   Synthesis/RiemannG21ScaledCothMonotonicity.lean
--   Synthesis/RiemannG21ScaledTanhMonotonicity.lean
--
-- The coth candidate proves strict increase of x*cosh(x)/sinh(x) on x>0.
-- The tanh candidate proves strict increase of x*sinh(x)/cosh(x) on x>0.
-- Both compose pinned Mathlib v4.28.0 calculus/hyperbolic primitives.  This
-- Agda receipt records source availability only: neither theorem is imported
-- as Agda proof authority and no exact-head Lean kernel GREEN claim is made.
------------------------------------------------------------------------

record LeanHyperbolicMonotonicityReceiptBoundary : Set where
  constructor lean-hyperbolic-monotonicity-receipt-boundary
  field
    sourceRepository : String
    sourceBranch : String
    sourceCommit : String
    cothSourceFile : String
    tanhSourceFile : String

    mathlibPrimitiveAttributionPreserved : Bool
    mathlibPrimitiveAttributionPreservedIsTrue :
      mathlibPrimitiveAttributionPreserved ≡ true

    scaledCothMonotonicitySourceWritten : Bool
    scaledCothMonotonicitySourceWrittenIsTrue :
      scaledCothMonotonicitySourceWritten ≡ true

    scaledTanhMonotonicitySourceWritten : Bool
    scaledTanhMonotonicitySourceWrittenIsTrue :
      scaledTanhMonotonicitySourceWritten ≡ true

    exactHeadLeanKernelChecked : Bool
    exactHeadLeanKernelCheckedIsFalse : exactHeadLeanKernelChecked ≡ false

    hyperbolicMonotonicityImportedIntoAgda : Bool
    hyperbolicMonotonicityImportedIntoAgdaIsFalse :
      hyperbolicMonotonicityImportedIntoAgda ≡ false

    continuumMomentLayerPaid : Bool
    continuumMomentLayerPaidIsFalse : continuumMomentLayerPaid ≡ false

    finiteRadiusParityMinorsPaid : Bool
    finiteRadiusParityMinorsPaidIsFalse : finiteRadiusParityMinorsPaid ≡ false

    poleQuotientTransversalityPaid : Bool
    poleQuotientTransversalityPaidIsFalse :
      poleQuotientTransversalityPaid ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

    receiptReading : String

canonicalLeanHyperbolicMonotonicityReceiptBoundary :
  LeanHyperbolicMonotonicityReceiptBoundary
canonicalLeanHyperbolicMonotonicityReceiptBoundary =
  lean-hyperbolic-monotonicity-receipt-boundary
    "chboishabba/dashi_lean4"
    "agent/rh-improved-zero-free-donor-20261016"
    "8d8826d6e96dd9c301a092b04346d0b600fdae34"
    "Synthesis/RiemannG21ScaledCothMonotonicity.lean"
    "Synthesis/RiemannG21ScaledTanhMonotonicity.lean"
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Both elementary G21 scaled-hyperbolic monotonicity leaves now have concrete source-written Lean proof candidates composed from pinned Mathlib v4.28.0 primitives. This receipt does not promote them into Agda theorem authority or kernel-GREEN status. Once transported, the remaining substantive frontier is the continuum even/odd moment layer, finite-radius Taylor/parity-minor control, and pole-quotient transversality; RH remains open."
