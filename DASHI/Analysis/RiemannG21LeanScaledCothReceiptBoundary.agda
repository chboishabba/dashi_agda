module DASHI.Analysis.RiemannG21LeanScaledCothReceiptBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-prover receipt for the concrete Lean calculus candidate.
--
-- Lean source:
--   chboishabba/dashi_lean4
--   branch agent/rh-improved-zero-free-donor-20261016
--   commit 1ac1459f11eb83003e78ad869d0107b738e16c03
--   Synthesis/RiemannG21ScaledCothMonotonicity.lean
--
-- It source-writes the chain
--
--   sinh(x) cosh(x) > x       (x>0)
--     -> d/dx [x cosh(x)/sinh(x)] > 0
--     -> StrictMonoOn (x coth x) (0,inf).
--
-- Mathlib v4.28.0 owns the primitive hyperbolic identities and mean-value
-- theorem; DASHI/Lean owns the composition.  This receipt deliberately does
-- not turn that Lean theorem into Agda proof authority, and no exact-head Lean
-- kernel result is asserted here.
------------------------------------------------------------------------

record LeanScaledCothReceiptBoundary : Set where
  constructor lean-scaled-coth-receipt-boundary
  field
    sourceRepository : String
    sourceBranch : String
    sourceCommit : String
    sourceFile : String

    mathlibPrimitiveAttributionPreserved : Bool
    mathlibPrimitiveAttributionPreservedIsTrue :
      mathlibPrimitiveAttributionPreserved ≡ true

    scaledCothMonotonicitySourceWritten : Bool
    scaledCothMonotonicitySourceWrittenIsTrue :
      scaledCothMonotonicitySourceWritten ≡ true

    exactHeadLeanKernelChecked : Bool
    exactHeadLeanKernelCheckedIsFalse : exactHeadLeanKernelChecked ≡ false

    scaledCothMonotonicityImportedIntoAgda : Bool
    scaledCothMonotonicityImportedIntoAgdaIsFalse :
      scaledCothMonotonicityImportedIntoAgda ≡ false

    continuumOddMomentSignPaid : Bool
    continuumOddMomentSignPaidIsFalse : continuumOddMomentSignPaid ≡ false

    finiteRadiusParityMinorPaid : Bool
    finiteRadiusParityMinorPaidIsFalse : finiteRadiusParityMinorPaid ≡ false

    poleQuotientTransversalityPaid : Bool
    poleQuotientTransversalityPaidIsFalse :
      poleQuotientTransversalityPaid ≡ false

    receiptReading : String

canonicalLeanScaledCothReceiptBoundary : LeanScaledCothReceiptBoundary
canonicalLeanScaledCothReceiptBoundary =
  lean-scaled-coth-receipt-boundary
    "chboishabba/dashi_lean4"
    "agent/rh-improved-zero-free-donor-20261016"
    "1ac1459f11eb83003e78ad869d0107b738e16c03"
    "Synthesis/RiemannG21ScaledCothMonotonicity.lean"
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The previously open G21 x*coth(x) scalar calculus leaf now has a concrete Lean source proof candidate composed from pinned Mathlib v4.28.0 primitives. Until exact-head Lean checking and an explicit cross-prover theorem transport exist, Agda continues to mark its own actual monotonicity theorem unpaid. Even after transport, the continuum odd-moment sign, finite-radius parity minor and pole-quotient transversality remain separate analytic/same-object obligations."
