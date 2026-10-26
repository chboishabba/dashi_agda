module DASHI.Analysis.RiemannG21LeanAtomicTP2ReceiptBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-prover receipt for the next G21 pointwise layer.
--
-- Lean source:
--   chboishabba/dashi_lean4
--   branch agent/rh-improved-zero-free-donor-20261016
--   commit 0015480ec2a811331ec5e9a86dd0b73d58544522
--   Synthesis/RiemannG21AtomicHyperbolicTP2.lean
--
-- The source candidate composes the scaled x*coth(x)/x*tanh(x)
-- monotonicity candidates into the exact pointwise strict determinants:
--
--   sinh(p v)sinh(a u) > sinh(p u)sinh(a v)
--   cosh(p v)cosh(a u) > cosh(p u)cosh(a v)
--
-- for 0<a<p and 0<u<v, by proving the corresponding scale ratios are
-- strictly increasing in u.
--
-- This remains source-written / kernel-pending on the Lean side and is not
-- promoted into Agda theorem authority here.
------------------------------------------------------------------------

record LeanAtomicTP2ReceiptBoundary : Set where
  constructor lean-atomic-tp2-receipt-boundary
  field
    sourceRepository : String
    sourceBranch : String
    sourceCommit : String
    sourceFile : String

    scaledHyperbolicMonotonicityDependencySourceWritten : Bool
    scaledHyperbolicMonotonicityDependencySourceWrittenIsTrue :
      scaledHyperbolicMonotonicityDependencySourceWritten ≡ true

    sinhTP2SourceWritten : Bool
    sinhTP2SourceWrittenIsTrue : sinhTP2SourceWritten ≡ true

    coshTP2SourceWritten : Bool
    coshTP2SourceWrittenIsTrue : coshTP2SourceWritten ≡ true

    exactHeadLeanKernelChecked : Bool
    exactHeadLeanKernelCheckedIsFalse : exactHeadLeanKernelChecked ≡ false

    atomicTP2ImportedIntoAgda : Bool
    atomicTP2ImportedIntoAgdaIsFalse : atomicTP2ImportedIntoAgda ≡ false

    actualTaperDoubleIntegralSignPaid : Bool
    actualTaperDoubleIntegralSignPaidIsFalse :
      actualTaperDoubleIntegralSignPaid ≡ false

    finiteRadiusParityMinorsPaid : Bool
    finiteRadiusParityMinorsPaidIsFalse : finiteRadiusParityMinorsPaid ≡ false

    poleQuotientTransversalityPaid : Bool
    poleQuotientTransversalityPaidIsFalse :
      poleQuotientTransversalityPaid ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

    receiptReading : String

canonicalLeanAtomicTP2ReceiptBoundary : LeanAtomicTP2ReceiptBoundary
canonicalLeanAtomicTP2ReceiptBoundary =
  lean-atomic-tp2-receipt-boundary
    "chboishabba/dashi_lean4"
    "agent/rh-improved-zero-free-donor-20261016"
    "0015480ec2a811331ec5e9a86dd0b73d58544522"
    "Synthesis/RiemannG21AtomicHyperbolicTP2.lean"
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The G21 pointwise sinh/cosh strict-TP2 leaves now have concrete Lean source proof candidates downstream of the paired scaled-hyperbolic monotonicity candidates. Agda does not import them as theorem authority and exact-head Lean kernel checking is still pending. If those candidates check and are transported, the live frontier moves to the actual taper-weighted continuum double-integral sign, finite-radius Taylor/parity-minor control, pole-quotient transversality and finally the RH consumer."
