module DASHI.Mathematics.Algebra.RationalAlbertF4RealPlaceCompactnessReceiptExact where

------------------------------------------------------------------------
-- RATIONAL ALBERT DERIVATION ALGEBRA: REAL-PLACE COMPACTNESS DIAGNOSTIC
--
-- DASHI executable authority:
--   scripts/rational_albert_f4_trace_rank_probe.py
--
-- On an exact 52-element rational basis of the actual inner-derivation span,
-- that producer forms
--
--   G_ij = - trace_27(D_i D_j)
--
-- and checks with exact SymPy rational arithmetic:
--
-- * rank(G) = 52;
-- * LDL diagonal entries are all positive;
-- * the only diagonal values occurring are 3/2 and 6;
-- * the exact center of the represented derivation algebra has dimension 0.
--
-- This is an exact finite-dimensional diagnostic consistent with the compact
-- real completion of the represented Lie algebra.  It is NOT, by itself, a
-- formal classification of the real form or of the original Q-form, and does
-- not manufacture Aut(J)=F4 or Isom(N)=E6.
--
-- The regular-element centralizer dimension 4 in the companion script is a
-- floating numerical diagnostic and is intentionally recorded separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record ExactTraceFormReceipt : Set where
  constructor exact-trace-form-receipt
  field
    producerPath : String
    derivationBasisDimension : Nat
    negativeTraceFormRank : Nat
    exactLDLPositive : Bool
    exactLDLOnlyThreeHalvesAndSix : Bool
    exactCenterDimension : Nat
    floatingPointUsedForTraceRank : Bool
    floatingPointUsedForLDLSigns : Bool
    floatingPointUsedForCenter : Bool
    numericalRegularCentralizerDimension : Nat
    numericalRegularCentralizerOnly : Bool
open ExactTraceFormReceipt public

canonicalExactTraceFormReceipt : ExactTraceFormReceipt
canonicalExactTraceFormReceipt =
  exact-trace-form-receipt
    "scripts/rational_albert_f4_trace_rank_probe.py"
    52 52 true true 0
    false false false
    4 true

record Boundary : Set where
  constructor boundary
  field
    exactPositiveInvariantTraceFormDiagnosticPaid : Bool
    exactCenterZeroDiagnosticPaid : Bool
    compactRealPlaceSuggestedByDiagnostic : Bool
    compactRealPlaceClassificationFormalized : Bool
    originalQFormClassifiedFromRealPlaceAlone : Bool
    globalF4GroupClassificationPaid : Bool
    realPlaceDiagnosticCreatesGlobalQFormClassification : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true
  false false false false
