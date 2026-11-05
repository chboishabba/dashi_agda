module DASHI.Reasoning.AlbertF4LeanCrossProverMaxCutReceiptExact where

------------------------------------------------------------------------
-- COMPANION LEAN ALBERT/F4 MAX-CUT RECEIPT
--
-- This owner records newly source-written companion Lean results without
-- converting them into Agda theorem authority.  Agda already owns the actual
-- rational Albert carrier/Jordan product and the generic arbitrary-element
-- inner-derivation law independently.
--
-- Companion Lean now additionally pays/source-writes:
--
-- * four explicit Spin/Tits triality lifts preserving the repo-native
--   octonion triality tensor;
-- * a 384-element synchronized Spin closure with exact two-sheeted quotient
--   onto the independently constructed W(D4)_192 kernel;
-- * direct coordinate proofs that all four lifts preserve the native Albert
--   unit, trace, cubic and Jordan product;
-- * an exhaustive 73728-element native signed-basis closure;
-- * a projective native lift of one outer triality direction (`g05`);
-- * exhaustive absence of the second outer direction (`g24`) from that
--   current signed-basis subgroup, forcing a non-monomial/Hadamard-Tits lift;
-- * an arbitrary-element Lean theorem that every [L_a,L_b] is a derivation;
-- * exact-rational local diagnostics from the same Albert coordinate product:
--       dim span([L_ei,L_ej]) = 52,
--       diagonal-idempotent stabilizer dimension = 28,
--       moving evaluation rank = 24,
--       and three faithful rank-28 actions on the 8-dimensional octonion slots.
--
-- These strengthen the cross-prover evidence for the classical
-- f4 = so8 + 8v + 8s + 8c architecture, but do not by themselves prove a
-- same-Lie-algebra/root-datum isomorphism or Aut(J)=F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record LeanAlbertF4CrossProverReceipt : Set where
  constructor lean-albert-f4-cross-prover-receipt
  field
    sourceRepository : String
    sourcePullRequest : Nat

    spinLiftCount : Nat
    spinCoverOrder : Nat
    d4QuotientOrder : Nat
    exactTwoSheetedSpinQuotientSourceWritten : Bool
    fourNativeAlbertSpinAutomorphismsSourceWritten : Bool

    nativeSignedBasisClosureOrder : Nat
    unsignedCoordinateImageOrder : Nat
    pureSignKernelOrder : Nat
    g05ProjectiveOuterLiftSourceWritten : Bool
    g24AbsentFromCurrentSignedBasisClosureSourceWritten : Bool
    missingOuterRequiresNonMonomialChart : Bool

    arbitraryInnerDerivationLawSourceWrittenInLean : Bool
    exactInnerDerivationSpanRank : Nat
    diagonalStabilizerDimension : Nat
    movingComplementDimension : Nat
    octonionSlotDimension : Nat
    exactRationalLocalProbe : Bool

    internalAgdaProofAuthorityTransferred : Bool
    sameLieAlgebraF4RecognitionPaid : Bool
    fullAutJordanEqualsF4Paid : Bool
open LeanAlbertF4CrossProverReceipt public

canonicalLeanAlbertF4CrossProverReceipt : LeanAlbertF4CrossProverReceipt
canonicalLeanAlbertF4CrossProverReceipt =
  lean-albert-f4-cross-prover-receipt
    "chboishabba/dashi_lean4"
    52
    4
    384
    192
    true
    true
    73728
    2304
    32
    true
    true
    true
    true
    52
    28
    24
    8
    true
    false
    false
    false

record Boundary : Set where
  constructor boundary
  field
    companionLeanSpinQuotientRecorded : Bool
    companionLeanActualD4AlbertAutomorphismsRecorded : Bool
    companionLeanOuterLiftAsymmetryRecorded : Bool
    companionLeanDerivation52_28_24Recorded : Bool
    agdaNativeAlbertAuthorityRemainsIndependent : Bool
    agdaNativeInnerDerivationLawRemainsIndependent : Bool
    fullF4PromotionStillRequiresSameObjectLieRecognition : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true true true true
