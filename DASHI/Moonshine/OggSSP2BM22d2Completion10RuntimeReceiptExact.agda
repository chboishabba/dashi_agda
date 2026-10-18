module DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact where

------------------------------------------------------------------------
-- M22:2 OUTER-INVOLUTION COMPLETION10 RUNTIME RECEIPT
--
-- Provenance: DASHI runtime computation over the actual AtlasRep
-- characteristic-two ten-dimensional modules for M22:2, executed locally on
-- 2026-10-03 by scripts/m22d2_completion10_outer_involution_screen.g.
--
-- Decisive finite result:
--   * both ten-dimensional M22:2 modules restrict to the actual M22 10a/10b;
--   * in each module an OUTER involution class has
--
--       class size             = 1386,
--       centralizer order      = 640,
--       rank(g - I)            = 5,
--       dim Fix(g)             = 5;
--
--   * the full ten-dimensional carrier admits five literal swapped pairs
--       a_i <-> b_i,
--     so the action has Jordan shape J2^5;
--   * there are exactly two such module/class matches, one in each ten-module.
--
-- This pays the FINITE Completion10 phase candidate one layer above the
-- failed bare-M22 involution route.  It does NOT identify either module as a
-- subquotient of the actual 2B Tate fibre and does NOT identify the M22:2
-- outer involution with the actual Monster-local action on that Tate fibre.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Exact runtime constants.
------------------------------------------------------------------------

outerInvolutionClassSize : Nat
outerInvolutionClassSize = 1386

outerInvolutionCentralizerOrder : Nat
outerInvolutionCentralizerOrder = 640

outerInvolutionRank : Nat
outerInvolutionRank = 5

outerInvolutionFixedDimension : Nat
outerInvolutionFixedDimension = 5

outerJ2x5MatchCount : Nat
outerJ2x5MatchCount = 2

outerInvolutionClassSizeIs1386 : outerInvolutionClassSize ≡ 1386
outerInvolutionClassSizeIs1386 = refl

outerInvolutionCentralizerOrderIs640 :
  outerInvolutionCentralizerOrder ≡ 640
outerInvolutionCentralizerOrderIs640 = refl

outerInvolutionRankIsFive : outerInvolutionRank ≡ 5
outerInvolutionRankIsFive = refl

outerInvolutionFixedDimensionIsFive :
  outerInvolutionFixedDimension ≡ 5
outerInvolutionFixedDimensionIsFive = refl

outerJ2x5MatchCountIsTwo : outerJ2x5MatchCount ≡ 2
outerJ2x5MatchCountIsTwo = refl

------------------------------------------------------------------------
-- 2. Per-module runtime receipts.
------------------------------------------------------------------------

data M22d2TenModuleKind : Set where
  tenA tenB : M22d2TenModuleKind

record OuterCompletionCandidate : Set where
  constructor outer-completion-candidate
  field
    moduleKind : M22d2TenModuleKind
    restrictsToActualM22Ten : Bool
    involutionIsOuter : Bool
    classSize : Nat
    centralizerOrder : Nat
    rankGMinusI : Nat
    fixedDimension : Nat
    fiveSwapPairsVerified : Bool
    tenVectorsSpanWholeModule : Bool

open OuterCompletionCandidate public

tenAOuterCompletionCandidate : OuterCompletionCandidate
tenAOuterCompletionCandidate =
  outer-completion-candidate
    tenA true true
    1386 640 5 5
    true true

tenBOuterCompletionCandidate : OuterCompletionCandidate
tenBOuterCompletionCandidate =
  outer-completion-candidate
    tenB true true
    1386 640 5 5
    true true

------------------------------------------------------------------------
-- 3. Exact finite Completion10 consequence.
------------------------------------------------------------------------

record FiniteM22d2Completion10Receipt : Set where
  constructor finite-m22d2-completion10-receipt
  field
    tenARestrictionIdentified : Bool
    tenBRestrictionIdentified : Bool
    outerJ2x5Matches : Nat
    literalFivePairBasisVerifiedInTenA : Bool
    literalFivePairBasisVerifiedInTenB : Bool
    finiteCompletionPhaseCandidatePaid : Bool
    actualTwoBTateSubquotientIdentified : Bool
    actualTateActionIntertwinerIdentified : Bool
    sourceProvenance : String

open FiniteM22d2Completion10Receipt public

canonicalFiniteM22d2Completion10Receipt : FiniteM22d2Completion10Receipt
canonicalFiniteM22d2Completion10Receipt =
  finite-m22d2-completion10-receipt
    true true
    2
    true true
    true
    false false
    "DASHI runtime: AtlasRep M22:2 ten-dimensional modules; outer involution class size 1386, centralizer order 640, rank(g-I)=5, dim Fix=5; five swapped pairs verified"

finiteCompletionPhaseCandidateIsPaid :
  finiteCompletionPhaseCandidatePaid canonicalFiniteM22d2Completion10Receipt
  ≡ true
finiteCompletionPhaseCandidateIsPaid = refl

actualTwoBTateSubquotientIdentifiedIsFalse :
  actualTwoBTateSubquotientIdentified canonicalFiniteM22d2Completion10Receipt
  ≡ false
actualTwoBTateSubquotientIdentifiedIsFalse = refl

actualTateActionIntertwinerIdentifiedIsFalse :
  actualTateActionIntertwinerIdentified canonicalFiniteM22d2Completion10Receipt
  ≡ false
actualTateActionIntertwinerIdentifiedIsFalse = refl

------------------------------------------------------------------------
-- 4. Promotion firewall.
------------------------------------------------------------------------

data OuterCompletionCandidateIsActualTwoBTateAction : Set where

data FiniteJ2x5ConstructsActualTateSubquotient : Set where

outerCompletionCandidateDoesNotIdentifyActualTateAction :
  OuterCompletionCandidateIsActualTwoBTateAction → ⊥
outerCompletionCandidateDoesNotIdentifyActualTateAction ()

finiteJ2x5DoesNotConstructActualTateSubquotient :
  FiniteJ2x5ConstructsActualTateSubquotient → ⊥
finiteJ2x5DoesNotConstructActualTateSubquotient ()

------------------------------------------------------------------------
-- 5. Revised C' boundary.
------------------------------------------------------------------------

record GateCPrimeRuntimeStatus : Set where
  constructor gate-c-prime-runtime-status
  field
    bareM22RouteKilled : Bool
    m22d2OuterRouteScreened : Bool
    m22d2OuterJ2x5Found : Bool
    outerMatchCount : Nat
    fivePairBasisVerified : Bool
    finiteCompletionSourceLocated : Bool
    actualTateSubquotientPaid : Bool
    actualTateActionSameObjectPaid : Bool
    nextResidual : String

canonicalGateCPrimeRuntimeStatus : GateCPrimeRuntimeStatus
canonicalGateCPrimeRuntimeStatus =
  gate-c-prime-runtime-status
    true true true 2 true true
    false false
    "identify one observed M22:2 ten-module as an actual subquotient of the 2B Tate fibre and prove the sourced outer involution action descends to that same subquotient"
