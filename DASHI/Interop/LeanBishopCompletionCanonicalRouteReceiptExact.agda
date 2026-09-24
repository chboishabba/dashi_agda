module DASHI.Interop.LeanBishopCompletionCanonicalRouteReceiptExact where

------------------------------------------------------------------------
-- LEAN BISHOP-COMPLETION / CANONICAL ROUTE-B EXTERNAL FORMAL RECEIPT
--
-- Lean companion owners:
--
--   Integration.BishopVendoredRealEvaluation
--   Integration.BishopVendoredCompletionEquivalence
--   Integration.BishopVendoredCompletionAlgebraEquivalence
--   Integration.BishopRound11MachinCanonicalBinding
--   Integration.BishopRound11MachinReplayIrrelevance
--   Integration.MoonshineEisensteinRound11CanonicalRouteB
--
-- This receipt records machine-formal theorem content written on the pinned
-- Lean branch.  It does NOT claim that those Lean files have an exact-head
-- kernel receipt, nor that a generated importer replayed the named Agda
-- declarations.
--
-- The theorem content recorded here is stronger than an injective evaluator:
--
--   Quotient(Bishop regular reals / Bishop _~_)  ~=  Lean Real
--
-- together with compatibility of the actual vendored arithmetic, exact order
-- reflection, a canonical Round11/Machin source-binding inhabitant, uniqueness
-- of every admissible binding up to the Bishop setoid, and independence of the
-- mapped q/E4/E6/Delta semantics from binding choice.
--
-- Thus generated cross-language replay is now purely provenance/validation
-- evidence; it cannot alter the mapped mathematical value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record LeanBishopCompletionCanonicalRouteReceipt : Set where
  constructor lean-bishop-completion-canonical-route-receipt
  field
    leanRepository : String
    leanBranch : String
    bishopSubmoduleRepository : String
    bishopSubmoduleCommit : String

    sharpSampleToLimitBoundOwned : Bool
    evaluatorRespectsBishopSetoid : Bool
    evaluatorReflectsBishopSetoid : Bool

    canonicalRealToBishopEncodingOwned : Bool
    evalAfterEncodeIsIdentity : Bool
    encodeAfterEvalEquivalentInBishopSetoid : Bool
    bishopQuotientEquivalentToLeanReal : Bool

    exactVendoredZeroCompatibilityOwned : Bool
    exactVendoredOneCompatibilityOwned : Bool
    exactVendoredNegCompatibilityOwned : Bool
    exactVendoredAdd2nCompatibilityOwned : Bool
    exactVendoredKResampledMulCompatibilityOwned : Bool
    bishopOrderExactlyReflected : Bool

    bishopConvergenceImpliesLeanTendsto : Bool
    leanTendstoImpliesBishopConvergence : Bool

    canonicalRound11MachinBindingInhabited : Bool
    everyAdmissibleBindingSetoidEquivalentToCanonical : Bool

    canonicalRouteQOwned : Bool
    canonicalRouteE4E6ConvergenceOwned : Bool
    canonicalRouteNormalizedDeltaConvergenceOwned : Bool
    mappedRouteIndependentOfReplayBinding : Bool

    normalizedDeltaEta24SameObjectOwnedInPinnedLean : Bool
    targetInverseConjugationReflectionOwned : Bool
    targetUnitCircleFixedLocusOwned : Bool

    leanReplaySyntaxProbeSourceOwned : Bool
    leanRecursiveReplayClosureGeneratorSourceOwned : Bool
    leanReplayKernelElaborationWorkflowStepOwned : Bool

    generatedAgdaReplayObserved : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaExactHeadKernelReceiptObserved : Bool

open LeanBishopCompletionCanonicalRouteReceipt public

canonicalLeanBishopCompletionCanonicalRouteReceipt :
  LeanBishopCompletionCanonicalRouteReceipt
canonicalLeanBishopCompletionCanonicalRouteReceipt =
  lean-bishop-completion-canonical-route-receipt
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "https://github.com/viktorcsimma/bishop.git"
    "240e38c7f6938f20f865b1f956c5f084da48bd54"

    true true true
    true true true true

    true true true true true true

    true true

    true true

    true true true true

    true true true

    true true true

    false false false

------------------------------------------------------------------------
-- Query-stable theorem-status receipts.
------------------------------------------------------------------------

bishopQuotientEquivalentToLeanRealIsTrue :
  bishopQuotientEquivalentToLeanReal
    canonicalLeanBishopCompletionCanonicalRouteReceipt
  ≡ true
bishopQuotientEquivalentToLeanRealIsTrue = refl

canonicalRound11MachinBindingInhabitedIsTrue :
  canonicalRound11MachinBindingInhabited
    canonicalLeanBishopCompletionCanonicalRouteReceipt
  ≡ true
canonicalRound11MachinBindingInhabitedIsTrue = refl

mappedRouteIndependentOfReplayBindingIsTrue :
  mappedRouteIndependentOfReplayBinding
    canonicalLeanBishopCompletionCanonicalRouteReceipt
  ≡ true
mappedRouteIndependentOfReplayBindingIsTrue = refl

generatedAgdaReplayObservedIsFalse :
  generatedAgdaReplayObserved
    canonicalLeanBishopCompletionCanonicalRouteReceipt
  ≡ false
generatedAgdaReplayObservedIsFalse = refl

leanExactHeadKernelReceiptObservedIsFalse :
  leanExactHeadKernelReceiptObserved
    canonicalLeanBishopCompletionCanonicalRouteReceipt
  ≡ false
leanExactHeadKernelReceiptObservedIsFalse = refl

agdaExactHeadKernelReceiptObservedIsFalse :
  agdaExactHeadKernelReceiptObserved
    canonicalLeanBishopCompletionCanonicalRouteReceipt
  ≡ false
agdaExactHeadKernelReceiptObservedIsFalse = refl
