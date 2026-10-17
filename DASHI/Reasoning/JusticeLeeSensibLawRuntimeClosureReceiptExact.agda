module DASHI.Reasoning.JusticeLeeSensibLawRuntimeClosureReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawResidualLattice as SL
import DASHI.Reasoning.JusticeLeeSensibLawBidiSearchClosureExact as Legacy

------------------------------------------------------------------------
-- RECEIPT-INDEXED RUNTIME CLOSURE
--
-- `Legacy.canonicalLeeSensibLawBidiClosure` is retained as the historical
-- formal baseline and therefore keeps its historical runtime/experiment flags
-- false.  Live closure is represented instead by an explicit receipt carrying
-- the source PNF emission and persisted review/Matter/controversy/search refs.
--
-- This module provides the closure type only.  It does not fabricate a
-- production receipt and deliberately exports no canonical live inhabitant.
-- Mabo or another real Matter may inhabit this type only from actual runtime
-- coordinates; source-level formalisation alone is not such an inhabitant.
------------------------------------------------------------------------

record RuntimePNFControversyReceipt : Set where
  constructor runtime-pnf-controversy-receipt
  field
    runtimeEmission : SL.PNFEmissionReceipt
    sourceRevisionReference : String
    reviewDecisionReference : String
    matterReference : String
    controversyReference : String
    reverseSearchReference : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    semanticAuthorityPromoted : Bool
    semanticAuthorityPromotedIsFalse : semanticAuthorityPromoted ≡ false

    legalAuthorityPromoted : Bool
    legalAuthorityPromotedIsFalse : legalAuthorityPromoted ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

    runtimeReceiptReference : String
open RuntimePNFControversyReceipt public

record ReceiptIndexedLeeRuntimeClosure : Set where
  constructor receipt-indexed-lee-runtime-closure
  field
    runtimeReceipt : RuntimePNFControversyReceipt
    formalOwnerReference : String
    closureReference : String
open ReceiptIndexedLeeRuntimeClosure public

------------------------------------------------------------------------
-- Compatibility/status reconciliation.
------------------------------------------------------------------------

legacyCanonicalRuntimeFlagRemainsHistorical :
  Legacy.LeeSensibLawBidiClosure.actualRuntimeEmissionReceiptAcquired
    Legacy.canonicalLeeSensibLawBidiClosure
  ≡ false
legacyCanonicalRuntimeFlagRemainsHistorical = refl

record RuntimeClosureBoundary : Set where
  constructor runtime-closure-boundary
  field
    legacyFalseFlagNegatesFutureReceipt : Bool
    legacyFalseFlagNegatesFutureReceiptIsFalse :
      legacyFalseFlagNegatesFutureReceipt ≡ false

    receiptCreatesSemanticAuthority : Bool
    receiptCreatesSemanticAuthorityIsFalse :
      receiptCreatesSemanticAuthority ≡ false

    receiptCreatesLegalAuthority : Bool
    receiptCreatesLegalAuthorityIsFalse :
      receiptCreatesLegalAuthority ≡ false

    receiptCreatesApplicability : Bool
    receiptCreatesApplicabilityIsFalse :
      receiptCreatesApplicability ≡ false

    receiptCreatesClaimTruth : Bool
    receiptCreatesClaimTruthIsFalse :
      receiptCreatesClaimTruth ≡ false

    maboOrOtherMatterReceiptIsEmpiricalLeeExperiment : Bool
    maboOrOtherMatterReceiptIsEmpiricalLeeExperimentIsFalse :
      maboOrOtherMatterReceiptIsEmpiricalLeeExperiment ≡ false
open RuntimeClosureBoundary public

canonicalRuntimeClosureBoundary : RuntimeClosureBoundary
canonicalRuntimeClosureBoundary =
  runtime-closure-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Attribution boundary.
--
-- A real SLR/PNF controversy receipt may pay the DASHI runtime-closure
-- obligation for this architecture.  It does not retroactively turn that
-- matter into a Justice Lee experiment, nor does it attribute DASHI runtime
-- structures or proofs to Justice Lee.
------------------------------------------------------------------------
