module DASHI.Interop.MaboRadicalTitleExactSourcePaymentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.MaboSourceConditionedReadingProjectionExact as Parent

------------------------------------------------------------------------
-- ONE-COORDINATE EXACT SOURCE PAYMENT
--
-- Runtime counterparts:
--   SensibLaw/src/storage/postgres/mabo_radical_title_source.py
--   SensibLaw/src/storage/postgres/semantic_reader_projection.py
--
-- This owner pays only the ability to reopen one exact Brennan J radical-title
-- passage after PostgreSQL has retained the source revision, canonical document,
-- exact span and valid bounds, and the retained literal matches the declared
-- anchor. It does not pay the wider Mabo proof chain, applicability or truth.
------------------------------------------------------------------------

record RadicalTitleSourceCoordinate : Set where
  constructor radicalTitleSourceCoordinate
  field
    caseCitation : String
    clrLocator : String
    judgeReference : String
    authorityIdentityReference : String
    manifestationReference : String
    sourceRevisionReference : String
    documentReference : String
    spanReference : String
    literalAnchorReference : String

open RadicalTitleSourceCoordinate public

canonicalRadicalTitleCoordinate : RadicalTitleSourceCoordinate
canonicalRadicalTitleCoordinate = radicalTitleSourceCoordinate
  "Mabo v Queensland (No 2) [1992] HCA 23"
  "175 CLR 1, 48-49"
  "Brennan J"
  "authority:mabo:1992:hca:23"
  "manifestation:mabo:1992:hca:23:wikisource:page-39"
  "source-revision:mabo:1992:hca:23:wikisource:page-39:2026-06-22"
  "document:mabo:1992:hca:23:brennan:wikisource-page-39"
  "span:mabo:brennan:radical-title:no-automatic-beneficial-ownership"
  "radical-title-no-automatic-absolute-beneficial-title"

record ExactRadicalTitlePayment : Set where
  constructor exactRadicalTitlePayment
  field
    postgresPayment : Parent.PostgresMaboSourcePayment
    sameAuthorityManifestationWeld : Bool
    exactLiteralAnchorMatched : Bool
    propositionChainPaid : Bool
    applicabilityPaid : Bool
    claimTruthPaid : Bool

open ExactRadicalTitlePayment public

exactRadicalTitleSourceReady : ExactRadicalTitlePayment → Bool
exactRadicalTitleSourceReady p with Parent.exactSourcePayment (postgresPayment p)
... | false = false
... | true with sameAuthorityManifestationWeld p
...   | false = false
...   | true = exactLiteralAnchorMatched p

data ExactReaderDisposition : Set where
  executeExactSource
  deferExactSource
  deferDetailedWhy : ExactReaderDisposition

exactRadicalTitleDisposition :
  ExactRadicalTitlePayment → Parent.ReaderAction → ExactReaderDisposition
exactRadicalTitleDisposition p Parent.sourceAction with exactRadicalTitleSourceReady p
... | true = executeExactSource
... | false = deferExactSource
exactRadicalTitleDisposition p Parent.whyAction = deferDetailedWhy
exactRadicalTitleDisposition p Parent.explainAction = executeExactSource
exactRadicalTitleDisposition p Parent.contextAction = executeExactSource

canonicalPaidSpan : ExactRadicalTitlePayment
canonicalPaidSpan = exactRadicalTitlePayment
  Parent.exactSpanPaid
  true
  true
  false
  false
  false

staleLiteralSpan : ExactRadicalTitlePayment
staleLiteralSpan = exactRadicalTitlePayment
  Parent.exactSpanPaid
  true
  false
  false
  false
  false

wrongManifestation : ExactRadicalTitlePayment
wrongManifestation = exactRadicalTitlePayment
  Parent.exactSpanPaid
  false
  true
  false
  false
  false

paidSpanExecutesSource :
  exactRadicalTitleDisposition canonicalPaidSpan Parent.sourceAction
    ≡ executeExactSource
paidSpanExecutesSource = refl

paidSpanStillDefersWhy :
  exactRadicalTitleDisposition canonicalPaidSpan Parent.whyAction
    ≡ deferDetailedWhy
paidSpanStillDefersWhy = refl

staleLiteralCannotPaySource :
  exactRadicalTitleDisposition staleLiteralSpan Parent.sourceAction
    ≡ deferExactSource
staleLiteralCannotPaySource = refl

wrongManifestationCannotPaySource :
  exactRadicalTitleDisposition wrongManifestation Parent.sourceAction
    ≡ deferExactSource
wrongManifestationCannotPaySource = refl

paidSpanDoesNotPayApplicability : applicabilityPaid canonicalPaidSpan ≡ false
paidSpanDoesNotPayApplicability = refl

paidSpanDoesNotPayTruth : claimTruthPaid canonicalPaidSpan ≡ false
paidSpanDoesNotPayTruth = refl

paidSpanDoesNotPayProofChain : propositionChainPaid canonicalPaidSpan ≡ false
paidSpanDoesNotPayProofChain = refl

------------------------------------------------------------------------
-- Identity/provenance firewalls.
------------------------------------------------------------------------

data ManifestationIdentityEqualsAuthorityIdentityPermission : Set where
data ExactLiteralCreatesApplicabilityPermission : Set where
data ExactLiteralCreatesClaimTruthPermission : Set where
data ExactLiteralCreatesProofChainPermission : Set where
\data StaleLiteralMayExecuteSourcePermission : Set where

manifestationIdentityCannotCollapseIntoAuthorityIdentity :
  ManifestationIdentityEqualsAuthorityIdentityPermission → ⊥
manifestationIdentityCannotCollapseIntoAuthorityIdentity ()

exactLiteralCannotCreateApplicability :
  ExactLiteralCreatesApplicabilityPermission → ⊥
exactLiteralCannotCreateApplicability ()

exactLiteralCannotCreateClaimTruth :
  ExactLiteralCreatesClaimTruthPermission → ⊥
exactLiteralCannotCreateClaimTruth ()

exactLiteralCannotCreateProofChain :
  ExactLiteralCreatesProofChainPermission → ⊥
exactLiteralCannotCreateProofChain ()

staleLiteralCannotExecuteSource :
  StaleLiteralMayExecuteSourcePermission → ⊥
staleLiteralCannotExecuteSource ()

sensibLawExactSourceOwner : String
sensibLawExactSourceOwner =
  "src/storage/postgres/mabo_radical_title_source.py"

itirPaymentConsumer : String
itirPaymentConsumer =
  "itir-svelte/src/lib/workbench/maboSourceProjection.js"

sourceWritten : Bool
sourceWritten = true

focusedRuntimeReceiptObserved : Bool
focusedRuntimeReceiptObserved = true

agdaKernelReceiptObserved : Bool
agdaKernelReceiptObserved = false
