module DASHI.Interop.MaboSourceConditionedReadingProjectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SemanticReaderElucidatoryConeExact as Reader
import DASHI.Interop.SensibLawMaboProgressiveExplanationProjectionExact as Mabo

------------------------------------------------------------------------
-- POSTGRESQL-CONDITIONED MABO READING PROJECTION
--
-- Runtime counterpart:
--   SensibLaw/src/storage/postgres/semantic_reader_projection.py
--
-- PostgreSQL is the active semantic persistence spine.  A persisted legal
-- source revision pays retrieval readiness only.  Source execution additionally
-- requires the requested exact span to be persisted on the same canonical
-- document with valid coordinates.  Proposition support, applicability, and
-- legal truth remain separate payments.
------------------------------------------------------------------------

record PostgresMaboSourcePayment : Set where
  constructor postgresMaboSourcePayment
  field
    sourceRevisionReference : String
    canonicalDocumentReference : String
    requestedSpanReference : String
    sourceRevisionPersisted : Bool
    canonicalDocumentPersisted : Bool
    exactRequestedSpanPersisted : Bool
    exactSpanBoundsValid : Bool
    propositionChainPaid : Bool
    applicabilityPaid : Bool
    claimTruthPaid : Bool

open PostgresMaboSourcePayment public

data ReaderAction : Set where
  explainAction
  contextAction
  sourceAction
  whyAction : ReaderAction

data ReaderDisposition : Set where
  executeDisposition
  deferExactAuthoritySpan
  deferDetailedPropositionChain : ReaderDisposition

exactSourcePayment : PostgresMaboSourcePayment → Bool
exactSourcePayment p with sourceRevisionPersisted p
... | false = false
... | true with canonicalDocumentPersisted p
...   | false = false
...   | true with exactRequestedSpanPersisted p
...     | false = false
...     | true = exactSpanBoundsValid p

postgresConditionedDisposition :
  PostgresMaboSourcePayment → ReaderAction → ReaderDisposition
postgresConditionedDisposition p explainAction = executeDisposition
postgresConditionedDisposition p contextAction = executeDisposition
postgresConditionedDisposition p sourceAction with exactSourcePayment p
... | true = executeDisposition
... | false = deferExactAuthoritySpan
postgresConditionedDisposition p whyAction with propositionChainPaid p
... | true = executeDisposition
... | false = deferDetailedPropositionChain

------------------------------------------------------------------------
-- Canonical fixtures expose the intended payment boundary.
------------------------------------------------------------------------

persistedRevisionOnly : PostgresMaboSourcePayment
persistedRevisionOnly = postgresMaboSourcePayment
  "source-revision:mabo-hca23"
  "document:mabo-hca23"
  "span:mabo:radical-title-native-title"
  true
  true
  false
  false
  false
  false
  false

exactSpanPaid : PostgresMaboSourcePayment
exactSpanPaid = postgresMaboSourcePayment
  "source-revision:mabo-hca23"
  "document:mabo-hca23"
  "span:mabo:radical-title-native-title"
  true
  true
  true
  true
  false
  false
  false

persistedRevisionStillDefersSource :
  postgresConditionedDisposition persistedRevisionOnly sourceAction
    ≡ deferExactAuthoritySpan
persistedRevisionStillDefersSource = refl

exactSpanExecutesSource :
  postgresConditionedDisposition exactSpanPaid sourceAction
    ≡ executeDisposition
exactSpanExecutesSource = refl

exactSpanStillDefersWhy :
  postgresConditionedDisposition exactSpanPaid whyAction
    ≡ deferDetailedPropositionChain
exactSpanStillDefersWhy = refl

exactSpanDoesNotPayTruth : claimTruthPaid exactSpanPaid ≡ false
exactSpanDoesNotPayTruth = refl

------------------------------------------------------------------------
-- Existing semantic-reader and Mabo owners remain the parent contracts.
------------------------------------------------------------------------

semanticReaderAnchor : Reader.SemanticReaderParity
semanticReaderAnchor = Reader.canonicalSemanticReaderParity

maboRuntimeAnchor : Mabo.RuntimeReadingConeParity
maboRuntimeAnchor = Mabo.canonicalRuntimeReadingConeParity

------------------------------------------------------------------------
-- Firewalls: persistence and projection coordinates cannot launder authority.
------------------------------------------------------------------------

data PersistedRevisionCreatesExactSpanPermission : Set where
data ExactSpanCreatesPropositionSupportPermission : Set where
data PropositionSupportCreatesApplicabilityPermission : Set where
data PersistedRowCreatesClaimTruthPermission : Set where
data DetachedPresentationCreatesSemanticAuthorityPermission : Set where

data ReaderProseCreatesEvidencePaymentPermission : Set where

persistedRevisionCannotCreateExactSpan :
  PersistedRevisionCreatesExactSpanPermission → ⊥
persistedRevisionCannotCreateExactSpan ()

exactSpanCannotCreatePropositionSupport :
  ExactSpanCreatesPropositionSupportPermission → ⊥
exactSpanCannotCreatePropositionSupport ()

propositionSupportCannotCreateApplicability :
  PropositionSupportCreatesApplicabilityPermission → ⊥
propositionSupportCannotCreateApplicability ()

persistedRowCannotCreateClaimTruth :
  PersistedRowCreatesClaimTruthPermission → ⊥
persistedRowCannotCreateClaimTruth ()

detachedPresentationCannotCreateSemanticAuthority :
  DetachedPresentationCreatesSemanticAuthorityPermission → ⊥
detachedPresentationCannotCreateSemanticAuthority ()

readerProseCannotCreateEvidencePayment :
  ReaderProseCreatesEvidencePaymentPermission → ⊥
readerProseCannotCreateEvidencePayment ()

------------------------------------------------------------------------
-- Concrete storage references and certification coordinates.
------------------------------------------------------------------------

sensibLawRuntimeReference : String
sensibLawRuntimeReference =
  "src/storage/postgres/semantic_reader_projection.py"

postgresPersistenceDoctrineReference : String
postgresPersistenceDoctrineReference =
  "database/postgres_migrations/README.md"

sourceWritten : Bool
sourceWritten = true

runtimeFocusedReceiptObserved : Bool
runtimeFocusedReceiptObserved = true

runtimeRepositoryToolchainReceiptObserved : Bool
runtimeRepositoryToolchainReceiptObserved = false

agdaKernelReceiptObserved : Bool
agdaKernelReceiptObserved = false
