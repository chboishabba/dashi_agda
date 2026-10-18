module DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact as Ingest
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical

------------------------------------------------------------------------
-- INGEST-1A durable long-document persistence boundary.
--
-- Persistence/reload preserves the already-welded source/revision/span and
-- exhaustive region partition. Durable storage is not review, semantic
-- admission, legal applicability, or truth payment.
------------------------------------------------------------------------

record PersistedGenericSource
    (source : Ingest.GenericCompiledSource) : Set where
  constructor persisted-generic-source
  field
    persistedSourceRevisionRef :
      Canonical.revisionSourceRevisionRef
        (Ingest.GenericCompiledSource.revision source)
      ≡ Canonical.manifestationSourceRevisionRef
          (Ingest.GenericCompiledSource.manifestation source)

    canonicalBytesReloadable : Bool
    canonicalBytesReloadableIsTrue :
      canonicalBytesReloadable ≡ true

    reloadPreservesContentDigest : Bool
    reloadPreservesContentDigestIsTrue :
      reloadPreservesContentDigest ≡ true

    persistenceCreatesSemanticAuthority : Bool
    persistenceCreatesSemanticAuthorityIsFalse :
      persistenceCreatesSemanticAuthority ≡ false

    persistenceCreatesReviewPayment : Bool
    persistenceCreatesReviewPaymentIsFalse :
      persistenceCreatesReviewPayment ≡ false

    persistenceCreatesApplicability : Bool
    persistenceCreatesApplicabilityIsFalse :
      persistenceCreatesApplicability ≡ false

    persistenceCreatesClaimTruth : Bool
    persistenceCreatesClaimTruthIsFalse :
      persistenceCreatesClaimTruth ≡ false

open PersistedGenericSource public

record PersistedLongDocumentCompilation
    (source : Ingest.GenericCompiledSource) : Set where
  constructor persisted-long-document-compilation
  field
    sourcePersistence : PersistedGenericSource source

    originalReceipt : Ingest.LosslessCompilationReceipt source
    reloadedAssignments :
      List (Ingest.RegionCompilationAssignment source)

    reloadPreservesExactPartition :
      reloadedAssignments
      ≡ Ingest.LosslessCompilationReceipt.assignments originalReceipt

    reloadCreatesSemanticAuthority : Bool
    reloadCreatesSemanticAuthorityIsFalse :
      reloadCreatesSemanticAuthority ≡ false

    reloadCreatesReviewPayment : Bool
    reloadCreatesReviewPaymentIsFalse :
      reloadCreatesReviewPayment ≡ false

    reloadCreatesClaimTruth : Bool
    reloadCreatesClaimTruthIsFalse :
      reloadCreatesClaimTruth ≡ false

    parserResidualReloadCreatesAbsence : Bool
    parserResidualReloadCreatesAbsenceIsFalse :
      parserResidualReloadCreatesAbsence ≡ false

open PersistedLongDocumentCompilation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PersistenceCreatesSemanticAuthority : Set where
data PersistenceCreatesReviewPayment : Set where
data PersistenceCreatesApplicability : Set where
data PersistenceCreatesClaimTruth : Set where
data ReloadChangesRegionPartition : Set where
data ReloadedResidualCreatesAbsence : Set where

persistenceDoesNotCreateSemanticAuthority :
  PersistenceCreatesSemanticAuthority → ⊥
persistenceDoesNotCreateSemanticAuthority ()

persistenceDoesNotCreateReviewPayment :
  PersistenceCreatesReviewPayment → ⊥
persistenceDoesNotCreateReviewPayment ()

persistenceDoesNotCreateApplicability :
  PersistenceCreatesApplicability → ⊥
persistenceDoesNotCreateApplicability ()

persistenceDoesNotCreateClaimTruth :
  PersistenceCreatesClaimTruth → ⊥
persistenceDoesNotCreateClaimTruth ()

reloadDoesNotChangeRegionPartition :
  ReloadChangesRegionPartition → ⊥
reloadDoesNotChangeRegionPartition ()

reloadedResidualDoesNotCreateAbsence :
  ReloadedResidualCreatesAbsence → ⊥
reloadedResidualDoesNotCreateAbsence ()
