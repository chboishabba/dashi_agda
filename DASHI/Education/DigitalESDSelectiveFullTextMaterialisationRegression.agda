module DASHI.Education.DigitalESDSelectiveFullTextMaterialisationRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact as Sparse

metadataUniverseCannotForceFullText :
  Sparse.MetadataUniverseForcesFullTextMaterialisation → ⊥
metadataUniverseCannotForceFullText =
  Sparse.metadataUniverseDoesNotForceFullTextMaterialisation

unreviewedCannotEnterFetchBatch :
  Sparse.UnreviewedRecordMayEnterFullTextBatch → ⊥
unreviewedCannotEnterFetchBatch =
  Sparse.unreviewedRecordDoesNotEnterFullTextBatch

budgetCannotBeIgnored :
  Sparse.FullTextBatchMayIgnoreStorageBudget → ⊥
budgetCannotBeIgnored =
  Sparse.fullTextBatchDoesNotIgnoreStorageBudget

cacheRegistrationCannotCreateAdmission :
  Sparse.CacheRegistrationCreatesSourceAuditAdmission → ⊥
cacheRegistrationCannotCreateAdmission =
  Sparse.cacheRegistrationDoesNotCreateSourceAuditAdmission

evictionCannotDestroyUnpaidEvidence :
  Sparse.UnprocessedArtifactMayBeEvictedAsPaid → ⊥
evictionCannotDestroyUnpaidEvidence =
  Sparse.unprocessedArtifactDoesNotBecomeEvictable


metadataOnlyUnreviewedCannotCreateRetrievalResidual :
  Material.MetadataOnlyUnreviewedCreatesRetrievalResidual → ⊥
metadataOnlyUnreviewedCannotCreateRetrievalResidual =
  Material.metadataOnlyUnreviewedDoesNotCreateRetrievalResidual

retrievalResidualCannotCreateSourceTruth :
  Material.RetrievalResidualCreatesSourceTruth → ⊥
retrievalResidualCannotCreateSourceTruth =
  Material.retrievalResidualDoesNotCreateSourceTruth

retrievalResidualCannotCreateReviewedEvidence :
  Material.RetrievalResidualCreatesReviewedEvidence → ⊥
retrievalResidualCannotCreateReviewedEvidence =
  Material.retrievalResidualDoesNotCreateReviewedEvidence
