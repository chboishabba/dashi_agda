module DASHI.Education.DigitalESDSearchToSourceAuditAdmissionRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSearchToSourceAuditAdmissionExact as Weld

preScreenCandidateCannotJumpToCorpus :
  Weld.PreScreenCandidateCreatesCorpusAuditedSource → ⊥
preScreenCandidateCannotJumpToCorpus =
  Weld.preScreenCandidateDoesNotCreateCorpusAuditedSource

searchHitCannotJumpToCorpus :
  Weld.SearchHitCreatesCorpusAuditedSource → ⊥
searchHitCannotJumpToCorpus =
  Weld.searchHitDoesNotCreateCorpusAuditedSource

auditAdmissionDoesNotCreateSearchLineage :
  Weld.AuditAdmissionCreatesSearchLineage → ⊥
auditAdmissionDoesNotCreateSearchLineage =
  Weld.auditAdmissionDoesNotCreateSearchLineage

searchLineageDoesNotCreateAuditAdmission :
  Weld.SearchLineageCreatesAuditAdmission → ⊥
searchLineageDoesNotCreateAuditAdmission =
  Weld.searchLineageDoesNotCreateAuditAdmission
