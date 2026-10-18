module DASHI.Education.DigitalESDERICStudyExecutionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDERICStudyExecutionExact as Exec

expectedRawOccurrences :
  Exec.expectedRawQueryOccurrenceCount ≡ 46597
expectedRawOccurrences = refl

expectedUniqueRecords :
  Exec.expectedUniqueERICRecordCount ≡ 43996
expectedUniqueRecords = refl

wrapperCannotCreateScreeningDecision :
  Exec.RealERICWrapperCreatesScreeningDecision → ⊥
wrapperCannotCreateScreeningDecision =
  Exec.realERICWrapperDoesNotCreateScreeningDecision

wrapperCannotCreateAdmission :
  Exec.RealERICWrapperCreatesSourceAuditAdmission → ⊥
wrapperCannotCreateAdmission =
  Exec.realERICWrapperDoesNotCreateSourceAuditAdmission

metadataCorpusCannotMasqueradeAsFullText :
  Exec.RealERICMetadataCorpusCountsAsFullTextCorpus → ⊥
metadataCorpusCannotMasqueradeAsFullText =
  Exec.realERICMetadataCorpusDoesNotCountAsFullTextCorpus

syntheticFixtureCannotPayRealExecution :
  Exec.SyntheticFixturePaysRealERICExecution → ⊥
syntheticFixtureCannotPayRealExecution =
  Exec.syntheticFixtureDoesNotPayRealERICExecution
