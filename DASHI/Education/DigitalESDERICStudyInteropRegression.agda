module DASHI.Education.DigitalESDERICStudyInteropRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDERICStudyInteropExact as ERIC

metadataCannotCreateDecision :
  ERIC.ParsedMetadataCreatesScreeningDecision → ⊥
metadataCannotCreateDecision =
  ERIC.parsedMetadataDoesNotCreateScreeningDecision

abstractCannotMasqueradeAsFullText :
  ERIC.ParsedAbstractCountsAsFullTextParsing → ⊥
abstractCannotMasqueradeAsFullText =
  ERIC.parsedAbstractDoesNotCountAsFullTextParsing

availabilityCannotMasqueradeAsRetrieval :
  ERIC.ERICFullTextAvailabilityCountsAsRetrievedArtifact → ⊥
availabilityCannotMasqueradeAsRetrieval =
  ERIC.ericFullTextAvailabilityDoesNotCountAsRetrievedArtifact

queryOverlapCannotCreateStudyIdentity :
  ERIC.QueryOverlapCreatesDuplicateStudyIdentity → ⊥
queryOverlapCannotCreateStudyIdentity =
  ERIC.queryOverlapDoesNotCreateDuplicateStudyIdentity

conflictingMetadataCannotMerge :
  ERIC.ConflictingMetadataMayBeSilentlyMerged → ⊥
conflictingMetadataCannotMerge =
  ERIC.conflictingMetadataCannotBeSilentlyMerged

syntheticFixtureIsNotERICCorpus :
  ERIC.SyntheticSLRFixtureCountsAsERICCorpus → ⊥
syntheticFixtureIsNotERICCorpus =
  ERIC.syntheticSLRFixtureDoesNotCountAsERICCorpus
