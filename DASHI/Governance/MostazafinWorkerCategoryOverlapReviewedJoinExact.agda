module DASHI.Governance.MostazafinWorkerCategoryOverlapReviewedJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.MostazafinRepresentedConstituencyDivergenceExact as Divergence

------------------------------------------------------------------------
-- CATEGORY-LEVEL OVERLAP:
--
-- historical Khomeinist discourse:
--   workers are incorporated into the broader mostazafin category
--
-- current empirical record:
--   workers/labour organisations participate in protest and are subject to
--   repression / representation constraints
--
-- This pays category overlap, not identity of every protester or person-level
-- continuity from 1979 to 2026.
------------------------------------------------------------------------

factoryDiscourseStudy : Source.AttributedSource
factoryDiscourseStudy = Source.mkDOISource
  "Paola Rivetti and contributors"
  "The Islamic Republican Party of Iran in the Factory: Control over Workers' Discourse in Posters (1979-1987)"
  "Middle Eastern Studies"
  "2018"
  "10.1080/05786967.2018.1423768"
  "https://www.tandfonline.com/doi/full/10.1080/05786967.2018.1423768"
  Source.academicArticleSource
  "peer-reviewed historical study explicitly describing workers as incorporated into the broader Khomeinist category of mostazafin; used only for the historical category relation"
  Source.publicAttribution

workerRights2026 : Source.AttributedSource
workerRights2026 = Source.mkNoDOISource
  "Worker Rights Watch / Volunteer Activists"
  "Workers Rights Watch - January to June 2026"
  "semi-annual labour monitoring report"
  "2026-07-31"
  "https://workerrightswatch.org/publications/jan-to-june-2026"
  (Source.namedSourceKind "labour-rights monitoring report")
  "documents 2026 labour protests, strikes, economic hardship and state restrictions; source role is labour-rights monitoring, not neutral state statistics"
  Source.publicAttribution

record CategoryOverlapReceipt : Set where
  constructor category-overlap-receipt
  field
    representedCategoryRef : String
    currentCohortRef : String
    historicalSource : Source.AttributedSource
    currentSource : Source.AttributedSource
    historicalMembershipRelationPaid : Bool
    historicalMembershipRelationPaidIsTrue :
      historicalMembershipRelationPaid ≡ true
    currentCohortPresencePaid : Bool
    currentCohortPresencePaidIsTrue :
      currentCohortPresencePaid ≡ true
    categoryOverlapPaid : Bool
    categoryOverlapPaidIsTrue :
      categoryOverlapPaid ≡ true
    everyCurrentProtesterInsideCategory : Bool
    everyCurrentProtesterInsideCategoryIsFalse :
      everyCurrentProtesterInsideCategory ≡ false
    sameHistoricalPersonsPersist : Bool
    sameHistoricalPersonsPersistIsFalse :
      sameHistoricalPersonsPersist ≡ false

open CategoryOverlapReceipt public

workerMostazafinCategoryOverlap : CategoryOverlapReceipt
workerMostazafinCategoryOverlap =
  category-overlap-receipt
    "historical Khomeinist mostazafin category includes workers"
    "2026 Iranian labour protest / strike cohort"
    factoryDiscourseStudy
    workerRights2026
    true refl
    true refl
    true refl
    false refl
    false refl

record CategoryDivergenceReceipt : Set where
  constructor category-divergence-receipt
  field
    overlap : CategoryOverlapReceipt
    divergenceCandidate : Divergence.StateActionDivergenceCandidate
    representedCategoryAndTargetedCohortOverlap : Bool
    representedCategoryAndTargetedCohortOverlapIsTrue :
      representedCategoryAndTargetedCohortOverlap ≡ true
    everyTargetedPersonProvedRepresented : Bool
    everyTargetedPersonProvedRepresentedIsFalse :
      everyTargetedPersonProvedRepresented ≡ false
    semanticBetrayalVerdictCreated : Bool
    semanticBetrayalVerdictCreatedIsFalse :
      semanticBetrayalVerdictCreated ≡ false

open CategoryDivergenceReceipt public

workerDivergence : CategoryDivergenceReceipt
workerDivergence =
  category-divergence-receipt
    workerMostazafinCategoryOverlap
    Divergence.labourDivergenceCandidate
    true refl
    false refl
    false refl

data CategoryOverlapMeansUniversalIdentity : Set where
data CategoryDivergenceMeansHypocrisyVerdict : Set where
data LabourMonitoringCreatesNeutralPopulationEstimate : Set where

categoryOverlapDoesNotCreateUniversalIdentity :
  CategoryOverlapMeansUniversalIdentity → ⊥
categoryOverlapDoesNotCreateUniversalIdentity ()

categoryDivergenceDoesNotCreateHypocrisyVerdict :
  CategoryDivergenceMeansHypocrisyVerdict → ⊥
categoryDivergenceDoesNotCreateHypocrisyVerdict ()

labourMonitoringDoesNotCreateNeutralPopulationEstimate :
  LabourMonitoringCreatesNeutralPopulationEstimate → ⊥
labourMonitoringDoesNotCreateNeutralPopulationEstimate ()

factoryStudySnowball :
  Snowball.SourceRoleSnowballReceipt factoryDiscourseStudy
factoryStudySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt factoryDiscourseStudy

workerRightsSnowball :
  Snowball.SourceRoleSnowballReceipt workerRights2026
workerRightsSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt workerRights2026
