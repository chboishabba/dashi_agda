module DASHI.Culture.AmyEskridgePOAMSObjectLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeObjectLineageBidiExact as L

------------------------------------------------------------------------
-- OBJECTS
------------------------------------------------------------------------

nasa2016Study : L.KnowledgeObject
nasa2016Study = L.knowledge-object
  "NASA MSFC / Quantum Machines POAMS experimental study (2015-2016)"
  L.experimentalStudy
  "NASA/TM-20205010911 retrospective account; SAA8-1519855"
  "The later NASA TM reports MSFC/QM POAMS experiments, including 2016 testing and proprietary-period constraints. This study is not silently identified with the later TM."

nasa2021TM : L.KnowledgeObject
nasa2021TM = L.knowledge-object
  "NASA/TM-20205010911 / M-1531"
  L.technicalReport
  "NASA NTRS 20205010911"
  "Public NASA Technical Memorandum acquired 1 Dec 2020 and published 1 Nov 2021, authored by R.H. Eskridge, M.A. Nelson and M.P. Schoenfeld."

instituteDerivedWork : L.KnowledgeObject
instituteDerivedWork = L.knowledge-object
  "Institute for Exotic Science derived/matured results described by Amy Eskridge"
  L.derivedPrivateWork
  "Amy Eskridge September 2020 captured statement; later Courtney Marchesani reconstruction"
  "Amy described additional Institute work that matured earlier NASA-origin science. Exact artifact identity and version history remain unrecovered."

amy2020ReviewObject : L.KnowledgeObject
amy2020ReviewObject = L.knowledge-object
  "Amy Eskridge September 2020 unnamed NASA-review / IP object"
  L.releaseReviewObject
  "Amy Eskridge September 2020 captured statement"
  "Amy described a NASA review/public-release dependency but did not name a paper title, M-1531, or NTRS 20205010911 in the recovered statement."

------------------------------------------------------------------------
-- SOURCE-BACKED / ATTRIBUTED LINEAGE
------------------------------------------------------------------------

studyToTM : L.KnowledgeObjectLineage
studyToTM = L.knowledge-object-lineage
  nasa2016Study
  nasa2021TM
  L.reportsResultsOf
  "NASA/TM-20205010911 describes the earlier MSFC/QM experiments, including V3/V5 work and 2016 testing."
  "The 2021 TM is a later report about the experimental programme; it is not definitionally the 2016 study itself."

studyToInstitute : L.KnowledgeObjectLineage
studyToInstitute = L.knowledge-object-lineage
  nasa2016Study
  instituteDerivedWork
  L.maturesFrom
  "Amy's 2020 account, as later reproduced/reconstructed, describes Institute work maturing earlier NASA-origin science."
  "This establishes a claimed derivational relation, not identity of the Institute work with the NASA study or final TM."

reviewToTMStrongCandidate : L.KnowledgeObjectLineage
reviewToTMStrongCandidate = L.knowledge-object-lineage
  amy2020ReviewObject
  nasa2021TM
  L.candidateSameObject
  "NASA NTRS timing/team/topic compatibility plus Courtney Marchesani's later report that Aiden Schaeffer referenced Eskridge-Nelson-Schoenfeld (2021) as the NASA paper Amy was transitioning."
  "Strong candidate relation only. The underlying Schaeffer X Spaces recording and a primary NASA review identifier have not been recovered."

reviewDependsOnEarlierNASAIP : L.KnowledgeObjectLineage
reviewDependsOnEarlierNASAIP = L.knowledge-object-lineage
  nasa2016Study
  amy2020ReviewObject
  L.dependsOnReleaseOf
  "Amy's 2020 account describes an intellectual-property/public-release process around earlier NASA-origin work before later Institute results could be demonstrated publicly."
  "A dependency on releasing earlier work does not prove the review object was literally the same document as either the 2016 study or the 2021 TM."

record CurrentPOAMSLineageAssessment : Set where
  constructor current-poams-lineage-assessment
  field
    earlierStudyDistinctFromLaterTM : Bool
    earlierStudyDistinctFromLaterTMIsTrue : earlierStudyDistinctFromLaterTM ≡ true
    instituteDerivedWorkDistinctFromEarlierStudy : Bool
    instituteDerivedWorkDistinctFromEarlierStudyIsTrue :
      instituteDerivedWorkDistinctFromEarlierStudy ≡ true
    reviewObjectToTMExactIdentityOwned : Bool
    reviewObjectToTMExactIdentityOwnedIsFalse :
      reviewObjectToTMExactIdentityOwned ≡ false
    reviewObjectToTMStrongCandidate : Bool
    reviewObjectToTMStrongCandidateIsTrue :
      reviewObjectToTMStrongCandidate ≡ true
    directSchaefferRecordingRecovered : Bool
    directSchaefferRecordingRecoveredIsFalse :
      directSchaefferRecordingRecovered ≡ false
    primaryNASAReviewIdentifierRecovered : Bool
    primaryNASAReviewIdentifierRecoveredIsFalse :
      primaryNASAReviewIdentifierRecovered ≡ false

canonicalCurrentPOAMSLineageAssessment : CurrentPOAMSLineageAssessment
canonicalCurrentPOAMSLineageAssessment = current-poams-lineage-assessment
  true refl
  true refl
  false refl
  true refl
  false refl
  false refl
