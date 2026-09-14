module DASHI.Law.SensibLawInstitutionalNormativityRoadmapRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawInstitutionalNormativityRoadmapExact as Roadmap

coreStructuralSpineAuthoredRegression :
  Roadmap.coreStructuralSpineAuthored Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ true
coreStructuralSpineAuthoredRegression = refl

sourceFixturesBoundedRegression :
  Roadmap.majorSourceFixturesBounded Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ true
sourceFixturesBoundedRegression = refl

israeliDomesticBoundedSearchAuthoredRegression :
  Roadmap.israeliDomesticLawBoundedSearchReceiptAuthored
    Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ true
israeliDomesticBoundedSearchAuthoredRegression = refl

israeliDomesticLawComprehensiveRegression :
  Roadmap.israeliDomesticLawComprehensiveFixturePaid Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ false
israeliDomesticLawComprehensiveRegression = refl

tasmaniaPrimaryArchiveAcquisitionFrontierRegression :
  Roadmap.tasmaniaPrimaryArchiveAcquisitionFrontierAuthored
    Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ true
tasmaniaPrimaryArchiveAcquisitionFrontierRegression = refl

tasmaniaPrimaryArchiveReplayRegression :
  Roadmap.tasmaniaPrimaryArchiveReplayPaid Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ false
tasmaniaPrimaryArchiveReplayRegression = refl

familyCourtPrimaryRecordRegression :
  Roadmap.abc2026UnderlyingPrimaryCourtRecordPaid Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ false
familyCourtPrimaryRecordRegression = refl

caseSpecificLobbyingInfluenceRegression :
  Roadmap.caseSpecificLobbyingInfluencePaid Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ false
caseSpecificLobbyingInfluenceRegression = refl

nextParetoAcquisitionRegression :
  Roadmap.nextParetoFrontierIsAcquisitionAndApplicationNotGenericOntology
    Roadmap.canonicalInstitutionalNormativityRoadmap
  ≡ true
nextParetoAcquisitionRegression = refl
