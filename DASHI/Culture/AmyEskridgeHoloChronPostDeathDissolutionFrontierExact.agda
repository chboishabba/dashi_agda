module DASHI.Culture.AmyEskridgeHoloChronPostDeathDissolutionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HOLOCHRON POST-DEATH DISSOLUTION FRONTIER
--
-- A registry-derived OpenCorporates/archive surface reports HoloChron LLC
-- (Alabama company 000-524-283) as dissolved on 2022-12-28, after Amy's
-- 2022-06-11 death.  This module deliberately treats that as a secondary
-- registry index, not as the primary dissolution filing or proof of any motive.
------------------------------------------------------------------------

record ReportedDissolutionSurface : Set where
  constructor reported-dissolution-surface
  field
    entity : String
    companyNumber : String
    reportedDissolutionDate : String
    sourceReference : String
    secondaryRegistrySurfaceLocated : Bool
    secondaryRegistrySurfaceLocatedIsTrue : secondaryRegistrySurfaceLocated ≡ true
    primaryDissolutionFilingLocated : Bool
    primaryDissolutionFilingLocatedIsFalse : primaryDissolutionFilingLocated ≡ false
    windingUpTermsLocated : Bool
    windingUpTermsLocatedIsFalse : windingUpTermsLocated ≡ false
    technicalAssetDispositionLocated : Bool
    technicalAssetDispositionLocatedIsFalse : technicalAssetDispositionLocated ≡ false
    suspiciousMeaningEstablished : Bool
    suspiciousMeaningEstablishedIsFalse : suspiciousMeaningEstablished ≡ false
    boundedReading : String

holoChronReportedDissolution : ReportedDissolutionSurface
holoChronReportedDissolution = reported-dissolution-surface
  "HoloChron LLC"
  "Alabama 000-524-283"
  "2022-12-28"
  "Archived OpenCorporates registry-derived page citing Alabama Secretary of State as source"
  true refl
  false refl
  false refl
  false refl
  false refl
  "A secondary registry-derived surface reports post-death dissolution. This creates an acquisition target for the primary filing and winding-up records; it does not establish why the company dissolved or what happened to any technical assets."

data HoloChronDissolutionReverseTarget : Set where
  acquirePrimaryDissolutionFiling
  acquireFilingSignatory
  acquireMemberManagerState
  acquireWindingUpTerms
  acquireTechnicalIPDisposition
  acquireApparatusDisposition
  acquireRepositoryAccountDisposition
  acquireNotebookArchiveDisposition
  acquireCreditorOrAssigneeSurface
  : HoloChronDissolutionReverseTarget

record HoloChronDissolutionBoundary : Set where
  constructor holochron-dissolution-boundary
  field
    postDeathDissolutionImpliesSuspicion : Bool
    postDeathDissolutionImpliesSuspicionIsFalse : postDeathDissolutionImpliesSuspicion ≡ false
    secondaryRegistryImpliesPrimaryFilingContents : Bool
    secondaryRegistryImpliesPrimaryFilingContentsIsFalse : secondaryRegistryImpliesPrimaryFilingContents ≡ false
    companyDissolutionImpliesTechnicalAssetDestruction : Bool
    companyDissolutionImpliesTechnicalAssetDestructionIsFalse : companyDissolutionImpliesTechnicalAssetDestruction ≡ false

canonicalHoloChronDissolutionBoundary : HoloChronDissolutionBoundary
canonicalHoloChronDissolutionBoundary = holochron-dissolution-boundary
  false refl
  false refl
  false refl
