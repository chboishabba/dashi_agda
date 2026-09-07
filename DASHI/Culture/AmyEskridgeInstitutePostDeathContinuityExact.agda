module DASHI.Culture.AmyEskridgeInstitutePostDeathContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record InstituteContinuityReceipt : Set where
  constructor institute-continuity-receipt
  field
    entity : String
    preDeathOperatingSurface : String
    postDeathEntitySurface : String
    sourceReference : String
    boundedReading : String

open InstituteContinuityReceipt public

institutePostDeathContinuity : InstituteContinuityReceipt
institutePostDeathContinuity = institute-continuity-receipt
  "The Institute P.B.C. / The Institute P.B.C., Inc."
  "2019 SEC financing; 2020 and 2021 payroll-relief records; Alabama operating entity surface"
  "Archived Alabama Secretary of State record shows status Exists and annual-report years continuing after Amy Eskridge's 2022 death"
  "SEC Form D 2019-03-27; Alabama Secretary of State entity record archived at archive.ph/jk5xt; SBA/USAspending PPP records"
  "The corporate entity appears to persist after Amy Eskridge's death. Entity survival does not establish survival, transfer or custody of any exact gravity-modification apparatus, notebook, repository, calibration archive, raw/reduced data or technical IP."

record InstituteContinuityBoundary : Set where
  constructor institute-continuity-boundary
  field
    entitySurvivalImpliesTechnicalCarrierSurvival : Bool
    entitySurvivalImpliesTechnicalCarrierSurvivalIsFalse : entitySurvivalImpliesTechnicalCarrierSurvival ≡ false
    annualReportImpliesActiveResearchProgramme : Bool
    annualReportImpliesActiveResearchProgrammeIsFalse : annualReportImpliesActiveResearchProgramme ≡ false
    payrollSurfaceImpliesResearchPayroll : Bool
    payrollSurfaceImpliesResearchPayrollIsFalse : payrollSurfaceImpliesResearchPayroll ≡ false
    corporateContinuityImpliesPostDeathAssetTransfer : Bool
    corporateContinuityImpliesPostDeathAssetTransferIsFalse : corporateContinuityImpliesPostDeathAssetTransfer ≡ false

canonicalInstituteContinuityBoundary : InstituteContinuityBoundary
canonicalInstituteContinuityBoundary = institute-continuity-boundary false refl false refl false refl false refl

data InstitutePostDeathReverseTarget : Set where
  acquirePostDeathOfficers
  acquireAnnualReports
  acquireTechnicalIPSchedule
  acquireApparatusCustody
  acquireNotebookRepositoryCustody
  acquirePostDeathResearchActivity
  : InstitutePostDeathReverseTarget
