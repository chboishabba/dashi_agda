module DASHI.Culture.AmyEskridgeInstituteEntityContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AMY ESKRIDGE / INSTITUTE ENTITY CONTINUITY
--
-- SEC and federal PPP records establish a multi-year corporate/entity surface
-- spanning 2019-2021.  These records do not establish that PPP funds financed
-- gravity research, that four reported jobs were technical staff, or that Amy
-- personally held the Institute's technical assets.
------------------------------------------------------------------------

record InstituteEntityContinuityReceipt : Set where
  constructor institute-entity-continuity-receipt
  field
    entity : String
    sec2019Reference : String
    ppp2020Reference : String
    ppp2021Reference : String
    secCorporateSurfaceOwned : Bool
    secCorporateSurfaceOwnedIsTrue : secCorporateSurfaceOwned ≡ true
    ppp2020EntitySurfaceOwned : Bool
    ppp2020EntitySurfaceOwnedIsTrue : ppp2020EntitySurfaceOwned ≡ true
    ppp2021EntitySurfaceOwned : Bool
    ppp2021EntitySurfaceOwnedIsTrue : ppp2021EntitySurfaceOwned ≡ true
    reportedJobs2020 : String
    reportedJobs2021 : String
    technicalResearchFundingEstablished : Bool
    technicalResearchFundingEstablishedIsFalse : technicalResearchFundingEstablished ≡ false
    technicalStaffIdentityEstablished : Bool
    technicalStaffIdentityEstablishedIsFalse : technicalStaffIdentityEstablished ≡ false
    technicalAssetCustodyEstablished : Bool
    technicalAssetCustodyEstablishedIsFalse : technicalAssetCustodyEstablished ≡ false
    boundedReading : String

instituteEntityContinuity : InstituteEntityContinuityReceipt
instituteEntityContinuity = institute-entity-continuity-receipt
  "Institute, P.B.C. / The Institute P.B.C., Inc."
  "SEC CIK 0001771320, accession 0001771320-19-000001, Form D filed 2019-03-27"
  "SBA/USAspending PPP loan 4113067104 / ASST_NON_4113067104_073, approved 2020-04-12"
  "SBA/USAspending PPP loan 9243538906 / ASST_NON_9243538906_073, approved 2021-05-12"
  true refl
  true refl
  true refl
  "4"
  "4"
  false refl
  false refl
  false refl
  "Issuer-filed SEC and federal payroll-relief records support a multi-year Institute entity/operating surface through 2021. PPP was payroll relief, not an antigravity R&D award; jobs reported are not identified here as scientists or as holders of any technical carrier."

record InstituteEntityContinuityBoundary : Set where
  constructor institute-entity-continuity-boundary
  field
    payrollReliefImpliesResearchFunding : Bool
    payrollReliefImpliesResearchFundingIsFalse : payrollReliefImpliesResearchFunding ≡ false
    fourJobsImpliesFourTechnicalResearchers : Bool
    fourJobsImpliesFourTechnicalResearchersIsFalse : fourJobsImpliesFourTechnicalResearchers ≡ false
    entityContinuityImpliesAmyTechnicalCustody : Bool
    entityContinuityImpliesAmyTechnicalCustodyIsFalse : entityContinuityImpliesAmyTechnicalCustody ≡ false

canonicalInstituteEntityContinuityBoundary : InstituteEntityContinuityBoundary
canonicalInstituteEntityContinuityBoundary = institute-entity-continuity-boundary
  false refl
  false refl
  false refl
