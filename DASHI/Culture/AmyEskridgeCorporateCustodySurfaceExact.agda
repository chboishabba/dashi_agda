module DASHI.Culture.AmyEskridgeCorporateCustodySurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationCapabilityCustodyBidiExact as C

------------------------------------------------------------------------
-- AMY ESKRIDGE CORPORATE / CUSTODY SURFACE
--
-- Primary institutional sources:
-- SEC Form D, CIK 0001771320, accession 0001771320-19-000001.
-- Official Alabama Secretary of State business-entity record (archived capture)
-- for The Institute P.B.C., Inc., entity 000-549-195.
------------------------------------------------------------------------

record InstituteCorporateSurface : Set where
  constructor institute-corporate-surface
  field
    delawareIssuer : Bool
    alabamaForeignCorporation : Bool
    amyPresidentAndDirector : Bool
    shantelButlerDirector : Bool
    nathanKloseDirector : Bool
    samuelReidDirector : Bool
    convertibleDebtOfferingUSD : String
    secReference : String
    alabamaEntityReference : String
    boundedReading : String

open InstituteCorporateSurface public

instituteCorporateSurface : InstituteCorporateSurface
instituteCorporateSurface = institute-corporate-surface
  true
  true
  true
  true
  true
  true
  "$555,000 convertible promissory note reported sold in the 2019 Form D"
  "SEC Form D CIK 0001771320, accession 0001771320-19-000001, filed 2019-03-27"
  "Alabama Secretary of State entity 000-549-195; The Institute P.B.C., Inc.; Delaware formation 2018-10-18; Alabama qualification 2019-04-12"
  "These records establish corporate structure, named directors, an issuer financing event and continuing Alabama entity existence. They do not identify technical IP ownership, apparatus title, repository custody, research-fund allocation or post-death disposition."

amyCorporateRoleReceipt : C.CapabilityCustodyReceipt
amyCorporateRoleReceipt = C.capability-custody-receipt
  "Institute for Exotic Science / Institute P.B.C. application programme"
  C.intellectualProperty
  C.custodyUnknown
  "Institute P.B.C.; Amy Eskridge Pettigrew was President and director in the 2019 SEC filing"
  "SEC Form D CIK 0001771320"
  "The filing establishes Amy's corporate authority but does not establish which technical IP or application carrier the corporation owned. Therefore IP custody remains unknown rather than inferred from office."

record EskridgeCorporateCustodyBoundary : Set where
  constructor eskridge-corporate-custody-boundary
  field
    presidentImpliesTechnicalIPOwner : Bool
    presidentImpliesTechnicalIPOwnerIsFalse : presidentImpliesTechnicalIPOwner ≡ false
    corporateFinancingImpliesResearchFunding : Bool
    corporateFinancingImpliesResearchFundingIsFalse : corporateFinancingImpliesResearchFunding ≡ false
    corporateExistenceImpliesApparatusSurvival : Bool
    corporateExistenceImpliesApparatusSurvivalIsFalse : corporateExistenceImpliesApparatusSurvival ≡ false
    namedDirectorImpliesExperimentPossession : Bool
    namedDirectorImpliesExperimentPossessionIsFalse : namedDirectorImpliesExperimentPossession ≡ false

canonicalEskridgeCorporateCustodyBoundary : EskridgeCorporateCustodyBoundary
canonicalEskridgeCorporateCustodyBoundary = eskridge-corporate-custody-boundary false refl false refl false refl false refl

data EskridgeCorporateCustodyReverseTarget : Set where
  acquireTechnicalIPAssignment : EskridgeCorporateCustodyReverseTarget
  acquireApparatusTitleAndLocation : EskridgeCorporateCustodyReverseTarget
  acquireRepositoryOwnership : EskridgeCorporateCustodyReverseTarget
  acquireNotebookCustody : EskridgeCorporateCustodyReverseTarget
  acquireLabOrLeaseRecord : EskridgeCorporateCustodyReverseTarget
  acquirePostDeathAssetDisposition : EskridgeCorporateCustodyReverseTarget
  acquireDirectorOrOfficerTransition : EskridgeCorporateCustodyReverseTarget
  acquireFundingUseForResearchObject : EskridgeCorporateCustodyReverseTarget
