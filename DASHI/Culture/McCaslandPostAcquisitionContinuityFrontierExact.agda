module DASHI.Culture.McCaslandPostAcquisitionContinuityFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationCapabilityCustodyBidiExact as C

------------------------------------------------------------------------
-- McCASLAND EVENT-TIME ORGANISATIONAL CONTINUITY
--
-- Primary/near-primary corporate sources:
-- ATA appointment announcement, 2014-01-07 (company-issued via PR Newswire).
-- AeroVironment acquisition close announcement, 2025-05-01.
-- SEC filings describing the BlueHalo acquisition and segment incorporation.
------------------------------------------------------------------------

record McCaslandTransitionSurface : Set where
  constructor mccasland-transition-surface
  field
    ataDirectorTechnologyRoleOwned : Bool
    ataRoleScope : String
    blueHaloAcquiredByAeroVironment : Bool
    acquisitionCloseDate : String
    acquisitionIntegrationSurface : String
    postAcquisitionMcCaslandRoleOwned : Bool
    postAcquisitionAccessOwned : Bool
    postAcquisitionPortfolioOwned : Bool
    sourceReference : String

open McCaslandTransitionSurface public

mccaslandTransitionSurface : McCaslandTransitionSurface
mccaslandTransitionSurface = mccasland-transition-surface
  true
  "technology identification and development across ATA competencies/applications; IRAD leadership; technology guidance/support/risk assessment across ATA programmes"
  true
  "2025-05-01"
  "AeroVironment states BlueHalo was incorporated into the combined company and SEC filings place BlueHalo into AV segments after the acquisition"
  false
  false
  false
  "ATA appointment release 2014-01-07; AeroVironment BlueHalo completion release 2025-05-01; AV SEC acquisition filings"

mccaslandPostAcquisitionContinuity : C.AccessContinuityReceipt
mccaslandPostAcquisitionContinuity = C.access-continuity-receipt
  "ATA/BlueHalo/AeroVironment application-transformation portfolio"
  "ATA Director of Technology role established from 2014"
  "post-2025-05-01 AeroVironment/BlueHalo role"
  false
  "AeroVironment acquisition closed 2025-05-01; no primary event-time source located in this pass fixing McCasland's exact post-close title, programme portfolio or access"
  "The acquisition is a real organisational transition surface close to the 2026 disappearance. It does not prove adverse change, targeting, access removal or role continuity/discontinuity."

record McCaslandPostAcquisitionBoundary : Set where
  constructor mccasland-post-acquisition-boundary
  field
    preAcquisitionRoleImpliesPostAcquisitionRole : Bool
    preAcquisitionRoleImpliesPostAcquisitionRoleIsFalse : preAcquisitionRoleImpliesPostAcquisitionRole ≡ false
    acquisitionImpliesAccessRevocation : Bool
    acquisitionImpliesAccessRevocationIsFalse : acquisitionImpliesAccessRevocation ≡ false
    acquisitionImpliesTargeting : Bool
    acquisitionImpliesTargetingIsFalse : acquisitionImpliesTargeting ≡ false
    acquisitionCreatesEventTimeContinuityQuestion : Bool
    acquisitionCreatesEventTimeContinuityQuestionIsTrue : acquisitionCreatesEventTimeContinuityQuestion ≡ true

canonicalMcCaslandPostAcquisitionBoundary : McCaslandPostAcquisitionBoundary
canonicalMcCaslandPostAcquisitionBoundary = mccasland-post-acquisition-boundary false refl false refl false refl true refl

data McCaslandPostAcquisitionReverseTarget : Set where
  acquire2025to2026Title : McCaslandPostAcquisitionReverseTarget
  acquire2025to2026ProgrammePortfolio : McCaslandPostAcquisitionReverseTarget
  acquireIRADAuthorityAfterClose : McCaslandPostAcquisitionReverseTarget
  acquireAccessCredentialContinuity : McCaslandPostAcquisitionReverseTarget
  acquireReportingLineAfterClose : McCaslandPostAcquisitionReverseTarget
  acquireHandoverOrSuccessor : McCaslandPostAcquisitionReverseTarget
  acquireRoleChangeOrExitRecord : McCaslandPostAcquisitionReverseTarget
