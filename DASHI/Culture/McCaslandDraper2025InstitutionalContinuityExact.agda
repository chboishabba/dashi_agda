module DASHI.Culture.McCaslandDraper2025InstitutionalContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- McCASLAND: 2025 DRAPER INSTITUTIONAL CONTINUITY
--
-- Draper's 2025 Annual Report lists William Neil McCasland, Ph.D. among the
-- Members of the Corporation.  This is a primary institutional continuity
-- receipt in 2025.  It is not an employment receipt, programme assignment,
-- technical-custody receipt, clearance receipt, or evidence of event causation.
------------------------------------------------------------------------

record Draper2025InstitutionalContinuityReceipt : Set where
  constructor draper-2025-institutional-continuity-receipt
  field
    person : String
    institution : String
    roleLabel : String
    sourceReference : String
    sourceLocator : String
    namedIn2025GovernanceSurface : Bool
    namedIn2025GovernanceSurfaceIsTrue : namedIn2025GovernanceSurface ≡ true
    employmentEstablished : Bool
    employmentEstablishedIsFalse : employmentEstablished ≡ false
    exactProgrammeEstablished : Bool
    exactProgrammeEstablishedIsFalse : exactProgrammeEstablished ≡ false
    technicalCustodyEstablished : Bool
    technicalCustodyEstablishedIsFalse : technicalCustodyEstablished ≡ false
    eventLinkEstablished : Bool
    eventLinkEstablishedIsFalse : eventLinkEstablished ≡ false
    boundedReading : String

mccaslandDraper2025Continuity : Draper2025InstitutionalContinuityReceipt
mccaslandDraper2025Continuity = draper-2025-institutional-continuity-receipt
  "William Neil McCasland"
  "The Charles Stark Draper Laboratory, Inc."
  "Member of the Corporation"
  "Draper 2025 Annual Report"
  "Annual Report 2025 p.41, Members of the Corporation"
  true refl
  false refl
  false refl
  false refl
  false refl
  "Draper's FY2025 governance page names William Neil McCasland as a Member of the Corporation. This establishes a 2025 institutional continuity surface only; it does not establish employment, portfolio ownership, access credentials, programme assignment, or a connection to the later disappearance."

record DraperContinuityBoundary : Set where
  constructor draper-continuity-boundary
  field
    corporationMemberImpliesEmployee : Bool
    corporationMemberImpliesEmployeeIsFalse : corporationMemberImpliesEmployee ≡ false
    corporationMemberImpliesProgrammeAccess : Bool
    corporationMemberImpliesProgrammeAccessIsFalse : corporationMemberImpliesProgrammeAccess ≡ false
    corporationMemberImpliesBlueHaloRoleContinuity : Bool
    corporationMemberImpliesBlueHaloRoleContinuityIsFalse : corporationMemberImpliesBlueHaloRoleContinuity ≡ false

canonicalDraperContinuityBoundary : DraperContinuityBoundary
canonicalDraperContinuityBoundary = draper-continuity-boundary
  false refl
  false refl
  false refl
