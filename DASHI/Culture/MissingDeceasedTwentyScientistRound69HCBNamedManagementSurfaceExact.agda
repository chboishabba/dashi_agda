module DASHI.Culture.MissingDeceasedTwentyScientistRound69HCBNamedManagementSurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound66HCBTemporalInstitutionalOverlapExact as R66
import DASHI.Culture.MissingDeceasedTwentyScientistRound68HCBDOITechnicalLineageExact as R68

------------------------------------------------------------------------
-- ROUND 69: NAMED HCB MANAGEMENT SURFACE
--
-- Real programme-level sources identify named task managers on both sides of
-- HBTD/HCB:
--
--   * Robert Bernstein — AFRL Hydrocarbon Boost program manager;
--   * Joe Burnett — Aerojet Rocketdyne Hydrocarbon Boost Technology
--     Demonstrator program manager.
--
-- McCasland's primary-paid role remains AFRL commander during part of the
-- programme's active period.  The acquired named-management surfaces do not
-- identify him as the HCB programme manager or Aerojet HBTD programme manager.
-- This is a granularity correction, not proof that he exercised no higher-level
-- command/portfolio oversight.
------------------------------------------------------------------------

afrlNamedHCBProgramManager : Attribution.AttributedSource
afrlNamedHCBProgramManager = Attribution.mkNoDOISource
  "Air Force Research Laboratory / Edwards Air Force Base"
  "Air Force advances rocket technology, tests first full-scale component of Hydrocarbon Boost Program"
  "Edwards Air Force Base public article"
  "2016"
  "https://www.edwards.af.mil/News/Display/Article/934614/air-force-advances-rocket-technology-tests-first-full-scale-component-of-hydroc/"
  Attribution.governmentSource
  "Names Robert Bernstein as AFRL's Hydrocarbon Boost program manager and Shawn Phillips as Rocket Propulsion Division chief; does not name William N. McCasland as HCB programme manager."
  Attribution.publicAttribution

aerojetNamedHBTDProgramManager : Attribution.AttributedSource
aerojetNamedHBTDProgramManager = Attribution.mkNoDOISource
  "Aerojet Rocketdyne"
  "AFRL Rocket Lab Technology Demonstration Program Completes Testing on Full-Scale Turbopump Machinery"
  "Aerojet Rocketdyne partner/news release mirrored by Space Foundation"
  "2017"
  "https://www.spacefoundation.org/2017/05/12/afrl-rocket-lab-technology-demonstration-program-completes-testing-on-full-scale-turbopump-machinery/"
  Attribution.practitionerSource
  "Names Joe Burnett as Aerojet Rocketdyne program manager of the Hydrocarbon Boost Technology Demonstrator programme; does not identify William N. McCasland in that task-level management role."
  Attribution.publicAttribution

bernsteinNamedManagerPaid : Bool
bernsteinNamedManagerPaid = true

burnettNamedManagerPaid : Bool
burnettNamedManagerPaid = true

mccaslandNamedHCBProgramManagerPaid : Bool
mccaslandNamedHCBProgramManagerPaid = false

mccaslandNamedHBTDTaskManagerPaid : Bool
mccaslandNamedHBTDTaskManagerPaid = false

mccaslandAFRLCommanderPaid : Bool
mccaslandAFRLCommanderPaid = R66.mccaslandHCBInstitutionalTemporalOverlapPaid

hcbDOITechnicalLineagePaid : Bool
hcbDOITechnicalLineagePaid = R68.hcbExactObjectNowStronglyIdentified

commanderDoesNotEqualNamedProgrammeManager : Bool
commanderDoesNotEqualNamedProgrammeManager = true

namedProgrammeManagerDoesNotExhaustHigherCommandOversight : Bool
namedProgrammeManagerDoesNotExhaustHigherCommandOversight = true

namedManagerSurfaceDoesNotProveExclusiveManagement : Bool
namedManagerSurfaceDoesNotProveExclusiveManagement = true

namedManagerSurfaceWeakensDirectProgrammeManagerNarrative : Bool
namedManagerSurfaceWeakensDirectProgrammeManagerNarrative = true

namedManagerSurfaceDoesNotDisproveHigherLevelPortfolioOversight : Bool
namedManagerSurfaceDoesNotDisproveHigherLevelPortfolioOversight = true

mccaslandExactTaskOrReviewCarrierStillRequired : Bool
mccaslandExactTaskOrReviewCarrierStillRequired = true

nextCarrier : String
nextCarrier = "Search for McCasland on an exact HCB/Mondaloy programme review, funding approval, acquisition decision, contract-management memo, industry-day attendee/speaker roster, or task-level briefing. Generic command responsibility and derivative media claims are now dominated."

round69H2PaidCount : Nat
round69H2PaidCount = 0

round69H3PaidCount : Nat
round69H3PaidCount = 0

round69Reading : String
round69Reading = "The HCB management surface is now person-resolved at task level: primary/near-primary programme sources name Robert Bernstein as AFRL Hydrocarbon Boost program manager and Joe Burnett as Aerojet Rocketdyne HBTD program manager. McCasland remains primary-paid as AFRL commander during active HCB work, but is not named as HCB/HBTD programme manager on the acquired task-level management carriers. This weakens stronger derivative claims that he personally managed or directly supervised Reza's HCB/Mondaloy work, while leaving higher-level command/portfolio oversight possible. H2 remains unpaid pending a McCasland identity-bearing HCB/Mondaloy task/review/funding carrier."
