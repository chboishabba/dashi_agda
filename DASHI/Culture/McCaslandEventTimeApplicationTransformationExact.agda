module DASHI.Culture.McCaslandEventTimeApplicationTransformationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EVENT-TIME APPLICATION TRANSFORMATION, MCCASLAND
--
-- Bounded to the post-USAF Applied Technology Associates role.  ATA's
-- contemporaneous appointment announcement names McCasland Director of
-- Technology and describes responsibility for technology identification,
-- development, technical vision and strategy.  ATA public releases separately
-- document applied work in space-vehicle technology, target acquisition/
-- tracking, counter-UAS directed energy and related precision systems.
--
-- This is not a claim that McCasland personally owned every ATA programme,
-- every classified application, or any UAP-related technology.
------------------------------------------------------------------------

record EventTimeApplicationRole : Set where
  constructor event-time-application-role
  field
    person : String
    organisation : String
    role : String
    transformationResponsibility : String
    publicApplicationSurface : String
    sourceReference : String
    roleOwned : Bool
    roleOwnedIsTrue : roleOwned ≡ true
    exactProgrammeCarrierOwned : Bool
    exactProgrammeCarrierOwnedIsFalse : exactProgrammeCarrierOwned ≡ false

open EventTimeApplicationRole public

mcCaslandATAApplicationRole : EventTimeApplicationRole
mcCaslandATAApplicationRole = event-time-application-role
  "William Neil McCasland"
  "Applied Technology Associates (later within BlueHalo)"
  "Director of Technology"
  "identify and develop technologies; shape technical vision and strategy"
  "ATA public portfolio includes Space Vehicles Advanced Technology, target acquisition/tracking, and directed-energy/counter-UAS applications"
  "Applied Technology Associates appointment announcement, 7 Jan 2014, PR Newswire; ATA public contract releases 2014-2020"
  true refl
  false refl

record McCaslandApplicationBoundary : Set where
  constructor mccasland-application-boundary
  field
    technologyStrategyRoleImpliesEveryProgrammePossession : Bool
    technologyStrategyRoleImpliesEveryProgrammePossessionIsFalse :
      technologyStrategyRoleImpliesEveryProgrammePossession ≡ false
    directedEnergyPortfolioImpliesUAPTechnology : Bool
    directedEnergyPortfolioImpliesUAPTechnologyIsFalse :
      directedEnergyPortfolioImpliesUAPTechnology ≡ false
    priorSAPOversightImpliesEventTimeSAPPossession : Bool
    priorSAPOversightImpliesEventTimeSAPPossessionIsFalse :
      priorSAPOversightImpliesEventTimeSAPPossession ≡ false
    eventTimeRoleSupportsExactProgrammeSearch : Bool
    eventTimeRoleSupportsExactProgrammeSearchIsTrue :
      eventTimeRoleSupportsExactProgrammeSearch ≡ true

canonicalMcCaslandApplicationBoundary : McCaslandApplicationBoundary
canonicalMcCaslandApplicationBoundary = mccasland-application-boundary false refl false refl false refl true refl

data McCaslandApplicationReverseTarget : Set where
  acquireEventTimeProgrammeList : McCaslandApplicationReverseTarget
  acquireIRADOrTechnologyPortfolio : McCaslandApplicationReverseTarget
  acquireConfigurationOrIntegrationRole : McCaslandApplicationReverseTarget
  acquireProgrammeAccessReceipt : McCaslandApplicationReverseTarget
  acquireNamedSuccessorOrHandover : McCaslandApplicationReverseTarget
  acquireObserverOrReviewSurface : McCaslandApplicationReverseTarget
