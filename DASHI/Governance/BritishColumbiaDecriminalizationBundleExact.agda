module DASHI.Governance.BritishColumbiaDecriminalizationBundleExact where

------------------------------------------------------------------------
-- BRITISH COLUMBIA DECRIMINALIZATION: INTERVENTION BUNDLE, NOT LABEL
--
-- The policy label "decriminalization" is not treated as a sufficient causal
-- description.  This module separates legal possession protection, public-space
-- rules, policing, harm-reduction/OAT service capacity, dedicated funding,
-- training, housing/poverty infrastructure, and measured outcomes over time.
--
-- SOURCES / BOUNDED ROLES
--
-- Province of British Columbia,
-- "Decriminalizing people who use drugs in B.C.", updated 2 March 2026;
-- no DOI asserted.  Primary policy source: pilot began in 2023, exemption
-- expired 31 January 2026 and was not renewed; monitoring domains include law
-- enforcement, wellbeing, pathways to services, system of care, seizures and
-- charges.
--
-- Canadian Institutes of Health Research (CIHR), Jürgen Rehm PI,
-- "Evaluation of the British Columbia Exemption to Allow for Personal
-- Possession of Small Amounts of Illegal Drugs: Progress Report Lay Summary:
-- November 2025-April 2026", modified 14 April 2026; no DOI asserted.
-- Bounded role: initial declines in possession seizures/cases/incarceration,
-- return toward pre-policy levels following amendment; minimal policy-related
-- service-delivery change, limited dedicated funding/training, persistent
-- staffing/resource constraints.
--
-- Becca Wood; Naomi Zakimi; Mieke Fraser; O Kara Loewen; Katie Fajber;
-- Brooke Kinniburgh; Charlene Burmeister; Iesha Henderson; Alissa Greer,
-- "Public drug use, policing, and the limits of decriminalization in British
-- Columbia: A mixed methods study", International Journal of Drug Policy
-- 151:105250 (2026), DOI 10.1016/j.drugpo.2026.105250.
-- Bounded role: 2024 HR Client Survey N=622 + interviews N=38; public-space
-- restrictions and displacement/surveillance disproportionately affect
-- unhoused/structurally vulnerable participants; housing/services/poverty
-- reduction identified as structural supports. Not a universal causal estimate.
--
-- "Exploring the early impacts of drug decriminalization on harm reduction and
-- opioid agonist treatment service operations and delivery in British
-- Columbia: insights from key informant interviews", BMC Public Health (2025),
-- DOI 10.1186/s12889-025-25479-x.
-- Bounded role: service-provider interviews; no substantial service adjustments,
-- staffing/resource shortages and insufficient dedicated support.
--
-- "Access to health and harm reduction services during drug decriminalization
-- in British Columbia, Canada: a mixed-method study", BMC Public Health (2026),
-- DOI 10.1186/s12889-026-26978-1.
-- Bounded role: barriers to health/harm-reduction access persisted; legal reform
-- alone may be insufficient without structural/institutional supports.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record BundleSource : Set where
  constructor bundleSource
  field
    authorsOrInstitution : String
    title : String
    year : Nat
    doiOrIdentifier : String
    boundedRole : String

open BundleSource public

data BundleAxis : Set where
  possessionProtection : BundleAxis
  publicSpaceProtection : BundleAxis
  policeConstraint : BundleAxis
  harmReductionCapacity : BundleAxis
  oatCapacity : BundleAxis
  dedicatedFunding : BundleAxis
  frontlineTraining : BundleAxis
  housingInfrastructure : BundleAxis
  povertyReductionInfrastructure : BundleAxis

data AxisState : Set where
  installed : AxisState
  partial : AxisState
  constrained : AxisState
  absentOrNotInstalled : AxisState
  unknown : AxisState

data PolicyPhase : Set where
  initialPilot : PolicyPhase
  postPublicSpaceAmendment : PolicyPhase
  postExpiry : PolicyPhase

record InterventionBundle : Set where
  constructor interventionBundle
  field
    phase : PolicyPhase
    possession : AxisState
    publicSpace : AxisState
    policing : AxisState
    harmReduction : AxisState
    oat : AxisState
    funding : AxisState
    training : AxisState
    housing : AxisState
    povertyReduction : AxisState

open InterventionBundle public

initialPilotBundle : InterventionBundle
initialPilotBundle = interventionBundle
  initialPilot installed partial partial constrained constrained
  constrained constrained absentOrNotInstalled absentOrNotInstalled

postAmendmentBundle : InterventionBundle
postAmendmentBundle = interventionBundle
  postPublicSpaceAmendment partial constrained partial constrained constrained
  constrained constrained absentOrNotInstalled absentOrNotInstalled

postExpiryBundle : InterventionBundle
postExpiryBundle = interventionBundle
  postExpiry absentOrNotInstalled constrained unknown constrained constrained
  constrained constrained absentOrNotInstalled absentOrNotInstalled

record OutcomeObservation : Set where
  constructor outcomeObservation
  field
    label : String
    phase : PolicyPhase
    direction : String
    source : BundleSource
    causalAttributionInstalled : Bool

open OutcomeObservation public

bcPolicySource : BundleSource
bcPolicySource = bundleSource
  "Province of British Columbia"
  "Decriminalizing people who use drugs in B.C."
  2026
  "official provincial policy page; no DOI asserted"
  "policy dates, expiry/non-renewal, stated objectives and monitoring domains"

cihr2026Source : BundleSource
cihr2026Source = bundleSource
  "Canadian Institutes of Health Research; Jürgen Rehm, nominated PI"
  "Evaluation of the British Columbia Exemption: Progress Report Lay Summary, November 2025-April 2026"
  2026
  "CIHR progress report; no DOI asserted"
  "criminal-justice trend, service-delivery/funding/training/resource implementation observations"

woodEtAl2026Source : BundleSource
woodEtAl2026Source = bundleSource
  "Becca Wood; Naomi Zakimi; Mieke Fraser; O Kara Loewen; Katie Fajber; Brooke Kinniburgh; Charlene Burmeister; Iesha Henderson; Alissa Greer"
  "Public drug use, policing, and the limits of decriminalization in British Columbia: A mixed methods study"
  2026
  "10.1016/j.drugpo.2026.105250"
  "public-space policing/displacement experiences, especially among unhoused or structurally vulnerable participants"

service2025Source : BundleSource
service2025Source = bundleSource
  "multi-author BMC Public Health study"
  "Exploring the early impacts of drug decriminalization on harm reduction and opioid agonist treatment service operations and delivery in British Columbia: insights from key informant interviews"
  2025
  "10.1186/s12889-025-25479-x"
  "service operations, staffing/resource constraints and implementation support"

access2026Source : BundleSource
access2026Source = bundleSource
  "multi-author BMC Public Health study"
  "Access to health and harm reduction services during drug decriminalization in British Columbia, Canada: a mixed-method study"
  2026
  "10.1186/s12889-026-26978-1"
  "persistent barriers to care/harm-reduction services during pilot; structural support boundary"

initialJusticeReduction : OutcomeObservation
initialJusticeReduction = outcomeObservation
  "possession seizures/cases/incarceration initially declined"
  initialPilot "decline" cihr2026Source false

postAmendmentReturn : OutcomeObservation
postAmendmentReturn = outcomeObservation
  "seizures/cases returned toward pre-policy levels following amendment"
  postPublicSpaceAmendment "return toward pre-policy levels" cihr2026Source false

serviceDeliveryMinimalChange : OutcomeObservation
serviceDeliveryMinimalChange = outcomeObservation
  "minimal policy-related change to HR/OAT service delivery"
  initialPilot "minimal change" cihr2026Source false

unhousedPublicSpaceBurden : OutcomeObservation
unhousedPublicSpaceBurden = outcomeObservation
  "heightened surveillance/displacement burden for unhoused or structurally vulnerable participants"
  postPublicSpaceAmendment "increased constraint" woodEtAl2026Source false

persistentAccessBarriers : OutcomeObservation
persistentAccessBarriers = outcomeObservation
  "barriers to health and harm-reduction access persisted during pilot"
  initialPilot "persistent barriers" access2026Source false

------------------------------------------------------------------------
-- Identification boundaries.
------------------------------------------------------------------------

data DecriminalizationLabelPromotesFullBundle : Set where

data PilotOutcomePromotesLegalReformCausality : Set where

data UnderprovisionPromotesImpossibilityOfReform : Set where

data VisiblePublicUsePromotesDecriminalizationCause : Set where

labelDoesNotPromoteFullBundle : DecriminalizationLabelPromotesFullBundle → ⊥
labelDoesNotPromoteFullBundle ()

outcomeDoesNotPromoteLegalReformCausality : PilotOutcomePromotesLegalReformCausality → ⊥
outcomeDoesNotPromoteLegalReformCausality ()

underprovisionDoesNotPromoteImpossibilityOfReform : UnderprovisionPromotesImpossibilityOfReform → ⊥
underprovisionDoesNotPromoteImpossibilityOfReform ()

visiblePublicUseDoesNotPromoteDecriminalizationCause :
  VisiblePublicUsePromotesDecriminalizationCause → ⊥
visiblePublicUseDoesNotPromoteDecriminalizationCause ()

record BCBundleBoundary : Set where
  constructor bcBundleBoundary
  field
    policyLabelAndImplementationBundleSeparated : Bool
    amendmentChangesTreatmentDefinition : Bool
    dedicatedFundingAndTrainingConstrained : Bool
    housingAndPovertyInfrastructureCommensuratelyInstalled : Bool
    initialJusticeReductionObserved : Bool
    serviceDeliveryTransformationObserved : Bool
    underprovisionedPilotEqualsFullyProvisionedReform : Bool
    pilotOutcomeAloneEstablishesDecriminalizationCausality : Bool

canonicalBCBundleBoundary : BCBundleBoundary
canonicalBCBundleBoundary =
  bcBundleBoundary true true true false true false false false
