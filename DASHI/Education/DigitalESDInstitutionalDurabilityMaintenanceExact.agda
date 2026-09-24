module DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence

------------------------------------------------------------------------
-- INSTITUTIONAL DURABILITY / MAINTENANCE
--
-- Launch/adoption is not persistence. A sustainable educational system needs
-- recurrent labour, funding, maintenance, governance, handover, accessibility
-- continuity and resilience to staffing/funding/political change.
------------------------------------------------------------------------

mclureAldridgeReformReview : Attr.AttributedSource
mclureAldridgeReformReview = Attr.mkDOISource
  "Felicity I. McLure; Jill M. Aldridge"
  "Sustaining reform implementation: a systematic literature review"
  "School Leadership & Management 43(1):70-98"
  "2023"
  "10.1080/13632434.2023.2171012"
  "https://doi.org/10.1080/13632434.2023.2171012"
  Attr.academicArticleSource
  "Systematic review of 249 empirical studies published 2000-2020. Supports source-bounded sustainability factors including shared leadership, budgeting/resourcing, continuing professional learning, data/evaluation, ongoing stakeholder engagement and staffing stability. It does not prove durability of any named digital-ESD intervention."
  Attr.publicAttribution

oecdShapingDigitalEducation : Attr.AttributedSource
oecdShapingDigitalEducation = Attr.mkDOISource
  "OECD"
  "Shaping Digital Education: Enabling Factors for Quality, Equity and Efficiency"
  "OECD Publishing"
  "2023"
  "10.1787/bac4dc9f-en"
  "https://doi.org/10.1787/bac4dc9f-en"
  Attr.institutionalSource
  "Institutional comparative-policy source. Supports the distinction between capital and recurrent digital-education expenditure and identifies maintenance, technical support, professional development, procurement and funding design as ongoing conditions. It is not a same-object intervention-effect study."
  Attr.publicAttribution

canonicalInstitutionalDurabilitySourceAtlas : Attr.AttributedSourceAtlas
canonicalInstitutionalDurabilitySourceAtlas = Attr.mkSourceAtlas
  "digital ESD institutional durability / maintenance source atlas"
  "DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceExact"
  (mclureAldridgeReformReview ∷ oecdShapingDigitalEducation ∷ [])
  "Review and institutional-policy source roles remain distinct; neither backfills same-object programme durability measurement."

data DurabilityCoordinate : Set where
  namedStewardMaintainer : DurabilityCoordinate
  paidLabourTimeAllocation : DurabilityCoordinate
  recurrentOperatingBudget : DurabilityCoordinate
  hardwareSoftwareMaintenance : DurabilityCoordinate
  securityUpdateResponsibility : DurabilityCoordinate
  documentationHandover : DurabilityCoordinate
  staffSuccessionTurnoverResilience : DurabilityCoordinate
  trainingProfessionalLearning : DurabilityCoordinate
  institutionalOwnershipGovernance : DurabilityCoordinate
  vendorCommunityDependency : DurabilityCoordinate
  monitoringEvaluationFeedback : DurabilityCoordinate
  dataExportMigration : DurabilityCoordinate
  politicalFundingShockResilience : DurabilityCoordinate
  defundingDecommissioningPlan : DurabilityCoordinate
  accessibilityProvisionContinuity : DurabilityCoordinate

institutionalDurabilityCoordinates : List DurabilityCoordinate
institutionalDurabilityCoordinates =
  namedStewardMaintainer
  ∷ paidLabourTimeAllocation
  ∷ recurrentOperatingBudget
  ∷ hardwareSoftwareMaintenance
  ∷ securityUpdateResponsibility
  ∷ documentationHandover
  ∷ staffSuccessionTurnoverResilience
  ∷ trainingProfessionalLearning
  ∷ institutionalOwnershipGovernance
  ∷ vendorCommunityDependency
  ∷ monitoringEvaluationFeedback
  ∷ dataExportMigration
  ∷ politicalFundingShockResilience
  ∷ defundingDecommissioningPlan
  ∷ accessibilityProvisionContinuity
  ∷ []

------------------------------------------------------------------------
-- Same successful launch, different durable institutional capacity.
------------------------------------------------------------------------

data DurabilityWorld : Set where
  launchedWithDurability : DurabilityWorld
  launchedWithoutSuccessionFunding : DurabilityWorld

data LaunchSurface : Set where successfulLaunch : LaunchSurface

launchProjection : DurabilityWorld → LaunchSurface
launchProjection launchedWithDurability = successfulLaunch
launchProjection launchedWithoutSuccessionFunding = successfulLaunch

institutionallyDurable : DurabilityWorld → Bool
institutionallyDurable launchedWithDurability = true
institutionallyDurable launchedWithoutSuccessionFunding = false

durabilityDiffers :
  institutionallyDurable launchedWithDurability ≡
  institutionallyDurable launchedWithoutSuccessionFunding → ⊥
durabilityDiffers ()

launchDurabilityWitness :
  Intersection.NonFactorabilityWitness launchProjection institutionallyDurable
launchDurabilityWitness = Intersection.nonFactorabilityWitness
  launchedWithDurability
  launchedWithoutSuccessionFunding
  refl
  durabilityDiffers

initialLaunchCannotDetermineInstitutionalDurability :
  Intersection.FactorsThrough launchProjection institutionallyDurable → ⊥
initialLaunchCannotDetermineInstitutionalDurability =
  Intersection.witnessRulesOutEveryFlatFactorisation launchDurabilityWitness

------------------------------------------------------------------------
-- Maintenance-specific no-promotion firewalls.
------------------------------------------------------------------------

data InitialGrantCreatesRecurrentlyFundedService : Set where
data TechnicalMaintainabilityCreatesFundedMaintenanceCapacity : Set where
data NamedMaintainerCreatesSuccessionResilience : Set where

initialGrantDoesNotCreateRecurrentlyFundedService :
  InitialGrantCreatesRecurrentlyFundedService → ⊥
initialGrantDoesNotCreateRecurrentlyFundedService ()

technicalMaintainabilityDoesNotCreateFundedMaintenanceCapacity :
  TechnicalMaintainabilityCreatesFundedMaintenanceCapacity → ⊥
technicalMaintainabilityDoesNotCreateFundedMaintenanceCapacity ()

namedMaintainerDoesNotCreateSuccessionResilience :
  NamedMaintainerCreatesSuccessionResilience → ⊥
namedMaintainerDoesNotCreateSuccessionResilience ()

record DurabilityIntersectionalChallenge : Set where
  constructor durability-intersectional-challenge
  field
    disabilityBoundary : Disability.DisabilityDigitalESDBoundary
    absenceAuditQuestionCount : Nat
    challengeReading : String

open DurabilityIntersectionalChallenge public

canonicalDurabilityIntersectionalChallenge : DurabilityIntersectionalChallenge
canonicalDurabilityIntersectionalChallenge = durability-intersectional-challenge
  Disability.canonicalDisabilityDigitalESDBoundary
  Absence.absenceAuditQuestionCount
  "Durability must be tested for differently situated learners and affected non-participants: maintenance, funding or staff turnover can selectively remove accessibility support, assistive-technology continuity, language/support capacity, household relief or practical exit even while the headline service remains online."

record InstitutionalDurabilityBoundary : Set where
  constructor institutional-durability-boundary
  field
    launchEqualsDurability : Bool
    launchEqualsDurabilityIsFalse : launchEqualsDurability ≡ false
    initialGrantEqualsRecurrentService : Bool
    initialGrantEqualsRecurrentServiceIsFalse : initialGrantEqualsRecurrentService ≡ false
    technicalMaintainabilityEqualsFundedMaintenance : Bool
    technicalMaintainabilityEqualsFundedMaintenanceIsFalse : technicalMaintainabilityEqualsFundedMaintenance ≡ false
    namedMaintainerEqualsSuccessionResilience : Bool
    namedMaintainerEqualsSuccessionResilienceIsFalse : namedMaintainerEqualsSuccessionResilience ≡ false
    intersectionalContinuityAuditRequired : Bool
    intersectionalContinuityAuditRequiredIsTrue : intersectionalContinuityAuditRequired ≡ true
    reviewOrPolicySourceEqualsSameObjectDurabilityMeasurement : Bool
    reviewOrPolicySourceEqualsSameObjectDurabilityMeasurementIsFalse : reviewOrPolicySourceEqualsSameObjectDurabilityMeasurement ≡ false

open InstitutionalDurabilityBoundary public

canonicalInstitutionalDurabilityBoundary : InstitutionalDurabilityBoundary
canonicalInstitutionalDurabilityBoundary = institutional-durability-boundary
  false refl
  false refl
  false refl
  false refl
  true refl
  false refl
