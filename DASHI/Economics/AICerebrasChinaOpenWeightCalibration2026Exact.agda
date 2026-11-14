module DASHI.Economics.AICerebrasChinaOpenWeightCalibration2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AIChinaTSMCGeoEconomicCalibration2026Exact as China
import DASHI.Economics.ChinaUSAITrainingServingComputeSeparation2026Exact as ChinaServing
import DASHI.Economics.AIUbiquityRentInversionExact as Ubiquity

------------------------------------------------------------------------
-- CEREBRAS / CHINA / OPEN-WEIGHT CALIBRATION
--
-- This owner keeps three distinct competitive-pressure mechanisms explicit:
--   1. alternative accelerator architectures and serving systems;
--   2. increasingly self-contained Chinese model/hardware/software stacks;
--   3. open-weight substitution and the usage/spend divergence.
--
-- The conjunction can weaken scarcity rents without proving that frontier
-- closed labs have literally zero moat or that any named firm must fail.
------------------------------------------------------------------------

cerebrasAlternativeArchitecture : Capital.BoundedObservation
cerebrasAlternativeArchitecture = Capital.boundedObservation
  "Cerebras wafer-scale inference"
  "OpenAI's 750 MW Cerebras partnership is evidence that frontier serving portfolios can include non-GPU accelerator architectures at large scale."
  Capital.cerebrasOpenAIPartnershipSource
  false false false false false

record CompetitiveSubstitutionCoordinates : Set where
  constructor competitiveSubstitutionCoordinates
  field
    alternativeAcceleratorArchitecture : Bool
    nonCUDAServingPath : Bool
    openWeightSubstitutability : Bool
    localInferenceFeasible : Bool
    chinaModelFrontierCompetitive : Bool
    chinaDomesticAcceleratorPath : Bool
    chinaDomesticSoftwarePath : Bool
    provesClosedModelNoMoat : Bool

open CompetitiveSubstitutionCoordinates public

candidateCompetitiveSubstitution2026 : CompetitiveSubstitutionCoordinates
candidateCompetitiveSubstitution2026 =
  competitiveSubstitutionCoordinates
    true true true true true true true false

------------------------------------------------------------------------
-- Open-weight usage / spend surface
------------------------------------------------------------------------

record OpenWeightPlatformObservation : Set where
  constructor openWeightPlatformObservation
  field
    platform : String
    dateOrWindow : String
    openTokenShareReading : String
    spendShareReading : String
    source : Source.AttributedSource
    globalMarketShareEstablished : Bool

open OpenWeightPlatformObservation public

kiloJuly2026 : OpenWeightPlatformObservation
kiloJuly2026 = openWeightPlatformObservation
  "Kilo"
  "week of 2026-07-20"
  "79.1 percent open-weight token usage"
  "not asserted by this source receipt"
  Capital.kiloOpenWeightShare2026
  false

vercelJune2026 : OpenWeightPlatformObservation
vercelJune2026 = openWeightPlatformObservation
  "Vercel AI Gateway"
  "June 2026"
  "29 percent open-weight token volume"
  "under 4 percent of spend"
  Capital.vercelOpenWeightShare2026
  false

record UsageRentDivergence : Set where
  constructor usageRentDivergence
  field
    openUsageShareRising : Bool
    openSpendShareLowerThanUsageShare : Bool
    proprietaryRentPerUnitUnderPressure : Bool
    totalAIUseCanStillRise : Bool

open UsageRentDivergence public

candidateUsageRentDivergence2026 : UsageRentDivergence
candidateUsageRentDivergence2026 =
  usageRentDivergence true true true true

------------------------------------------------------------------------
-- China calibration bridge
------------------------------------------------------------------------

existingChinaGeoEconomicCalibration : China.GeoEconomicObservation
existingChinaGeoEconomicCalibration = China.chinaManufacturingScale

-- Preserve the repo's training/serving separation owner as the place where
-- national compute observations are interpreted.  This module contributes
-- competitive-pressure coordinates, not a national-winner theorem.
record ChinaStackSubstitutionBoundary : Set where
  constructor chinaStackSubstitutionBoundary
  field
    modelCapabilityPressure : Bool
    acceleratorSubstitutionPressure : Bool
    servingSoftwareSubstitutionPressure : Bool
    exportControlsGuaranteePermanentScarcity : Bool
    nationalCapabilityFollowsFromOneChipMetric : Bool

open ChinaStackSubstitutionBoundary public

candidateChinaStackBoundary2026 : ChinaStackSubstitutionBoundary
candidateChinaStackBoundary2026 =
  chinaStackSubstitutionBoundary true true true false false

data ChinaScaleImpliesFrontierDominancePermission : Set where
data ExportControlsImplyPermanentWesternMoatPermission : Set where
data OpenUsageImpliesClosedFrontierIrrelevancePermission : Set where

chinaScaleDoesNotAutoProveFrontierDominance :
  ChinaScaleImpliesFrontierDominancePermission → ⊥
chinaScaleDoesNotAutoProveFrontierDominance ()

exportControlsDoNotAutoProvePermanentWesternMoat :
  ExportControlsImplyPermanentWesternMoatPermission → ⊥
exportControlsDoNotAutoProvePermanentWesternMoat ()

openUsageDoesNotAutoProveClosedFrontierIrrelevance :
  OpenUsageImpliesClosedFrontierIrrelevancePermission → ⊥
openUsageDoesNotAutoProveClosedFrontierIrrelevance ()

------------------------------------------------------------------------
-- Existing ubiquity boundary retained verbatim at the integration surface.
------------------------------------------------------------------------

technologySuccessCanCoincideWithCapitalRecoveryPressure :
  Ubiquity.TechnologySuccessCapitalLossBoundary
technologySuccessCanCoincideWithCapitalRecoveryPressure =
  Ubiquity.canonicalTechnologySuccessCapitalLossBoundary
