module DASHI.Governance.SiegePressureDomesticDivergenceHypothesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- SIEGE PRESSURE / DOMESTIC DIVERGENCE
--
-- "Siege logic" is represented as a causal hypothesis family, not a verdict.
------------------------------------------------------------------------

reutersIranEconomy : Source.AttributedSource
reutersIranEconomy = Source.mkNoDOISource
  "Reuters"
  "Iranians stagger under soaring costs of seven months of war"
  "Reuters"
  "2026-09-29"
  "https://www.reuters.com/business/energy/iranians-stagger-under-soaring-costs-seven-months-war-2026-09-29/"
  Source.newsSource
  "current reporting on blockade, war-related economic strain, household hardship, repression and negotiation pressure"
  Source.publicAttribution

reutersIranStrategy : Source.AttributedSource
reutersIranStrategy = Source.mkNoDOISource
  "Reuters"
  "Iran readies harder retaliation if attacked as diplomacy faces long odds"
  "Reuters"
  "2026-10-01"
  "https://www.reuters.com/world/middle-east/iran-readies-harder-retaliation-if-attacked-diplomacy-faces-long-odds-2026-10-01/"
  Source.newsSource
  "current reporting on retaliatory doctrine, allied-group preparation, diplomacy, internal unrest concerns and strategic costs"
  Source.publicAttribution

commonsCuba2026 : Source.AttributedSource
commonsCuba2026 = Source.mkNoDOISource
  "UK House of Commons Library"
  "Frequently asked questions: Cuba's humanitarian crisis and US tensions in 2026"
  "House of Commons Library Research Briefing"
  "2026-08-17"
  "https://commonslibrary.parliament.uk/research-briefings/cbp-10991/"
  Source.governmentSource
  "balanced briefing: Cuba's crisis reflects both U.S. sanctions/oil restrictions and domestic economic-policy constraints; also records repression of dissent"
  Source.publicAttribution

reutersCubaGrid : Source.AttributedSource
reutersCubaGrid = Source.mkNoDOISource
  "Reuters"
  "Cuba's electrical grid collapses again, plunging island into darkness"
  "Reuters"
  "2026-09-18"
  "https://www.reuters.com/business/energy/cuba-energy-grid-suffers-nationwide-collapse-2026-09-18/"
  Source.newsSource
  "current reporting on grid collapse, fuel shortages and the role of U.S. oil restrictions alongside infrastructure fragility"
  Source.publicAttribution

data PressureAxis : Set where
  externalMilitaryThreat : PressureAxis
  sanctionsOrBlockade : PressureAxis
  fiscalResourceConstraint : PressureAxis
  domesticEconomicPolicy : PressureAxis
  infrastructureFragility : PressureAxis
  domesticDissent : PressureAxis
  coerciveStateResponse : PressureAxis
  externalDeterrenceStrategy : PressureAxis

record PressureObservation : Set where
  constructor pressure-observation
  field
    caseRef : String
    axis : PressureAxis
    source : Source.AttributedSource
    reading : String
    independentlyProvesNecessity : Bool
    independentlyProvesNecessityIsFalse :
      independentlyProvesNecessity ≡ false

open PressureObservation public

iranExternalPressure : PressureObservation
iranExternalPressure =
  pressure-observation
    "Iran-2026"
    sanctionsOrBlockade
    reutersIranEconomy
    "War and blockade materially constrain oil revenue, imports and household welfare."
    false refl

iranDeterrence : PressureObservation
iranDeterrence =
  pressure-observation
    "Iran-2026"
    externalDeterrenceStrategy
    reutersIranStrategy
    "Iranian officials describe broader retaliatory preparation and coordinated regional responses if attacks resume."
    false refl

cubaExternalPressure : PressureObservation
cubaExternalPressure =
  pressure-observation
    "Cuba-2026"
    sanctionsOrBlockade
    commonsCuba2026
    "U.S. restrictions on fuel supply materially worsen Cuba's energy and humanitarian crisis."
    false refl

cubaDomesticConstraint : PressureObservation
cubaDomesticConstraint =
  pressure-observation
    "Cuba-2026"
    domesticEconomicPolicy
    commonsCuba2026
    "The briefing treats Cuban economic policy and U.S. sanctions as jointly relevant causes rather than one exclusive cause."
    false refl

data MechanismHypothesisKind : Set where
  siegePressureContributes : MechanismHypothesisKind
  domesticGovernanceContributes : MechanismHypothesisKind
  securityFramingRoutesDissent : MechanismHypothesisKind
  foreignPolicyLegitimacySubstitution : MechanismHypothesisKind
  coercionMaintainsExternalStrategy : MechanismHypothesisKind

record MechanismHypothesis : Set where
  constructor mechanism-hypothesis
  field
    kind : MechanismHypothesisKind
    caseRef : String
    sourceRefs : List String
    counterHypothesisRef : String
    reviewedAsCausalMechanism : Bool
    reviewedAsCausalMechanismIsFalse :
      reviewedAsCausalMechanism ≡ false

open MechanismHypothesis public

iranSiegeHypothesis : MechanismHypothesis
iranSiegeHypothesis =
  mechanism-hypothesis
    siegePressureContributes
    "Iran-2026"
    ("Reuters 2026-09-29 economic strain" ∷ "Reuters 2026-10-01 strategic posture" ∷ [])
    "domestic governance, distributive choices, institutional interests, ideology, and wartime damage may independently or jointly explain outcomes"
    false refl

cubaSiegeHypothesis : MechanismHypothesis
cubaSiegeHypothesis =
  mechanism-hypothesis
    siegePressureContributes
    "Cuba-2026"
    ("House of Commons Library 2026-08-17" ∷ "Reuters 2026-09-18 grid collapse" ∷ [])
    "domestic economic structure, aging infrastructure, natural shocks and policy choices remain independent contributors"
    false refl

record IranCubaComparisonBoundary : Set where
  constructor iran-cuba-comparison-boundary
  field
    externalPressureComparable : Bool
    internalInstitutionsComparable : Bool
    sameHistoricalMechanism : Bool
    sameThreatMagnitude : Bool
    sameRepressionPattern : Bool
    sanctionsAloneExplainOutcome : Bool
    domesticPolicyAloneExplainsOutcome : Bool
    comparisonCreatesRegimeEvaluation : Bool

canonicalIranCubaBoundary : IranCubaComparisonBoundary
canonicalIranCubaBoundary =
  iran-cuba-comparison-boundary true true false false false false false false

data ExternalThreatNecessitatesDomesticRepression : Set where
data DomesticRepressionProvesExternalThreatFake : Set where
data SiegePressureMeansStateHasNoChoice : Set where
data IranAndCubaHaveSameMechanism : Set where

externalThreatDoesNotNecessitateRepression :
  ExternalThreatNecessitatesDomesticRepression → ⊥
externalThreatDoesNotNecessitateRepression ()

repressionDoesNotProveThreatUnreal :
  DomesticRepressionProvesExternalThreatFake → ⊥
repressionDoesNotProveThreatUnreal ()

siegePressureDoesNotEraseChoice :
  SiegePressureMeansStateHasNoChoice → ⊥
siegePressureDoesNotEraseChoice ()

comparisonDoesNotCreateIdentity :
  IranAndCubaHaveSameMechanism → ⊥
comparisonDoesNotCreateIdentity ()

iranEconomySnowball : Snowball.SourceRoleSnowballReceipt reutersIranEconomy
iranEconomySnowball = Snowball.canonicalSourceRoleSnowballReceipt reutersIranEconomy

cubaBriefingSnowball : Snowball.SourceRoleSnowballReceipt commonsCuba2026
cubaBriefingSnowball = Snowball.canonicalSourceRoleSnowballReceipt commonsCuba2026
