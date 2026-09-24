module DASHI.Wikimedia.IbrahimPesticideStandardsAustraliaUSEUComparisonParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimAustraliaPesticideExposurePriorParetoExact as Australia
import DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExposureParetoExact as Tobacco
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- AUSTRALIA / UNITED STATES / EUROPEAN UNION PESTICIDE-STANDARDS COMPARISON
--
-- Country/jurisdiction labels do not create a scalar safety ordering.  The
-- comparison is coordinate-indexed: exposure-model freshness, MRL scope,
-- market surveillance, emergency/minor-use controls, lifecycle transitions,
-- tobacco residue governance and inhalation-specific treatment.
------------------------------------------------------------------------

data Jurisdiction : Set where
  australia : Jurisdiction
  unitedStates : Jurisdiction
  europeanUnion : Jurisdiction

data ComparisonAxis : Set where
  dietaryExposureModelFreshness : ComparisonAxis
  foodMRLHarmonisation : ComparisonAxis
  retailFoodResidueSurveillance : ComparisonAxis
  emergencyOrMinorUseDerogation : ComparisonAxis
  nonFoodToFoodLifecycleControl : ComparisonAxis
  tobaccoPesticideResidueGovernance : ComparisonAxis
  inhalationSpecificResidueGovernance : ComparisonAxis
  updateAndReviewCadence : ComparisonAxis

record JurisdictionCoordinate : Set where
  constructor jurisdiction-coordinate
  field
    jurisdiction : Jurisdiction
    axis : ComparisonAxis
    sourceReference : String
    boundedFinding : String
    strongCoordinatePaid : Bool
    scalarWinnerPaid : Bool
open JurisdictionCoordinate public

------------------------------------------------------------------------
-- EU food-residue architecture.
------------------------------------------------------------------------

euMRLHarmonisation : JurisdictionCoordinate
euMRLHarmonisation = jurisdiction-coordinate
  europeanUnion foodMRLHarmonisation
  "European Commission Regulation (EC) No 396/2005; EU MRL legislation and Commission MRL Q&A"
  "EU pesticide MRLs are harmonised for food/feed across the Union; a general default MRL of 0.01 mg/kg applies where no specific MRL exists, subject to listed exceptions and analytical feasibility. The same market MRLs apply to EU and imported food/feed."
  true false

euSurveillance : JurisdictionCoordinate
euSurveillance = jurisdiction-coordinate
  europeanUnion retailFoodResidueSurveillance
  "EFSA annual EU pesticide residue reports and EU-coordinated multiannual control programme"
  "EU Member States plus Norway and Iceland report annual residue-control data. EFSA states that more than 100,000 food samples and more than 600 pesticides are covered annually across coordinated and national programmes. The 2024 dataset contained more than 125,000 samples; the coordinated programme rotates representative commodities on a three-year cycle."
  true false

euExposureModel : JurisdictionCoordinate
euExposureModel = jurisdiction-coordinate
  europeanUnion dietaryExposureModelFreshness
  "EFSA Comprehensive European Food Consumption Database; PRIMo revision 4 programme"
  "EFSA's consumption database was materially updated in December 2024 and is country/age/high-consumer indexed. PRIMo 4 uses individual consumption data transformed to raw-primary-commodity equivalents; EFSA is transitioning toward newer harmonised exposure tooling rather than relying only on a single old national survey vintage."
  true false

euEmergencyUse : JurisdictionCoordinate
euEmergencyUse = jurisdiction-coordinate
  europeanUnion emergencyOrMinorUseDerogation
  "Regulation (EC) No 1107/2009 Article 53; Commission emergency-authorisation guidance"
  "Member States may grant emergency plant-protection-product authorisations for at most 120 days and limited/controlled use where a danger cannot be contained otherwise. The notification architecture explicitly asks whether the use complies with Regulation 396/2005 MRLs; where it does not, a proposed temporary MRL and consumer-risk assessment are required."
  true false

euLifecycle : JurisdictionCoordinate
euLifecycle = jurisdiction-coordinate
  europeanUnion nonFoodToFoodLifecycleControl
  "Regulation (EC) No 396/2005 Articles 2 and 18"
  "The food/feed MRL regulation excludes products demonstrably intended for non-food/non-feed manufacture, but once covered products are placed on the market as food/feed they must comply with MRLs. For certain post-harvest fumigant derogations, controls must prevent consumer availability until residues fall within the applicable MRL."
  true false

euTobacco : JurisdictionCoordinate
euTobacco = jurisdiction-coordinate
  europeanUnion tobaccoPesticideResidueGovernance
  "Directive 2014/40/EU Articles 3-5 and European Commission tobacco product-regulation guidance"
  "EU tobacco-product law requires reporting of ingredients and specified emissions and allows additional emission methods/studies, but the food/feed MRL architecture in Regulation 396/2005 is not a retail tobacco pesticide-residue CoA system. No Union-wide batch-by-batch multiresidue tobacco-pesticide certification comparable to medicinal-cannabis testing was located in the acquired primary surfaces."
  true false

euInhalation : JurisdictionCoordinate
euInhalation = jurisdiction-coordinate
  europeanUnion inhalationSpecificResidueGovernance
  "Directive 2014/40/EU plus current acquired EU pesticide/MRL surfaces"
  "The EU has inhalation/emissions regulation for tobacco products, but the acquired food-pesticide MRL framework is dietary and does not itself provide a general cannabis-style smoke/vape pesticide-pyrolysis assessment architecture. Exact cross-product inhalation-pesticide coverage remains incomplete."
  false false

euReviewCadence : JurisdictionCoordinate
euReviewCadence = jurisdiction-coordinate
  europeanUnion updateAndReviewCadence
  "EFSA Article 12 MRL review progress; annual residue reports; EFSA food-consumption database updates"
  "EFSA publishes annual residue reports, updates Article 12 MRL review progress quarterly, and has an actively maintained consumption-data programme. This supports a comparatively explicit review cadence, though it does not prove every MRL or dietary survey is current for every subpopulation."
  true false

------------------------------------------------------------------------
-- Australia coordinates from the existing owner.
------------------------------------------------------------------------

australiaExposure : JurisdictionCoordinate
australiaExposure = jurisdiction-coordinate
  australia dietaryExposureModelFreshness
  "APVMA 2025 dimethoate berry reconsideration plus FSANZ dietary-exposure architecture"
  "A real counterexample to timeless approval exists: berry-consumption assumptions used in the earlier dimethoate assessment became inadequate as Australians consumed substantially more berries, reopening acute dietary risk for young children. This pays vulnerability to stale exposure priors, not a claim that every Australian model is stale."
  true false

australiaEmergencyLifecycle : JurisdictionCoordinate
australiaEmergencyLifecycle = jurisdiction-coordinate
  australia nonFoodToFoodLifecycleControl
  "APVMA fire-ant bifenthrin permits PER14317 and PER9796 plus Queensland fire-ant nursery guidance"
  "Quarantine/minor-use permits allow bifenthrin dipping/drenching or long-lived granular treatment of nursery stock under non-food/non-bearing constraints. The lifecycle transition from treated non-bearing stock to later food-bearing state is therefore a meaningful control point, not automatically paid by the initial permit."
  true false

australiaTobacco : JurisdictionCoordinate
australiaTobacco = jurisdiction-coordinate
  australia tobaccoPesticideResidueGovernance
  "Australian federal tobacco product regulations and ingredient-reporting framework"
  "Current acquired federal tobacco rules require ingredient/product reporting and ignition-propensity compliance, but no cannabis-like routine batch multiresidue pesticide CoA requirement for retail tobacco was located."
  true false

------------------------------------------------------------------------
-- United States coordinates from existing comparison work plus current EPA/FDA
-- primary surfaces.
------------------------------------------------------------------------

usExposure : JurisdictionCoordinate
usExposure = jurisdiction-coordinate
  unitedStates dietaryExposureModelFreshness
  "US EPA DEEM-FCID/Calendex current software page"
  "EPA's currently published DEEM-FCID model page states that its food-consumption data derive from 2005-2010 NHANES/WWEIA. This is a concrete stale-data coordinate, not evidence that all US pesticide risk assessment is obsolete."
  true false

usFoodFramework : JurisdictionCoordinate
usFoodFramework = jurisdiction-coordinate
  unitedStates foodMRLHarmonisation
  "US EPA pesticide tolerance framework under the Federal Food, Drug, and Cosmetic Act"
  "EPA food tolerances require a reasonable certainty of no harm and consider aggregate exposure and sensitive populations. Unlike the EU's single Union-wide MRL architecture, the US system is federal but uses its own commodity/tolerance structure rather than EU Regulation 396/2005."
  true false

usTobacco : JurisdictionCoordinate
usTobacco = jurisdiction-coordinate
  unitedStates tobaccoPesticideResidueGovernance
  "FDA Federal Food, Drug, and Cosmetic Act section 907 tobacco-product standard surface"
  "Federal tobacco law prohibits tobacco exceeding any applicable federal pesticide tolerance for domestically grown tobacco, but FDA has documented that no such federal tobacco pesticide tolerances were established on the acquired surface. No routine cannabis-style retail tobacco multiresidue CoA requirement is therefore paid."
  true false

------------------------------------------------------------------------
-- Structural comparisons.
------------------------------------------------------------------------

data ScalarCountryRankingFromCoordinates : Set where
data AnnualMonitoringCreatesUniversalSafety : Set where
data DefaultMRLCreatesZeroRisk : Set where
data EmergencyAuthorisationCreatesFoodSafety : Set where
data IngredientReportingCreatesResidueTesting : Set where

data SameRegulatoryWordCreatesSameArchitecture : Set where

scalarCountryRankingDoesNotFollow : ScalarCountryRankingFromCoordinates → ⊥
scalarCountryRankingDoesNotFollow ()

annualMonitoringDoesNotCreateUniversalSafety : AnnualMonitoringCreatesUniversalSafety → ⊥
annualMonitoringDoesNotCreateUniversalSafety ()

defaultMRLDoesNotCreateZeroRisk : DefaultMRLCreatesZeroRisk → ⊥
defaultMRLDoesNotCreateZeroRisk ()

emergencyAuthorisationDoesNotCreateFoodSafety : EmergencyAuthorisationCreatesFoodSafety → ⊥
emergencyAuthorisationDoesNotCreateFoodSafety ()

ingredientReportingDoesNotCreateResidueTesting : IngredientReportingCreatesResidueTesting → ⊥
ingredientReportingDoesNotCreateResidueTesting ()

sameRegulatoryWordDoesNotCreateSameArchitecture : SameRegulatoryWordCreatesSameArchitecture → ⊥
sameRegulatoryWordDoesNotCreateSameArchitecture ()

record ComparativeFinding : Set where
  constructor comparative-finding
  field
    axis : ComparisonAxis
    finding : String
    australiaStanding : String
    usStanding : String
    euStanding : String
    scalarWinnerPaid : Bool
open ComparativeFinding public

foodMonitoringFinding : ComparativeFinding
foodMonitoringFinding = comparative-finding
  retailFoodResidueSurveillance
  "EU currently has the clearest harmonised supranational annual residue-surveillance architecture among the three compared systems on the acquired sources. This is a surveillance-strength claim, not a universal safety ranking."
  "national surveillance exists but is not yet normalised here to the same coverage/sample-count denominator"
  "USDA/EPA surveillance exists but exact like-for-like denominator remains to be normalised"
  "annual EFSA reporting; >100k samples/year and >600 pesticide analytes across coordinated/national programmes"
  false

modelFreshnessFinding : ComparativeFinding
modelFreshnessFinding = comparative-finding
  dietaryExposureModelFreshness
  "No simple winner is paid. Australia provides a recent real-world model-drift failure; the US publishes a current tool using 2005-2010 consumption data; the EU has a newer, actively updated consumption database and PRIMo 4 transition."
  "2025 berry case proves stale-prior vulnerability"
  "DEEM-FCID uses 2005-2010 NHANES/WWEIA on current EPA page"
  "Comprehensive consumption DB updated Dec 2024; PRIMo 4 uses individual/RPC data"
  false

emergencyUseFinding : ComparativeFinding
emergencyUseFinding = comparative-finding
  emergencyOrMinorUseDerogation
  "All three systems permit exceptional/minor-use pathways, but EU Article 53 explicitly couples emergency-use notification to MRL compliance or a temporary-MRL/consumer-risk-assessment path. Australia's fire-ant permits show a strong non-food/quarantine use case whose downstream lifecycle must be tracked separately."
  "APVMA permits can authorise long-lived quarantine treatments under non-food/non-bearing constraints"
  "US emergency/minor-use architecture not normalised in this owner"
  "Article 53 max 120 days; MRL compliance explicitly queried; tMRL/risk assessment if not compliant"
  false

tobaccoFinding : ComparativeFinding
tobaccoFinding = comparative-finding
  tobaccoPesticideResidueGovernance
  "Tobacco remains a common weak coordinate: none of the acquired AU/US/EU primary frameworks pays a cannabis-style routine batch multiresidue pesticide CoA for retail combustible tobacco."
  "ingredient/product reporting, no located batch pesticide CoA"
  "conditional tolerance language but no paid federal tobacco tolerance or batch CoA"
  "ingredient/emission reporting under TPD, no located batch pesticide CoA"
  false

------------------------------------------------------------------------
-- Pareto roadmap.
------------------------------------------------------------------------

data ComparisonParetoTarget : Set where
  normalizeFoodSurveillance : ComparisonParetoTarget
  normalizeExposureModelVintage : ComparisonParetoTarget
  normalizeEmergencyUseControls : ComparisonParetoTarget
  traceLifecycleTransitions : ComparisonParetoTarget
  compareTobaccoBlindSpot : ComparisonParetoTarget
  compareInhalationSpecificStandards : ComparisonParetoTarget
  scalarCountryRanking : ComparisonParetoTarget

record ComparisonParetoStep : Set where
  constructor comparison-pareto-step
  field
    priority : Nat
    target : ComparisonParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open ComparisonParetoStep public

pareto0 : ComparisonParetoStep
pareto0 = comparison-pareto-step
  0 normalizeFoodSurveillance
  "normalise EFSA EU-MACP/national-control, USDA PDP/FDA/EPA and Australian residue-surveillance programmes by yearly sample count, analyte breadth, random-vs-risk sampling and market coverage"
  "actual surveillance strength rather than anecdotal strictness"
  "none"

pareto1 : ComparisonParetoStep
pareto1 = comparison-pareto-step
  1 normalizeExposureModelVintage
  "record the exact survey vintages and population coverage feeding EFSA PRIMo 4, EPA DEEM-FCID and FSANZ/APVMA dietary models"
  "model-freshness comparison"
  "none"

pareto2 : ComparisonParetoStep
pareto2 = comparison-pareto-step
  2 normalizeEmergencyUseControls
  "compare APVMA minor/emergency permits, EU Article 53 and US FIFRA emergency exemptions on duration, residue/MRL handling and consumer-risk reassessment"
  "exception-path governance"
  "food-surveillance and model semantics should remain separate"

pareto3 : ComparisonParetoStep
pareto3 = comparison-pareto-step
  3 traceLifecycleTransitions
  "trace treated ornamental/non-bearing stock into later edible-bearing states in each jurisdiction and identify the explicit legal/residue gate at that transition"
  "non-food to food same-object transition control"
  "exact product/use cases required"

pareto4 : ComparisonParetoStep
pareto4 = comparison-pareto-step
  4 compareTobaccoBlindSpot
  "compare whether any of AU, US or EU performs routine retail tobacco pesticide surveillance with public analyte-level results"
  "mixed cannabis+tobacco source-residue coverage"
  "ingredient reporting is not a substitute"

pareto5 : ComparisonParetoStep
pareto5 = comparison-pareto-step
  5 compareInhalationSpecificStandards
  "compare cannabis/tobacco smoke-vape pesticide transformation requirements and identify where pyrolysis data are mandatory, optional or absent"
  "route-specific standards comparison"
  "source-residue architecture first"

pareto99 : ComparisonParetoStep
pareto99 = comparison-pareto-step
  99 scalarCountryRanking
  "do not collapse heterogeneous coordinates into 'Australia worse', 'EU safest' or 'US strongest' without an explicit weighted consumer and justified weights"
  "prevents unsupported scalar ranking"
  "dominated by coordinate-normalised comparison"

------------------------------------------------------------------------
-- Temporal evidence.
------------------------------------------------------------------------

data ComparisonTime : Set where
  legacyModelEra : ComparisonTime
  current2026Comparison : ComparisonTime

data ComparisonInterpretation : Set where
  euFoodSurveillanceStructurallyStrong : ComparisonInterpretation
  australiaModelDriftCaseReal : ComparisonInterpretation
  usExposureModelOldConsumptionData : ComparisonInterpretation
  tobaccoBlindSpotShared : ComparisonInterpretation
  euUniversallySafest : ComparisonInterpretation
  australiaUniversallyWorst : ComparisonInterpretation

data ComparisonSummary : Set where coordinateIndexedNotScalar : ComparisonSummary

ComparisonCompatible : ComparisonTime → ComparisonInterpretation → Set
ComparisonCompatible legacyModelEra euFoodSurveillanceStructurallyStrong = ⊥
ComparisonCompatible legacyModelEra australiaModelDriftCaseReal = ⊥
ComparisonCompatible legacyModelEra usExposureModelOldConsumptionData = ⊥
ComparisonCompatible legacyModelEra tobaccoBlindSpotShared = ⊥
ComparisonCompatible legacyModelEra euUniversallySafest = ⊥
ComparisonCompatible legacyModelEra australiaUniversallyWorst = ⊥
ComparisonCompatible current2026Comparison euFoodSurveillanceStructurallyStrong = ⊤
ComparisonCompatible current2026Comparison australiaModelDriftCaseReal = ⊤
ComparisonCompatible current2026Comparison usExposureModelOldConsumptionData = ⊤
ComparisonCompatible current2026Comparison tobaccoBlindSpotShared = ⊤
ComparisonCompatible current2026Comparison euUniversallySafest = ⊥
ComparisonCompatible current2026Comparison australiaUniversallyWorst = ⊥

comparisonTemporalSystem : Temporal.TemporalEvidenceSystem
comparisonTemporalSystem = record
  { Time = ComparisonTime
  ; Interpretation = ComparisonInterpretation
  ; Compatible = ComparisonCompatible
  ; Summary = ComparisonSummary
  ; summarize = λ _ → coordinateIndexedNotScalar
  ; timeReference = λ
      { legacyModelEra → "pre-normalised AU/US/EU pesticide-regulation comparison"
      ; current2026Comparison → "current DASHI coordinate-indexed AU/US/EU standards comparison"
      }
  }

currentComparisonFibre : Temporal.EvidenceFibre comparisonTemporalSystem current2026Comparison
currentComparisonFibre = Temporal.liveInterpretationAt euFoodSurveillanceStructurallyStrong tt

record ComparisonBoundary : Set where
  constructor comparison-boundary
  field
    euFoodMRLHarmonised : Bool
    euAnnualSurveillanceStrong : Bool
    euEmergencyUseStillNeedsMRLHandling : Bool
    euConsumptionDataRecentlyUpdated : Bool
    tobaccoBatchPesticideCoAPaidInAnyOfThree : Bool
    australiaUniversallyWorsePaid : Bool
    euUniversallySaferPaid : Bool
    scalarRankingBlocked : Bool
open ComparisonBoundary public

canonicalComparisonBoundary : ComparisonBoundary
canonicalComparisonBoundary = comparison-boundary
  true true true true false false false true
