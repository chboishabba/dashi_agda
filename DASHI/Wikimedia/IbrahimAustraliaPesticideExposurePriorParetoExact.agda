module DASHI.Wikimedia.IbrahimAustraliaPesticideExposurePriorParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimAustraliaPesticideExposurePriorRegression as Regression
import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Measurement
import DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExposureParetoExact as Tobacco
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- AUSTRALIAN PESTICIDE EXPOSURE-PRIOR / QUARANTINE-PERMIT OWNER
--
-- Two primary Australian cases are retained separately:
--
-- 1. Dimethoate on blueberries/raspberries/blackberries: approved label use
--    ceased to retain an adequate acute dietary safety margin after contemporary
--    berry-consumption data showed Australians eat substantially more berries
--    than the exposure model used in the previous reconsideration.
--
-- 2. Fire-ant biosecurity permits allow persistent bifenthrin treatment of
--    nursery/potted plants, including pot drenches/dips and long-lived granular
--    treatment in potting media. These are non-food/quarantine-use objects and
--    must not be silently interpreted as edible-crop residue admissions.
--
-- The synthesis target is model governance:
--   hazard × residue × consumption/use distribution × route × time.
------------------------------------------------------------------------

data RegulatoryObjectKind : Set where
  foodResidueUse : RegulatoryObjectKind
  quarantineNonFoodUse : RegulatoryObjectKind
  biosecurityMovementControl : RegulatoryObjectKind
  dietaryExposureModel : RegulatoryObjectKind
  pesticideToleranceSystem : RegulatoryObjectKind

record RegulatoryEvidence : Set where
  constructor regulatory-evidence
  field
    jurisdiction : String
    objectKind : RegulatoryObjectKind
    authority : String
    sourceTitle : String
    sourceDate : String
    directLink : String
    boundedReading : String
    promotedClaim : String
    excludedPromotion : String
    primarySourcePaid : Bool
open RegulatoryEvidence public

berryDimethoate2025 : RegulatoryEvidence
berryDimethoate2025 = regulatory-evidence
  "Australia"
  foodResidueUse
  "Australian Pesticides and Veterinary Medicines Authority (APVMA)"
  "Suspension of specific dimethoate products"
  "11 November 2025"
  "https://www.apvma.gov.au/news-and-publications/news/suspension-of-specific-dimethoate-products-251111"
  "APVMA states contemporary FSANZ consumption data showed substantially increased blueberry, blackberry and raspberry consumption since the 2017 reconsideration; use under the existing labels no longer retained an adequate safety margin."
  "Existing approved directions for dimethoate on these berries were suspended; a 14-day harvest withholding pathway was supplied during suspension."
  "Does not prove prior regulatory negligence, actual poisoning, or that all Australian MRLs are unsafe."
  true

berryDimethoateStatementReasons2025 : RegulatoryEvidence
berryDimethoateStatementReasons2025 = regulatory-evidence
  "Australia"
  dietaryExposureModel
  "APVMA"
  "Gazette No 23 - Statement of Reasons"
  "11 November 2025"
  "https://www.apvma.gov.au/sites/default/files/2025-11/Gazette%20No%2023%2C%20Tuesday%2011%20November%202025.pdf"
  "The statement records updated exposure modelling and says normal berry consumption could exceed the acute reference dose for children aged 2-6 under the then-current use instructions."
  "A changed consumption distribution can reopen a previously accepted residue/use pattern even where pesticide toxicology itself is unchanged."
  "Does not mean every child exposure exceeded the ARfD, nor that observed residues caused clinical harm."
  true

fireAntPottedPlant2026 : RegulatoryEvidence
fireAntPottedPlant2026 = regulatory-evidence
  "Queensland / Australia"
  biosecurityMovementControl
  "National Fire Ant Eradication Program / APVMA permits"
  "Potted plant fire ant management"
  "current 2026 surface"
  "https://www.fireants.org.au/treat/business/materials/potted-plant-management"
  "Potted plants from fire-ant biosecurity zones can be chemically managed using approved treatments; the program describes granular bifenthrin, drenches/dips and spray treatments with defined protection periods."
  "Biosecurity movement controls can require or allow persistent pesticide treatment on nursery stock."
  "Does not establish food-use permission or consumer dietary safety for treated nursery material."
  true

bifenthrinDipPermit : RegulatoryEvidence
bifenthrinDipPermit = regulatory-evidence
  "Australia"
  quarantineNonFoodUse
  "APVMA"
  "PER14317 - bifenthrin treatment of potted/containerised root-balled plants"
  "permit current to February 2029"
  "https://permits.apvma.gov.au/PER14317.PDF"
  "Permit allows pot/container/root-ball drench or immersion treatment at a minimum 28-day retreatment interval; fruit trees bearing fruit must have fruit removed before treatment and used dip solution has controlled disposal requirements."
  "The permitted object is a quarantine/biosecurity plant-treatment pathway with explicit use restrictions."
  "Does not create an edible-fruit residue tolerance or imply harmlessness of treated potting media if later repurposed."
  true

bifenthrinGranularPermit : RegulatoryEvidence
bifenthrinGranularPermit = regulatory-evidence
  "Australia"
  quarantineNonFoodUse
  "APVMA"
  "PER9796 / related fire-ant nursery-stock bifenthrin use"
  "current permit lineage"
  "https://permits.apvma.gov.au/PER9796.PDF"
  "Permit covers quarantine treatment for ornamental species and non-bearing fruit trees using granular bifenthrin in potting media; it expressly excludes nursery stock bearing fruit and vegetable seedlings/other edible crops."
  "Persistent potting-media treatment is explicitly separated from ordinary edible-crop residue use."
  "Does not support treating food-bearing nursery stock as if it were an ornamental/non-food carrier."
  true

------------------------------------------------------------------------
-- Exposure models are not timeless facts.
------------------------------------------------------------------------

record ExposurePrior : Set where
  constructor exposure-prior
  field
    foodOrCarrier : String
    population : String
    route : String
    consumptionOrUseDistribution : String
    residueOrTreatmentReference : String
    healthOrOperationalThreshold : String
    observationDateReference : String
    currentForDecision : Bool
open ExposurePrior public

berryPrior2017 : ExposurePrior
berryPrior2017 = exposure-prior
  "blueberries/blackberries/raspberries"
  "Australian consumers"
  "oral dietary"
  "consumption assumptions used in the most recent dimethoate reconsideration completed in 2017"
  "approved label use and residues trials"
  "acute reference dose / dietary safety margin"
  "2017 regulatory state"
  false

berryPrior2025 : ExposurePrior
berryPrior2025 = exposure-prior
  "blueberries/blackberries/raspberries"
  "Australian consumers, including children aged 2-6"
  "oral dietary"
  "contemporary FSANZ consumption information indicating substantially increased berry intake"
  "existing dimethoate label use plus residue-trial information"
  "acute reference dose / adequate safety margin"
  "2025 APVMA reassessment"
  true

record PriorRevision : Set where
  constructor prior-revision
  field
    oldPrior : ExposurePrior
    newPrior : ExposurePrior
    hazardIdentityChanged : Bool
    consumptionDistributionChanged : Bool
    regulatoryDecisionChanged : Bool
    oldApprovalCreatesPermanentSafety : Bool
open PriorRevision public

berryConsumptionRevision : PriorRevision
berryConsumptionRevision = prior-revision
  berryPrior2017 berryPrior2025 false true true false

------------------------------------------------------------------------
-- Fire-ant permit semantics.
------------------------------------------------------------------------

data PlantUseClass : Set where
  ornamental : PlantUseClass
  nonBearingFruitTree : PlantUseClass
  bearingFruitTree : PlantUseClass
  vegetableSeedling : PlantUseClass
  edibleCrop : PlantUseClass
  unresolvedPlantUse : PlantUseClass

record NurseryTreatmentAdmission : Set where
  constructor nursery-treatment-admission
  field
    treatment : String
    activeIngredient : String
    plantClass : PlantUseClass
    persistenceReference : String
    foodResidueAdmission : Bool
    bearingFruitAllowedWithoutRemoval : Bool
    quarantineUsePaid : Bool
open NurseryTreatmentAdmission public

fireAntBifenthrinDip : NurseryTreatmentAdmission
fireAntBifenthrinDip = nursery-treatment-admission
  "pot/container/root-ball drench or complete immersion under PER14317"
  "bifenthrin"
  unresolvedPlantUse
  "28-day protection / minimum retreatment interval; fruit must be removed from bearing fruit trees before treatment"
  false false true

fireAntGranularOrnamental : NurseryTreatmentAdmission
fireAntGranularOrnamental = nursery-treatment-admission
  "granular bifenthrin incorporated/applied to potting media under fire-ant quarantine permits"
  "bifenthrin"
  ornamental
  "program guidance states protection can exceed 24 months depending on dose/product; permit is directed to ornamental/non-food nursery stock"
  false false true

fireAntGranularNonBearingFruit : NurseryTreatmentAdmission
fireAntGranularNonBearingFruit = nursery-treatment-admission
  "granular bifenthrin quarantine treatment"
  "bifenthrin"
  nonBearingFruitTree
  "persistent media treatment; transition to future bearing/food status is a separate consumer-state question"
  false false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ApprovedLabelCreatesPermanentSafety : Set where
data QuarantinePermitCreatesFoodResidueAdmission : Set where
data NonBearingStatusCreatesFutureEdibleSafety : Set where
data ChangedConsumptionCreatesToxicologyChange : Set where
data AustralianExamplesProveCountryWorseThanUS : Set where

approvedLabelDoesNotCreatePermanentSafety : ApprovedLabelCreatesPermanentSafety → ⊥
approvedLabelDoesNotCreatePermanentSafety ()

quarantinePermitDoesNotCreateFoodResidueAdmission : QuarantinePermitCreatesFoodResidueAdmission → ⊥
quarantinePermitDoesNotCreateFoodResidueAdmission ()

nonBearingStatusDoesNotCreateFutureEdibleSafety : NonBearingStatusCreatesFutureEdibleSafety → ⊥
nonBearingStatusDoesNotCreateFutureEdibleSafety ()

changedConsumptionDoesNotCreateToxicologyChange : ChangedConsumptionCreatesToxicologyChange → ⊥
changedConsumptionDoesNotCreateToxicologyChange ()

australianExamplesDoNotProveCountryWorseThanUS : AustralianExamplesProveCountryWorseThanUS → ⊥
australianExamplesDoNotProveCountryWorseThanUS ()

------------------------------------------------------------------------
-- Comparative governance surface.
------------------------------------------------------------------------

record JurisdictionComparison : Set where
  constructor jurisdiction-comparison
  field
    jurisdiction : String
    foodResidueFramework : String
    exposureModelReference : String
    reReviewMechanismReference : String
    tobaccoResidueReference : String
    strengths : String
    knownWeaknessOrResidual : String
open JurisdictionComparison public

australiaComparison : JurisdictionComparison
australiaComparison = jurisdiction-comparison
  "Australia"
  "APVMA MRL/use approval plus FSANZ dietary exposure modelling; residue analyses are required for pesticides used on edible crops"
  "FSANZ Harvest combines food chemical concentrations with individual consumption/body-weight data and high-consumer statistics"
  "chemical reviews, reconsiderations, permit/label variation and suspension; 2025 dimethoate berry action demonstrates reopening when exposure data change"
  "no cannabis-style retail tobacco pesticide CoA requirement located in the current federal tobacco framework"
  "individual-consumption modelling exists and 2025 action shows the system can reopen a prior approval"
  "niche-food consumption can move materially between major exposure-model updates; non-food permits and later consumer-state changes require explicit boundary tracking"

usComparison : JurisdictionComparison
usComparison = jurisdiction-comparison
  "United States"
  "EPA food tolerances under FFDCA with reasonable-certainty-of-no-harm safety finding, aggregate exposure and sensitive-subpopulation analysis"
  "DEEM-FCID uses NHANES/WWEIA consumption data; current published version still identifies 2005-2010 consumption data"
  "registration review periodically reexamines tolerances and may use surveillance/monitoring data"
  "FDA section 907 prohibits tobacco residues above any federal tolerance applicable to domestically grown tobacco, but FDA has historically stated no such tobacco tolerances were established"
  "aggregate-route framework and explicit child/sensitive-population analysis; USDA PDP provides food surveillance"
  "published dietary-model consumption base can itself be old; tobacco is not a clean example of stronger residue governance"

record ComparativeBoundary : Set where
  constructor comparative-boundary
  field
    australiaHasExposureModelStalenessExample : Bool
    australiaHasPersistentNonFoodQuarantineTreatment : Bool
    usAlsoHasStaleConsumptionModelIssue : Bool
    usTobaccoToleranceGapExistsHistorically : Bool
    countryScalarRankingPaid : Bool
open ComparativeBoundary public

canonicalComparativeBoundary : ComparativeBoundary
canonicalComparativeBoundary =
  comparative-boundary true true true true false

------------------------------------------------------------------------
-- Pareto roadmap.
------------------------------------------------------------------------

data AustraliaStandardsParetoTarget : Set where
  quantifyBerryPriorShift : AustraliaStandardsParetoTarget
  traceFireAntPlantLifecycle : AustraliaStandardsParetoTarget
  auditNonFoodToFoodTransitions : AustraliaStandardsParetoTarget
  compareAusUsConsumptionModelFreshness : AustraliaStandardsParetoTarget
  compareRetailSurveillance : AustraliaStandardsParetoTarget
  tobaccoResidueGovernance : AustraliaStandardsParetoTarget
  scalarCountryRanking : AustraliaStandardsParetoTarget

record AustraliaStandardsParetoStep : Set where
  constructor australia-standards-pareto-step
  field
    priority : Nat
    target : AustraliaStandardsParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open AustraliaStandardsParetoStep public

pareto0 : AustraliaStandardsParetoStep
pareto0 = australia-standards-pareto-step
  0 quantifyBerryPriorShift
  "recover the old versus contemporary berry-consumption distributions and calculate which exposure coordinate drove the dimethoate ARfD crossing"
  "exact stale-prior counterexample rather than qualitative narrative"
  "none"

pareto1 : AustraliaStandardsParetoStep
pareto1 = australia-standards-pareto-step
  1 traceFireAntPlantLifecycle
  "follow ornamental/non-bearing nursery stock after bifenthrin dip/media treatment into later retail, repotting and possible bearing/edible states"
  "same-object lifecycle transition"
  "permit legality alone does not pay downstream consumer state"

pareto2 : AustraliaStandardsParetoStep
pareto2 = australia-standards-pareto-step
  2 auditNonFoodToFoodTransitions
  "find explicit APVMA/state controls for a plant transitioning from non-bearing quarantine stock to food production"
  "bridge between quarantine permit and future food-residue governance"
  "same plant identity and elapsed time required"

pareto3 : AustraliaStandardsParetoStep
pareto3 = australia-standards-pareto-step
  3 compareAusUsConsumptionModelFreshness
  "compare dates, update cadence and niche-food supplementation in FSANZ Harvest versus EPA DEEM-FCID rather than comparing country labels"
  "model-governance comparison"
  "common basis required"

pareto4 : AustraliaStandardsParetoStep
pareto4 = australia-standards-pareto-step
  4 compareRetailSurveillance
  "compare Australian residue monitoring with USDA PDP and enforcement sampling by analyte, commodity, frequency and public-data availability"
  "observer/surveillance comparison"
  "model comparison alone is insufficient"

pareto5 : AustraliaStandardsParetoStep
pareto5 = australia-standards-pareto-step
  5 tobaccoResidueGovernance
  "continue the tobacco lane on both jurisdictions, including the US federal-tolerance paradox and Australian retail testing residual"
  "co-smoke source-vector governance"
  "separate from food MRL quality"

pareto99 : AustraliaStandardsParetoStep
pareto99 = australia-standards-pareto-step
  99 scalarCountryRanking
  "do not declare Australia globally worse or better than the US before normalising food, tobacco, quarantine, surveillance, update cadence and route-specific standards"
  "country-level ranking"
  "dominated by coordinate-wise comparison"

------------------------------------------------------------------------
-- Temporal fibre: approval is time-indexed because exposure priors can reopen.
------------------------------------------------------------------------

data StandardsTime : Set where
  dimethoate2017 : StandardsTime
  berryConsumption2025 : StandardsTime
  fireAntPermitCurrent : StandardsTime
  currentDashi : StandardsTime

data StandardsInterpretation : Set where
  usePatternAcceptedUnderPriorExposure : StandardsInterpretation
  consumptionPriorChanged : StandardsInterpretation
  foodUseReopened : StandardsInterpretation
  nonFoodQuarantineTreatmentPaid : StandardsInterpretation
  australiaGloballyWorseThanUS : StandardsInterpretation

data StandardsSummary : Set where exposurePriorMustBeVersioned : StandardsSummary

StandardsCompatible : StandardsTime → StandardsInterpretation → Set
StandardsCompatible dimethoate2017 usePatternAcceptedUnderPriorExposure = ⊤
StandardsCompatible dimethoate2017 consumptionPriorChanged = ⊥
StandardsCompatible dimethoate2017 foodUseReopened = ⊥
StandardsCompatible dimethoate2017 nonFoodQuarantineTreatmentPaid = ⊥
StandardsCompatible dimethoate2017 australiaGloballyWorseThanUS = ⊥
StandardsCompatible berryConsumption2025 usePatternAcceptedUnderPriorExposure = ⊤
StandardsCompatible berryConsumption2025 consumptionPriorChanged = ⊤
StandardsCompatible berryConsumption2025 foodUseReopened = ⊤
StandardsCompatible berryConsumption2025 nonFoodQuarantineTreatmentPaid = ⊥
StandardsCompatible berryConsumption2025 australiaGloballyWorseThanUS = ⊥
StandardsCompatible fireAntPermitCurrent usePatternAcceptedUnderPriorExposure = ⊤
StandardsCompatible fireAntPermitCurrent consumptionPriorChanged = ⊤
StandardsCompatible fireAntPermitCurrent foodUseReopened = ⊤
StandardsCompatible fireAntPermitCurrent nonFoodQuarantineTreatmentPaid = ⊤
StandardsCompatible fireAntPermitCurrent australiaGloballyWorseThanUS = ⊥
StandardsCompatible currentDashi usePatternAcceptedUnderPriorExposure = ⊤
StandardsCompatible currentDashi consumptionPriorChanged = ⊤
StandardsCompatible currentDashi foodUseReopened = ⊤
StandardsCompatible currentDashi nonFoodQuarantineTreatmentPaid = ⊤
StandardsCompatible currentDashi australiaGloballyWorseThanUS = ⊥

standardsTemporalSystem : Temporal.TemporalEvidenceSystem
standardsTemporalSystem = record
  { Time = StandardsTime
  ; Interpretation = StandardsInterpretation
  ; Compatible = StandardsCompatible
  ; Summary = StandardsSummary
  ; summarize = λ _ → exposurePriorMustBeVersioned
  ; timeReference = λ
      { dimethoate2017 → "dimethoate berry use accepted under the exposure state used in the 2017 reconsideration"
      ; berryConsumption2025 → "contemporary berry-consumption data reopen the acute dietary safety margin"
      ; fireAntPermitCurrent → "current fire-ant nursery-stock bifenthrin quarantine permits"
      ; currentDashi → "current DASHI Australian pesticide-governance Pareto frontier"
      }
  }

currentStandardsResidual : Temporal.EvidenceFibre standardsTemporalSystem currentDashi
currentStandardsResidual = Temporal.liveInterpretationAt consumptionPriorChanged tt

regressionReference : Regression.AustraliaExposurePriorRegression
regressionReference = Regression.requiredAustraliaExposurePriorRegression
