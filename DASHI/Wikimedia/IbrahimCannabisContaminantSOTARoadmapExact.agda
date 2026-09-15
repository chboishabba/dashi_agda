module DASHI.Wikimedia.IbrahimCannabisContaminantSOTARoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Architecture
import DASHI.Wikimedia.IbrahimCannabisBtBiopesticideExposureParetoExact as Bt
import DASHI.Wikimedia.IbrahimCannabisGlyphosateAMPAPyrolysisParetoExact as Glyphosate
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- 2026 SOTA ROADMAP FOR CANNABIS CONTAMINANTS / TESTING
--
-- The field is shifting from merely asking whether a contaminant is detectable
-- toward asking whether limits and study designs are route-specific,
-- toxicologically justified and comparable across jurisdictions.
--
-- SOTA source != standard already adopted != exact product safety conclusion.
------------------------------------------------------------------------

data SOTASourceRole : Set where
  recentAnalyticalReview
  recentToxicologyReview
  recentMarketSurveillance
  activeStandardWorkItem
  currentRegulatoryGuidance
  currentRegulatoryRulemaking
  legacyRiskAssessment : SOTASourceRole

record SOTASource : Set where
  constructor sota-source
  field
    authorsOrBody : String
    title : String
    publicationOrAuthority : String
    year : Nat
    doiOrIdentifier : String
    directLink : String
    role : SOTASourceRole
    boundedReading : String
    excludedPromotion : String
open SOTASource public

rosasPinto2026 : SOTASource
rosasPinto2026 = sota-source
  "Danna Valeria Rosas Pinto; Hui Li; Mingjing Sun"
  "Cannabis Products and Contaminant Detection: Critical Review of Regulatory Oversight and Analytical Methodologies"
  "Cannabis and Cannabinoid Research" 2026
  "10.1177/25785125261439008"
  "https://doi.org/10.1177/25785125261439008"
  recentAnalyticalReview
  "Compares U.S. adult-use contaminant regulation and 2020-2025 methods; finds wide jurisdictional variability and identifies ICP-MS, LC-MS/MS, GC-MS/MS and headspace GC as dominant modality-specific methods."
  "A review of available methods/regulations does not prove that every relevant contaminant class is covered or that any specific action level is health protective."

watsonEtAl2026 : SOTASource
watsonEtAl2026 = sota-source
  "Tyler D. Watson; Nicholas C. Glodosky; Tholo J. Johnson; Nicholas Poolman; Anthony Mistretta; Sarah A. Okey"
  "Pesticides in Cannabis: The Need for Evidence to Inform Policy and Protect Patients"
  "Clinical Therapeutics 48(9):902-906" 2026
  "10.1016/j.clinthera.2026.02.003"
  "https://doi.org/10.1016/j.clinthera.2026.02.003"
  recentToxicologyReview
  "Argues that many cannabis pesticide action levels are based on analytical detection limits or non-cannabis assumptions rather than cannabis-specific human-health risk, with special concern for medical users."
  "Commentary/review-level critique does not itself supply analyte-specific inhalation thresholds or prove patient harm from a measured residue."

partI2026 : SOTASource
partI2026 = sota-source
  "Current Opinion in Toxicology review authors"
  "Identification of reference values intended to be protective of human health for potential contaminants in hemp plant material and hemp-based products: Part I. Microbial and elemental contaminants"
  "Current Opinion in Toxicology 45:100567" 2026
  "10.1016/j.cotox.2025.100567"
  "https://doi.org/10.1016/j.cotox.2025.100567"
  recentToxicologyReview
  "Finds large regulatory variation for microbial and elemental contaminants, including harmful organisms without established reference values; proposes a conservative tiered-reference approach."
  "Recommended reference values are synthesis outputs and do not replace jurisdiction-specific law or product-specific exposure assessment."

partII2026 : SOTASource
partII2026 = sota-source
  "Current Opinion in Toxicology review authors"
  "Identification of reference values intended to be protective of human health for potential contaminants in hemp plant material and hemp-based products: Part II. Pesticides and solvents"
  "Current Opinion in Toxicology 45:100555" 2026
  "10.1016/j.cotox.2025.100555"
  "https://doi.org/10.1016/j.cotox.2025.100555"
  recentToxicologyReview
  "Finds substantial gaps and regional inconsistency in pesticide/solvent coverage, limits and testing; notes pesticide reference values often lack clear toxicological justification."
  "Conservative review-derived values are not equivalent to validated cannabis-inhalation risk levels for every analyte."

fiering2026 : SOTASource
fiering2026 = sota-source
  "Quinton Fiering et al."
  "Comparative analysis of metals, pesticides, mycotoxins, microbial contaminants and THC potency in illegal and regulated cannabis inflorescences in Canada"
  "Journal of Cannabis Research 8:48" 2026
  "10.1186/s42238-026-00414-y"
  "https://doi.org/10.1186/s42238-026-00414-y"
  recentMarketSurveillance
  "Fifty legal and fifty illegal Canadian samples were tested with validated methods across THC, pesticides, metals, mycotoxins and microbes; legal samples were much cleaner for pesticides overall but some legal products exceeded microbial limits and some elemental limits remained relevant."
  "Canadian surveillance does not establish prevalence in other jurisdictions and does not exhaust unmeasured contaminant classes such as Bt proteins or dedicated glyphosate/AMPA unless specifically included."

pmra2025 : SOTASource
pmra2025 = sota-source
  "Health Canada Pest Management Regulatory Agency"
  "Classification of cannabis and industrial hemp crops as use sites, data requirements and label amendments"
  "PMRA guidance" 2025
  "current guidance"
  "https://www.canada.ca/en/health-canada/services/consumer-product-safety/reports-publications/pesticides-pest-management/policies-guidelines/guidance-classification-cannabis-industrial-hemp-crops-use-sites-data-requirements-label-amendments.html"
  currentRegulatoryGuidance
  "Requires route-aware inhalation assessment for cannabis/hemp intended for smoking or vaping, including supervised residue trials and separate smoke/vape pyrolysis studies where applicable; flowering-stage biopesticide uses must address residue and pyrolysis requirements."
  "A regulatory data requirement is not evidence that every registered product already has publicly accessible, independently replicated route-specific data."

astmWK96795 : SOTASource
astmWK96795 = sota-source
  "ASTM Committee D37 / Subcommittee D37.03"
  "WK96795 New Specification for Risk Levels of Pesticides in Cannabinoid-Containing Extracts Intended for Inhalation"
  "ASTM work item" 2025
  "WK96795"
  "https://www.astm.org/membership-participation/technical-committees/workitems/workitem-wk96795"
  activeStandardWorkItem
  "Active work item seeks inhalation-specific, risk-based pesticide levels using hazard identification, dose-response, exposure estimation and uncertainty analysis for inhaled cannabinoid extracts."
  "Work item is under development and is not a published consensus standard; no numerical level is promoted from the work-item description alone."

california2026 : SOTASource
california2026 = sota-source
  "California Department of Cannabis Control"
  "DCC-2025-03-R pesticide testing final rulemaking materials"
  "California DCC" 2026
  "DCC-2025-03-R"
  "https://www.cannabis.ca.gov/cannabis-laws/rulemaking/dcc-2025-03-r-pesticide-testing/final-text/"
  currentRegulatoryRulemaking
  "Separates inhalable and non-inhalable pesticide action levels and phases in additional analytes/method validation; final statement of reasons explicitly weighs public-health protection against laboratory feasibility."
  "Different action levels do not by themselves prove complete inhalation toxicology; some values remain constrained by technical implementation and existing evidence."

efsaABTS351 : SOTASource
efsaABTS351 = sota-source
  "European Food Safety Authority"
  "Peer review of the pesticide risk assessment of Bacillus thuringiensis subsp. kurstaki strain ABTS-351"
  "EFSA Journal" 2021
  "10.2903/j.efsa.2021.6879"
  "https://doi.org/10.2903/j.efsa.2021.6879"
  legacyRiskAssessment
  "ABTS-351 assessment identifies unresolved repeated-inhalation/pathogenicity and non-dietary Cry-protein questions and requests viable-count residues linked to PHI to show harvest levels below the consumer threshold used in that assessment."
  "Agricultural EFSA data gaps do not establish cannabis consumer harm and do not substitute for post-application cannabis-flower measurements."

------------------------------------------------------------------------
-- Current SOTA interpretation.
------------------------------------------------------------------------

data SOTAClaim : Set where
  detectionTechnologyMature
  regulationHarmonised
  actionLevelsGenerallyHealthBased
  inhalationRouteMustBeModelled
  thermalTransformationMustBeModelled
  surveillanceSupportsLegalIllegalDifference
  btHarvestResidueResolved
  glyphosateCoverageUniversallyResolved
  crossClassMeasurementRequired : SOTAClaim

record SOTAStanding : Set where
  constructor sota-standing
  field
    claim : SOTAClaim
    standing : String
    evidenceReference : String
    paid : Bool
open SOTAStanding public

detectionStanding : SOTAStanding
detectionStanding = sota-standing
  detectionTechnologyMature
  "substantially paid for conventional target classes, with mature ICP-MS / LC-MS/MS / GC-MS/MS / headspace workflows and validated low-level methods"
  "Rosas Pinto et al. 2026 plus accredited Health Canada surveillance"
  true

harmonisationStanding : SOTAStanding
harmonisationStanding = sota-standing
  regulationHarmonised
  "not paid: current reviews still report major inter-jurisdiction variation in analyte lists, limits, validation and reporting"
  "Rosas Pinto et al. 2026; Current Opinion in Toxicology Parts I-II"
  false

healthBasedStanding : SOTAStanding
healthBasedStanding = sota-standing
  actionLevelsGenerallyHealthBased
  "not paid: 2026 toxicology/policy literature explicitly identifies action levels derived from analytical capability or non-cannabis assumptions"
  "Watson et al. 2026; Current Opinion in Toxicology Part II"
  false

inhalationStanding : SOTAStanding
inhalationStanding = sota-standing
  inhalationRouteMustBeModelled
  "paid as a regulatory/scientific design requirement for smoked/vaped cannabis; not yet paid as complete analyte-specific risk values"
  "PMRA cannabis/hemp guidance; ASTM WK96795 direction of travel"
  true

thermalStanding : SOTAStanding
thermalStanding = sota-standing
  thermalTransformationMustBeModelled
  "paid as a required evidential coordinate for pesticide-treated material intended for smoking/vaping"
  "PMRA requires distinct smoke- and vape-temperature pyrolysis studies using treated/radiolabelled material unless an acceptable waiver applies"
  true

surveillanceStanding : SOTAStanding
surveillanceStanding = sota-standing
  surveillanceSupportsLegalIllegalDifference
  "paid for Canadian 2026 sample: regulated products were substantially cleaner for pesticides than illegal samples, while microbial and elemental issues did not vanish"
  "Fiering et al. 2026"
  true

btStanding : SOTAStanding
btStanding = sota-standing
  btHarvestResidueResolved
  "not paid: no acquired same-object cannabis-flower dataset currently closes viable Btk/Cry burden at harvest after known application"
  "current DASHI acquisition plus EFSA ABTS-351 residue/inhalation data gaps"
  false

glyphosateStanding : SOTAStanding
glyphosateStanding = sota-standing
  glyphosateCoverageUniversallyResolved
  "not paid: historical marijuana occurrence exists, but inclusion/validated LOQ is panel-specific and cannot be inferred from generic multiresidue coverage"
  "IbrahimCannabisGlyphosateAMPAPyrolysisParetoExact plus current jurisdiction panels"
  false

crossClassStanding : SOTAStanding
crossClassStanding = sota-standing
  crossClassMeasurementRequired
  "paid: current regulation/reviews/surveillance span chemically and biologically distinct hazard classes requiring different observers"
  "measurement architecture owner plus 2026 analytical review"
  true

------------------------------------------------------------------------
-- Regulatory maturity ladder.
------------------------------------------------------------------------

data RiskMaturity : Set where
  detectabilityDriven
  ruleBasedActionLevel
  routeSeparatedActionLevel
  routeSpecificTransformationData
  healthBasedExposureThreshold
  harmonisedCrossJurisdictionStandard : RiskMaturity

record RiskMaturityReceipt : Set where
  constructor risk-maturity-receipt
  field
    stage : RiskMaturity
    status : String
    sourceReference : String
    globallyPaid : Bool
open RiskMaturityReceipt public

maturity0 : RiskMaturityReceipt
maturity0 = risk-maturity-receipt
  detectabilityDriven
  "historically common and still explicitly criticised in current literature"
  "Watson et al. 2026"
  true

maturity1 : RiskMaturityReceipt
maturity1 = risk-maturity-receipt
  ruleBasedActionLevel
  "widely implemented but jurisdiction-specific"
  "California/Canada/Australia regulatory architectures"
  true

maturity2 : RiskMaturityReceipt
maturity2 = risk-maturity-receipt
  routeSeparatedActionLevel
  "partially paid: California now separates inhalable and non-inhalable levels for many pesticides"
  "California DCC-2025-03-R final text"
  false

maturity3 : RiskMaturityReceipt
maturity3 = risk-maturity-receipt
  routeSpecificTransformationData
  "required prospectively by PMRA for smoking/vaping uses; public same-object datasets remain sparse"
  "PMRA DACO 7.8.1 guidance"
  false

maturity4 : RiskMaturityReceipt
maturity4 = risk-maturity-receipt
  healthBasedExposureThreshold
  "emerging rather than globally paid; ASTM WK96795 explicitly targets this gap for inhaled cannabinoid extracts"
  "ASTM WK96795; Current Opinion in Toxicology Part II"
  false

maturity5 : RiskMaturityReceipt
maturity5 = risk-maturity-receipt
  harmonisedCrossJurisdictionStandard
  "not paid"
  "2026 analytical/regulatory reviews identify persistent fragmentation"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CurrentReviewCreatesConsensusStandard : Set where
data WorkItemCreatesPublishedASTMStandard : Set where
data LegalMarketCreatesZeroContaminants : Set where
data ActionLevelCreatesHealthThreshold : Set where
data PyrolysisRequirementCreatesPyrolysisResult : Set where
data BtDataGapCreatesBtHarm : Set where

reviewDoesNotCreateConsensusStandard : CurrentReviewCreatesConsensusStandard → ⊥
reviewDoesNotCreateConsensusStandard ()

workItemDoesNotCreatePublishedASTMStandard : WorkItemCreatesPublishedASTMStandard → ⊥
workItemDoesNotCreatePublishedASTMStandard ()

legalMarketDoesNotCreateZeroContaminants : LegalMarketCreatesZeroContaminants → ⊥
legalMarketDoesNotCreateZeroContaminants ()

actionLevelDoesNotCreateHealthThreshold : ActionLevelCreatesHealthThreshold → ⊥
actionLevelDoesNotCreateHealthThreshold ()

pyrolysisRequirementDoesNotCreatePyrolysisResult : PyrolysisRequirementCreatesPyrolysisResult → ⊥
pyrolysisRequirementDoesNotCreatePyrolysisResult ()

btDataGapDoesNotCreateBtHarm : BtDataGapCreatesBtHarm → ⊥
btDataGapDoesNotCreateBtHarm ()

------------------------------------------------------------------------
-- Pareto roadmap after SOTA check.
------------------------------------------------------------------------

data SOTATarget : Set where
  deriveRouteSpecificRiskPackets
  acquirePyrolysisAndVapeData
  closeBtHarvestResidue
  normalizeJurisdictionRiskLevels
  modernGlyphosateAMPASurveillance
  expandGenericResidueList
  broadReviewAccumulation : SOTATarget

record SOTAParetoStep : Set where
  constructor sota-pareto-step
  field
    priority : Nat
    target : SOTATarget
    action : String
    pays : String
    dominatedUntil : String
open SOTAParetoStep public

pareto0 : SOTAParetoStep
pareto0 = sota-pareto-step
  0 deriveRouteSpecificRiskPackets
  "for the highest-prevalence / highest-concentration residues, bind flower concentration, smoke/vape transformation, inhaled dose and health-based endpoint rather than comparing concentration directly to a generic action level"
  "consumer-relevant risk packet"
  "none"

pareto1 : SOTAParetoStep
pareto1 = sota-pareto-step
  1 acquirePyrolysisAndVapeData
  "recover public registration dossiers or experiments that identify parent transfer and thermal products separately at smoking and vaping temperatures, prioritising myclobutanil, paclobutrazol, chlorfenapyr, piperonyl butoxide and other high-occurrence residues"
  "route-transformation coordinate required by current PMRA SOTA"
  "source residue/identity already paid for several candidates"

pareto2 : SOTAParetoStep
pareto2 = sota-pareto-step
  2 closeBtHarvestResidue
  "find or generate an evidence path from exact cannabis-authorised Bt product and application timing to viable-count and Cry-protein residue at harvest"
  "biopesticide residue/exposure admission"
  "do not infer from legal-use label or generic microbial count"

pareto3 : SOTAParetoStep
pareto3 = sota-pareto-step
  3 normalizeJurisdictionRiskLevels
  "compare California inhalable/non-inhalable action levels, Canada mandatory LoQs/registration risk requirements and Australian pharmacopoeial limits by analyte, route, toxicological basis and analytical feasibility"
  "separates detection threshold, compliance threshold and health threshold"
  "requires preserving jurisdiction/version date"

pareto4 : SOTAParetoStep
pareto4 = sota-pareto-step
  4 modernGlyphosateAMPASurveillance
  "seek post-legalisation cannabis/hemp flower glyphosate plus AMPA measurements using cannabis-validated dedicated polar methods"
  "modern prevalence and LOQ packet"
  "historical occurrence is already paid but not current-market prevalence"

pareto99 : SOTAParetoStep
pareto99 = sota-pareto-step
  99 expandGenericResidueList
  "add further pesticide names only when they discriminate a route-risk, panel-coverage or high-prevalence question"
  "low marginal information"
  "dominated by route-specific transformation/risk work"

pareto100 : SOTAParetoStep
pareto100 = sota-pareto-step
  100 broadReviewAccumulation
  "do not accumulate generic reviews once they cease changing the experiment or regulatory discriminator"
  "none by itself"
  "dominated by primary route-specific data"

------------------------------------------------------------------------
-- Temporal evidence fibre.
------------------------------------------------------------------------

data SOTATime : Set where
  legacyDetectionEra
  routeAwareRegulation2025
  currentSOTA2026 : SOTATime

data SOTAInterpretation : Set where
  detectionIsEnough
  routeSpecificRiskNeeded
  globallyHarmonisedHealthThresholdsExist : SOTAInterpretation

data SOTASummary : Set where routeRiskIsCurrentFrontier : SOTASummary

SOTACompatible : SOTATime → SOTAInterpretation → Set
SOTACompatible legacyDetectionEra detectionIsEnough = ⊤
SOTACompatible legacyDetectionEra routeSpecificRiskNeeded = ⊥
SOTACompatible legacyDetectionEra globallyHarmonisedHealthThresholdsExist = ⊥
SOTACompatible routeAwareRegulation2025 detectionIsEnough = ⊥
SOTACompatible routeAwareRegulation2025 routeSpecificRiskNeeded = ⊤
SOTACompatible routeAwareRegulation2025 globallyHarmonisedHealthThresholdsExist = ⊥
SOTACompatible currentSOTA2026 detectionIsEnough = ⊥
SOTACompatible currentSOTA2026 routeSpecificRiskNeeded = ⊤
SOTACompatible currentSOTA2026 globallyHarmonisedHealthThresholdsExist = ⊥

sotaTemporalSystem : Temporal.TemporalEvidenceSystem
sotaTemporalSystem = record
  { Time = SOTATime
  ; Interpretation = SOTAInterpretation
  ; Compatible = SOTACompatible
  ; Summary = SOTASummary
  ; summarize = λ _ → routeRiskIsCurrentFrontier
  ; timeReference = λ
      { legacyDetectionEra → "legacy cannabis contaminant testing focused primarily on analyte detection/compliance"
      ; routeAwareRegulation2025 → "PMRA cannabis/hemp guidance formalises smoking/vaping residue and pyrolysis data needs"
      ; currentSOTA2026 → "2026 reviews, surveillance, California rulemaking and ASTM work item emphasise route-specific risk and harmonisation gaps"
      }
  }

currentSOTAResidual : Temporal.EvidenceFibre sotaTemporalSystem currentSOTA2026
currentSOTAResidual = Temporal.liveInterpretationAt routeSpecificRiskNeeded tt

record CannabisContaminantSOTABoundary : Set where
  constructor cannabis-contaminant-sota-boundary
  field
    conventionalDetectionMature : Bool
    regulationsHarmonised : Bool
    actionLevelsGenerallyHealthBased : Bool
    inhalationSpecificRiskIsFrontier : Bool
    pyrolysisAndVapeTransformationRequired : Bool
    btHarvestResidueClosed : Bool
    astmWorkItemIsPublishedStandard : Bool
    legalMarketMeansZeroContaminants : Bool
open CannabisContaminantSOTABoundary public

canonicalCannabisContaminantSOTABoundary : CannabisContaminantSOTABoundary
canonicalCannabisContaminantSOTABoundary =
  cannabis-contaminant-sota-boundary true false false true true false false false
