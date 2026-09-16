module DASHI.Wikimedia.IbrahimCannabisGlyphosateAMPAPyrolysisParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisCommonResiduePanelParetoExact as Residues
import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Measurement
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- GLYPHOSATE / AMPA CANNABIS OCCURRENCE AND PYROLYSIS PARETO OWNER
--
-- This closes the previous "dedicated polar method likely required" gap with
-- direct marijuana-matrix occurrence evidence, while keeping occurrence,
-- modern compliance-panel inclusion, combustion products and toxicology apart.
------------------------------------------------------------------------

record GlyphosateOccurrenceSource : Set where
  constructor glyphosate-occurrence-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    matrix : String
    method : String
    sampleCount : String
    glyphosateResult : String
    ampaResult : String
    paraquatResult : String
    modernRegulatedMarketRepresentative : Bool
    inhalationRiskPaid : Bool
open GlyphosateOccurrenceSource public

lanaro2015 : GlyphosateOccurrenceSource
lanaro2015 = glyphosate-occurrence-source
  "Rafael Lanaro; Jose L. Costa; Silvia O. S. Cazenave; Luiz A. Zanolli-Filho; Marina F. M. Tavares; Alice A. M. Chasin"
  "Determination of Herbicides Paraquat, Glyphosate, and Aminomethylphosphonic Acid in Marijuana Samples by Capillary Electrophoresis"
  "Journal of Forensic Sciences 60(S1):S241-S247"
  2015
  "10.1111/1556-4029.12628"
  "130 marijuana samples"
  "capillary electrophoresis; glyphosate/AMPA extracted with 5 mmol/L HCl and measured by indirect UV/VIS; paraquat by capillary zone electrophoresis with direct UV"
  "n = 130"
  "3 samples positive, 0.15-0.75 mg/g"
  "1 sample positive for AMPA"
  "12 samples positive, 0.01-25.1 mg/g"
  false false

------------------------------------------------------------------------
-- Registry / metabolite distinction.
------------------------------------------------------------------------

record PolarHerbicideIdentity : Set where
  constructor polar-herbicide-identity
  field
    canonicalName : String
    role : String
    pubChemCID : String
    relationshipReference : String
    identityPaid : Bool
open PolarHerbicideIdentity public

glyphosateIdentity : PolarHerbicideIdentity
glyphosateIdentity = polar-herbicide-identity
  "glyphosate" "herbicide active ingredient" "3496"
  "parent analyte; PubChem CID inherited from common-residue owner"
  true

ampaIdentity : PolarHerbicideIdentity
ampaIdentity = polar-herbicide-identity
  "aminomethylphosphonic acid (AMPA)" "major glyphosate degradation/metabolite coordinate"
  ""
  "identity/name paid from primary analytical literature; PubChem CID intentionally left unpaid in this owner pending direct registry join"
  true

------------------------------------------------------------------------
-- Modern method coverage remains a separate question.
------------------------------------------------------------------------

record GlyphosatePanelCoverage : Set where
  constructor glyphosate-panel-coverage
  field
    panelReference : String
    targetMatrix : String
    exactGlyphosateIncluded : Bool
    exactAMPAIncluded : Bool
    matrixValidated : Bool
    analyteSpecificLOQPaid : Bool
open GlyphosatePanelCoverage public

currentGenericCannabisPanelResidual : GlyphosatePanelCoverage
currentGenericCannabisPanelResidual = glyphosate-panel-coverage
  "large LC-MS/MS + GC-MS/MS cannabis multiresidue panels such as the 2025 Canadian 96-analyte method and 2019 Oregon 367-analyte method do not automatically pay glyphosate/AMPA coverage"
  "dried cannabis flower/hemp"
  false false false false

lanaroCannabisMatrixCoverage : GlyphosatePanelCoverage
lanaroCannabisMatrixCoverage = glyphosate-panel-coverage
  "Lanaro et al. 2015 dedicated capillary-electrophoresis methods"
  "marijuana"
  true true true false

------------------------------------------------------------------------
-- Canada now explicitly requires pyrolysis evidence for pesticide uses on
-- cannabis/hemp intended for smoking or vaping.
------------------------------------------------------------------------

record PyrolysisRequirementReceipt : Set where
  constructor pyrolysis-requirement-receipt
  field
    regulator : String
    sourceReference : String
    cropScope : String
    routeScope : String
    requirement : String
    appliesGenericallyToPesticideUses : Bool
    glyphosateSpecificPyrolysisStudyAcquired : Bool
open PyrolysisRequirementReceipt public

canada2025PyrolysisRequirement : PyrolysisRequirementReceipt
canada2025PyrolysisRequirement = pyrolysis-requirement-receipt
  "Health Canada Pest Management Regulatory Agency"
  "Guidance: Classification of cannabis and industrial hemp crops as use sites, data requirements and label amendments"
  "cannabis and industrial hemp flowers/buds intended for smoking/vaping"
  "combustion / smoking and vaping exposure"
  "pyrolysis studies are required for pesticide uses intended on flower/bud consumed by smoking or vaping to identify potential pyrolytic by-products"
  true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HistoricalMarijuanaOccurrenceCreatesCurrentMarketPrevalence : Set where
data GlyphosateDetectionCreatesInhalationRisk : Set where
data GenericPanelCreatesGlyphosateCoverage : Set where
data PyrolysisRequirementCreatesPyrolysisResult : Set where

historicalOccurrenceDoesNotCreateCurrentMarketPrevalence : HistoricalMarijuanaOccurrenceCreatesCurrentMarketPrevalence → ⊥
historicalOccurrenceDoesNotCreateCurrentMarketPrevalence ()

glyphosateDetectionDoesNotCreateInhalationRisk : GlyphosateDetectionCreatesInhalationRisk → ⊥
glyphosateDetectionDoesNotCreateInhalationRisk ()

genericPanelDoesNotCreateGlyphosateCoverage : GenericPanelCreatesGlyphosateCoverage → ⊥
genericPanelDoesNotCreateGlyphosateCoverage ()

pyrolysisRequirementDoesNotCreatePyrolysisResult : PyrolysisRequirementCreatesPyrolysisResult → ⊥
pyrolysisRequirementDoesNotCreatePyrolysisResult ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data GlyphosateParetoTarget : Set where
  modernCannabisOccurrence
  cannabisValidatedLCMS
  ampaRegistryClosure
  combustionPyrolysis
  vaporisationTransformation
  inhaledDose : GlyphosateParetoTarget

record GlyphosateParetoStep : Set where
  constructor glyphosate-pareto-step
  field
    priority : Nat
    target : GlyphosateParetoTarget
    action : String
    pays : String
open GlyphosateParetoStep public

pareto0 : GlyphosateParetoStep
pareto0 = glyphosate-pareto-step
  0 modernCannabisOccurrence
  "find licensed and illicit modern cannabis/hemp flower surveys that deliberately include glyphosate plus AMPA with analyte-specific LOQ"
  "current-market prevalence and concentration"

pareto1 : GlyphosateParetoStep
pareto1 = glyphosate-pareto-step
  1 cannabisValidatedLCMS
  "acquire or validate a modern isotope-labelled polar LC-MS/MS glyphosate/AMPA method directly in cannabis flower"
  "method-performance bridge from historical capillary electrophoresis to current compliance analytics"

pareto2 : GlyphosateParetoStep
pareto2 = glyphosate-pareto-step
  2 ampaRegistryClosure
  "bind AMPA to direct authoritative molecular registry coordinates"
  "metabolite identity closure"

pareto3 : GlyphosateParetoStep
pareto3 = glyphosate-pareto-step
  3 combustionPyrolysis
  "find pesticide-specific cannabis/hemp pyrolysis experiments or registration dossiers for glyphosate/AMPA"
  "smoking transformation products and transfer fractions"

pareto4 : GlyphosateParetoStep
pareto4 = glyphosate-pareto-step
  4 vaporisationTransformation
  "do not reuse combustion results for vaporisation; measure relevant temperature/device conditions independently"
  "vape-route transformation packet"

pareto9 : GlyphosateParetoStep
pareto9 = glyphosate-pareto-step
  9 inhaledDose
  "calculate inhaled dose only after current source concentration and route-specific transfer are paid"
  "consumer exposure admission"

------------------------------------------------------------------------
-- Temporal fibre.
------------------------------------------------------------------------

data GlyphosateTime : Set where
  forensicOccurrence2015
  modernPanelEra
  canadaPyrolysisGuidance
  currentGlyphosateState : GlyphosateTime

data GlyphosateInterpretation : Set where
  cannabisOccurrenceDemonstrated
  modernPrevalenceKnown
  pyrolysisRequiredForUseRegistration
  routeRiskResolved : GlyphosateInterpretation

data GlyphosateSummary : Set where occurrencePaidExposureOpen : GlyphosateSummary

GlyphosateCompatible : GlyphosateTime → GlyphosateInterpretation → Set
GlyphosateCompatible forensicOccurrence2015 cannabisOccurrenceDemonstrated = ⊤
GlyphosateCompatible forensicOccurrence2015 modernPrevalenceKnown = ⊥
GlyphosateCompatible forensicOccurrence2015 pyrolysisRequiredForUseRegistration = ⊥
GlyphosateCompatible forensicOccurrence2015 routeRiskResolved = ⊥
GlyphosateCompatible modernPanelEra cannabisOccurrenceDemonstrated = ⊤
GlyphosateCompatible modernPanelEra modernPrevalenceKnown = ⊥
GlyphosateCompatible modernPanelEra pyrolysisRequiredForUseRegistration = ⊥
GlyphosateCompatible modernPanelEra routeRiskResolved = ⊥
GlyphosateCompatible canadaPyrolysisGuidance cannabisOccurrenceDemonstrated = ⊤
GlyphosateCompatible canadaPyrolysisGuidance modernPrevalenceKnown = ⊥
GlyphosateCompatible canadaPyrolysisGuidance pyrolysisRequiredForUseRegistration = ⊤
GlyphosateCompatible canadaPyrolysisGuidance routeRiskResolved = ⊥
GlyphosateCompatible currentGlyphosateState cannabisOccurrenceDemonstrated = ⊤
GlyphosateCompatible currentGlyphosateState modernPrevalenceKnown = ⊥
GlyphosateCompatible currentGlyphosateState pyrolysisRequiredForUseRegistration = ⊤
GlyphosateCompatible currentGlyphosateState routeRiskResolved = ⊥

glyphosateTemporalSystem : Temporal.TemporalEvidenceSystem
glyphosateTemporalSystem = record
  { Time = GlyphosateTime
  ; Interpretation = GlyphosateInterpretation
  ; Compatible = GlyphosateCompatible
  ; Summary = GlyphosateSummary
  ; summarize = λ _ → occurrencePaidExposureOpen
  ; timeReference = λ
      { forensicOccurrence2015 → "Lanaro et al. marijuana glyphosate/AMPA occurrence study"
      ; modernPanelEra → "modern cannabis multiresidue-method era"
      ; canadaPyrolysisGuidance → "current PMRA cannabis/hemp pesticide pyrolysis data requirement"
      ; currentGlyphosateState → "current DASHI glyphosate/AMPA Pareto frontier"
      }
  }

currentGlyphosateResidual : Temporal.EvidenceFibre glyphosateTemporalSystem currentGlyphosateState
currentGlyphosateResidual = Temporal.liveInterpretationAt cannabisOccurrenceDemonstrated tt

record CannabisGlyphosateAMPABoundary : Set where
  constructor cannabis-glyphosate-ampa-boundary
  field
    cannabisOccurrencePaid : Bool
    ampaCoOccurrenceObserved : Bool
    modernMarketPrevalencePaid : Bool
    genericPanelCoveragePaid : Bool
    pyrolysisRequirementPaid : Bool
    routeRiskPaid : Bool
open CannabisGlyphosateAMPABoundary public

canonicalCannabisGlyphosateAMPABoundary : CannabisGlyphosateAMPABoundary
canonicalCannabisGlyphosateAMPABoundary =
  cannabis-glyphosate-ampa-boundary true true false false true false
