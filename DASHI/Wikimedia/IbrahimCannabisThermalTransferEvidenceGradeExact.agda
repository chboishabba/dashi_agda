module DASHI.Wikimedia.IbrahimCannabisThermalTransferEvidenceGradeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisThermalTransferEvidenceGradeRegression as Regression
import DASHI.Wikimedia.IbrahimCannabisContaminantSOTARoadmapExact as SOTA
import DASHI.Wikimedia.IbrahimCannabisCommonResiduePanelParetoExact as Residues
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- ROUTE-SPECIFIC THERMAL TRANSFER / PYROLYSIS EVIDENCE GRADES
--
-- The central rule is evidence-grade preservation.  A residue can be measured
-- on flower or in vape fluid without any direct evidence about transfer into
-- inhaled smoke/aerosol.  Likewise, a compound can have known thermal
-- decomposition chemistry outside cannabis without a measured cannabis dose.
------------------------------------------------------------------------

data EvidenceGrade : Set where
  directCannabisSmokeTransfer
  directCannabisVapeAerosolTransfer
  cannabisProductOccurrenceOnly
  nonCannabisThermalTransformation
  mechanisticPredictionOnly
  unresolved : EvidenceGrade

record ThermalTransferEvidence : Set where
  constructor thermal-transfer-evidence
  field
    analyte : String
    source : String
    year : Nat
    route : String
    matrix : String
    grade : EvidenceGrade
    result : String
    boundedReading : String
    directCannabisTransferPaid : Bool
    inhaledDosePaid : Bool
    toxicologicalHarmPaid : Bool
open ThermalTransferEvidence public

------------------------------------------------------------------------
-- Paclobutrazol: direct cannabis smoke-transfer experiment.
------------------------------------------------------------------------

paclobutrazolSmoke2013 : ThermalTransferEvidence
paclobutrazolSmoke2013 = thermal-transfer-evidence
  "paclobutrazol"
  "Nicholas Sullivan; Sytze Elzinga; Jeffrey C. Raber, Determination of Pesticide Residues in Cannabis Smoke, Journal of Toxicology 2013, DOI 10.1155/2013/378168"
  2013
  "combustion / mainstream cannabis smoke"
  "homogenized cannabis flower deliberately spiked with paclobutrazol"
  directCannabisSmokeTransfer
  "paclobutrazol recovery was 10.2% in filtered water-pipe smoke condensate, 49.5% in unfiltered water-pipe condensate, and 67.4% in glass-pipe condensate; n=3 per device"
  "This directly establishes device-dependent parent-residue transfer into collected mainstream smoke condensate under the study conditions. It does not establish chronic human dose, actual-market prevalence, or toxicological harm."
  true false false

------------------------------------------------------------------------
-- Myclobutanil: product occurrence and thermal-risk interpretation are not the
-- same object as a direct cannabis transfer experiment.
------------------------------------------------------------------------

myclobutanilRecallInterpretation2017 : ThermalTransferEvidence
myclobutanilRecallInterpretation2017 = thermal-transfer-evidence
  "myclobutanil"
  "Health Canada clarification on myclobutanil and cannabis, 2017"
  2017
  "combustion risk assessment of recalled cannabis"
  "recalled licensed cannabis products containing trace myclobutanil"
  mechanisticPredictionOnly
  "Health Canada estimated that additional cyanide attributable to the measured trace myclobutanil was over 1000-fold lower than cyanide already present in cannabis smoke and 500-fold below the cited NIOSH acceptable level; serious adverse-health risk was assessed as low for those recalled concentrations"
  "This is a dose-specific regulatory interpretation. It does not mean myclobutanil can never yield toxic thermal products, and it does not supply a direct measured smoke-transfer fraction for those products."
  false false false

myclobutanilVapeFluidOccurrence : ThermalTransferEvidence
myclobutanilVapeFluidOccurrence = thermal-transfer-evidence
  "myclobutanil"
  "Analysis of Cannabinoid-Containing Fluids in Illicit Vaping Cartridges Recovered from Pulmonary Injury Patients"
  2020
  "vape-product fluid occurrence"
  "illicit cannabinoid-containing vape fluids associated with EVALI investigations"
  cannabisProductOccurrenceOnly
  "myclobutanil was detected in numerous vape-fluid samples"
  "Presence in vape fluid is not equivalent to measured transfer into generated aerosol and does not identify thermal decomposition products."
  false false false

------------------------------------------------------------------------
-- Piperonyl butoxide: strong cannabis/vape occurrence evidence, but no direct
-- aerosol-transfer payment found in the current SOTA pass.
------------------------------------------------------------------------

pboVapeFluidOccurrence : ThermalTransferEvidence
pboVapeFluidOccurrence = thermal-transfer-evidence
  "piperonyl butoxide"
  "Analysis of Cannabinoid-Containing Fluids in Illicit Vaping Cartridges Recovered from Pulmonary Injury Patients"
  2020
  "vape-product fluid occurrence"
  "illicit cannabinoid-containing vape fluids"
  cannabisProductOccurrenceOnly
  "PBO was detected in numerous vape-fluid samples"
  "The current acquired surface pays occurrence in precursor fluid, not aerosol transfer, pyrolysis products, or inhaled dose."
  false false false

------------------------------------------------------------------------
-- Chlorfenapyr: cannabis occurrence is current; thermal/degradation chemistry
-- exists outside cannabis but must not be promoted into cannabis inhalation.
------------------------------------------------------------------------

chlorfenapyrNonCannabisThermal : ThermalTransferEvidence
chlorfenapyrNonCannabisThermal = thermal-transfer-evidence
  "chlorfenapyr"
  "Kandil et al., Effect of Light and Temperature on Chlorfenapyr and Identification of its Main Degradation Products, Research Journal of Environmental Toxicology 5 (2011) 316-322, DOI 10.3923/rjet.2011.316.322"
  2011
  "non-cannabis thermal / photodegradation"
  "technical chlorfenapyr under controlled temperature/light exposure"
  nonCannabisThermalTransformation
  "chlorfenapyr degradation increased with temperature and time; multiple transformation products were identified in the photodegradation experiments"
  "These transformation pathways are not direct cannabis smoke/vape pyrolysis products. The study operates at tens of degrees Celsius over hours/days, not smoking/vaping conditions."
  false false false

chlorfenapyrVapeRecallOccurrence : ThermalTransferEvidence
chlorfenapyrVapeRecallOccurrence = thermal-transfer-evidence
  "chlorfenapyr"
  "California Department of Cannabis Control mandatory recall, Backpackboyz PREMIUM VAPE Integrated Vaporizer, 17 July 2024"
  2024
  "vape-product contamination"
  "regulated integrated cannabis vaporizer product"
  cannabisProductOccurrenceOnly
  "California recalled the product for Category I chlorfenapyr contamination"
  "A contaminated vaporizer product establishes precursor-product occurrence; it does not by itself pay aerosol transfer or thermal-product identity."
  false false false

------------------------------------------------------------------------
-- Evidence-grade firewalls.
------------------------------------------------------------------------

data VapeFluidOccurrenceCreatesAerosolTransfer : Set where
data NonCannabisThermalCreatesCannabisPyrolysisIdentity : Set where
data SmokeTransferFractionCreatesHumanDose : Set where
data ThermalProductPossibilityCreatesClinicalHarm : Set where
data DeviceIndependentTransfer : Set where

vapeFluidOccurrenceDoesNotCreateAerosolTransfer : VapeFluidOccurrenceCreatesAerosolTransfer → ⊥
vapeFluidOccurrenceDoesNotCreateAerosolTransfer ()

nonCannabisThermalDoesNotCreateCannabisPyrolysisIdentity : NonCannabisThermalCreatesCannabisPyrolysisIdentity → ⊥
nonCannabisThermalDoesNotCreateCannabisPyrolysisIdentity ()

smokeTransferFractionDoesNotCreateHumanDose : SmokeTransferFractionCreatesHumanDose → ⊥
smokeTransferFractionDoesNotCreateHumanDose ()

thermalProductPossibilityDoesNotCreateClinicalHarm : ThermalProductPossibilityCreatesClinicalHarm → ⊥
thermalProductPossibilityDoesNotCreateClinicalHarm ()

deviceIndependentTransferIsFalse : DeviceIndependentTransfer → ⊥
deviceIndependentTransferIsFalse ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data ThermalParetoTarget : Set where
  modernPaclobutrazolReplication
  myclobutanilDirectSmokeProducts
  myclobutanilDirectVapeAerosolProducts
  chlorfenapyrDirectVapeAerosolProducts
  pboDirectVapeAerosolTransfer
  concentrationToInhaledDose
  broaderThermalPrediction : ThermalParetoTarget

record ThermalParetoStep : Set where
  constructor thermal-pareto-step
  field
    priority : Nat
    target : ThermalParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open ThermalParetoStep public

pareto0 : ThermalParetoStep
pareto0 = thermal-pareto-step
  0 myclobutanilDirectSmokeProducts
  "acquire a direct cannabis combustion experiment that measures myclobutanil parent transfer and thermal products, rather than inferring products from generic decomposition chemistry"
  "combustion same-object transformation packet"
  "none"

pareto1 : ThermalParetoStep
pareto1 = thermal-pareto-step
  1 myclobutanilDirectVapeAerosolProducts
  "measure or acquire aerosol-phase parent and transformation products from myclobutanil-contaminated cannabis material or extract under controlled vaporizer temperatures"
  "vaporisation-specific transformation packet"
  "smoking evidence cannot substitute"

pareto2 : ThermalParetoStep
pareto2 = thermal-pareto-step
  2 chlorfenapyrDirectVapeAerosolProducts
  "acquire direct aerosol chemistry for chlorfenapyr because current evidence pays contaminated vape-product occurrence but not aerosol transfer"
  "high-priority vape-route gap"
  "non-cannabis thermal data cannot substitute"

pareto3 : ThermalParetoStep
pareto3 = thermal-pareto-step
  3 pboDirectVapeAerosolTransfer
  "acquire parent PBO transfer and transformation products from contaminated cannabis vape fluid/aerosol"
  "aerosol-transfer closure"
  "precursor-fluid occurrence is insufficient"

pareto4 : ThermalParetoStep
pareto4 = thermal-pareto-step
  4 modernPaclobutrazolReplication
  "replicate the 2013 direct cannabis smoke-transfer experiment with modern controlled smoking topography and lower realistic residue levels"
  "modern transfer distribution and uncertainty"
  "2013 direct evidence is useful but high-spike and device-specific"

pareto5 : ThermalParetoStep
pareto5 = thermal-pareto-step
  5 concentrationToInhaledDose
  "combine measured source concentration, product mass, route-specific transfer fraction and puff/topography data only after each coordinate is paid"
  "inhaled-dose estimate"
  "direct route-specific transfer required first"

pareto99 : ThermalParetoStep
pareto99 = thermal-pareto-step
  99 broaderThermalPrediction
  "do not expand speculative thermal-product lists while direct cannabis smoke/vape measurements remain missing"
  "low marginal information"
  "dominated by same-object route measurements"

------------------------------------------------------------------------
-- Temporal evidence fibre.
------------------------------------------------------------------------

data ThermalTime : Set where
  smokeTransfer2013
  recallRisk2017
  vapeOccurrence2020
  currentSota2026 : ThermalTime

data ThermalInterpretation : Set where
  parentResidueCanTransferToSmoke
  vapeFluidOccurrenceIsNotAerosolTransfer
  routeSpecificProductsRemainOpen
  directDoseComplete : ThermalInterpretation

data ThermalSummary : Set where routeSpecificEvidenceGradesRequired : ThermalSummary

ThermalCompatible : ThermalTime → ThermalInterpretation → Set
ThermalCompatible smokeTransfer2013 parentResidueCanTransferToSmoke = ⊤
ThermalCompatible smokeTransfer2013 vapeFluidOccurrenceIsNotAerosolTransfer = ⊥
ThermalCompatible smokeTransfer2013 routeSpecificProductsRemainOpen = ⊤
ThermalCompatible smokeTransfer2013 directDoseComplete = ⊥
ThermalCompatible recallRisk2017 parentResidueCanTransferToSmoke = ⊤
ThermalCompatible recallRisk2017 vapeFluidOccurrenceIsNotAerosolTransfer = ⊥
ThermalCompatible recallRisk2017 routeSpecificProductsRemainOpen = ⊤
ThermalCompatible recallRisk2017 directDoseComplete = ⊥
ThermalCompatible vapeOccurrence2020 parentResidueCanTransferToSmoke = ⊤
ThermalCompatible vapeOccurrence2020 vapeFluidOccurrenceIsNotAerosolTransfer = ⊤
ThermalCompatible vapeOccurrence2020 routeSpecificProductsRemainOpen = ⊤
ThermalCompatible vapeOccurrence2020 directDoseComplete = ⊥
ThermalCompatible currentSota2026 parentResidueCanTransferToSmoke = ⊤
ThermalCompatible currentSota2026 vapeFluidOccurrenceIsNotAerosolTransfer = ⊤
ThermalCompatible currentSota2026 routeSpecificProductsRemainOpen = ⊤
ThermalCompatible currentSota2026 directDoseComplete = ⊥

thermalTemporalSystem : Temporal.TemporalEvidenceSystem
thermalTemporalSystem = record
  { Time = ThermalTime
  ; Interpretation = ThermalInterpretation
  ; Compatible = ThermalCompatible
  ; Summary = ThermalSummary
  ; summarize = λ _ → routeSpecificEvidenceGradesRequired
  ; timeReference = λ
      { smokeTransfer2013 → "Sullivan et al. direct cannabis smoke transfer experiment"
      ; recallRisk2017 → "Health Canada dose-specific myclobutanil recall interpretation"
      ; vapeOccurrence2020 → "EVALI-era contaminated cannabis vape-fluid occurrence studies"
      ; currentSota2026 → "current route-specific thermal-transfer evidence frontier"
      }
  }

currentThermalResidual : Temporal.EvidenceFibre thermalTemporalSystem currentSota2026
currentThermalResidual = Temporal.liveInterpretationAt routeSpecificProductsRemainOpen tt

regressionReference : Regression.RegressionRequirement
regressionReference = Regression.canonicalRegressionRequirement

record ThermalTransferBoundary : Set where
  constructor thermal-transfer-boundary
  field
    evidenceGradesSeparated : Bool
    deviceDependenceRetained : Bool
    vapeOccurrenceEqualsAerosolTransfer : Bool
    nonCannabisThermalEqualsCannabisPyrolysis : Bool
    parentTransferEqualsDose : Bool
    myclobutanilRecallRiskInterpretationRetained : Bool
open ThermalTransferBoundary public

canonicalThermalTransferBoundary : ThermalTransferBoundary
canonicalThermalTransferBoundary =
  thermal-transfer-boundary true true false false false true
