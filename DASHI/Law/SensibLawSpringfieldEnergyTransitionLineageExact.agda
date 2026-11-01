module DASHI.Law.SensibLawSpringfieldEnergyTransitionLineageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SPRINGFIELD ENERGY TRANSITION LINEAGE
--
-- This owner keeps three eras distinct:
--   2004 gas/electricity greenfield rollout;
--   2018 long-horizon ENGIE net-zero alliance;
--   Energy Queensland/Energex net-zero planning and electrification study.
--
-- The purpose is to test legacy gas lock-in versus later transition policy.
-- Neither chronology nor corporate proximity is promoted into intent.
------------------------------------------------------------------------

data EnergyEra : Set where
  gasBuildout2004 : EnergyEra
  netZeroAlliance2018 : EnergyEra
  electrificationPlanning2020s : EnergyEra

data EvidenceStatus : Set where
  firstPartyPaid : EvidenceStatus
  governmentPrimaryPaid : EvidenceStatus
  secondaryLocatorOnly : EvidenceStatus

record EnergyLineageReceipt : Set where
  constructor energy-lineage-receipt
  field
    era : EnergyEra
    source : Source.AttributedSource
    boundedStatement : String
    status : EvidenceStatus
    provesFossilIntent : Bool
    provesFossilIntentIsFalse : provesFossilIntent ≡ false

open EnergyLineageReceipt public

abcSpringfieldGasRollout : Source.AttributedSource
abcSpringfieldGasRollout = Source.mkNoDOISource
  "Australian Broadcasting Corporation"
  "Development aims to set alternative energy use trend"
  "ABC News"
  "2004"
  "https://www.abc.net.au/news/2004-04-30/development-aims-to-set-alternative-energy-use/178340"
  Source.newsSource
  "Contemporaneous secondary locator reporting an Energex–Springfield Land Corporation alliance to build gas and electricity networks, including an Energex statement referring to 8,000 gas connections. Original agreement remains unpaid."
  Source.publicAttribution

engieSpringfieldAlliance : Source.AttributedSource
engieSpringfieldAlliance = Source.mkNoDOISource
  "ENGIE"
  "ENGIE partners with Greater Springfield to develop Zero Net Energy city of the future"
  "ENGIE press release"
  "2018"
  "https://www.engie.com/en/journalists/press-releases/partners-greater-springfield-australia-zero-net-energy-city"
  Source.practitionerSource
  "First-party source recording a 50-year strategic alliance between ENGIE and Springfield City Group targeting a net-zero-energy Greater Springfield by 2038, with renewable generation, storage, district energy, green mobility and energy-efficiency investments."
  Source.publicAttribution

energexSpringfieldNetZeroStudy : Source.AttributedSource
energexSpringfieldNetZeroStudy = Source.mkNoDOISource
  "Energy Queensland / Energex"
  "DMIA Case Study — Springfield Net Zero"
  "Demand Management Innovation Allowance case study"
  "2026"
  "https://www.energex.com.au/__data/assets/pdf_file/0019/1016416/DMIA-Case-Study-Springfield-Net-Zero.pdf"
  Source.governmentSource
  "Network-planning case study undertaken with Springfield City Group and Tractebel examining energy transitions, developer/network collaboration, greenfield energy-density planning and allowance for electrification of transport. It does not state that existing reticulated gas is removed or that dwellings are all-electric."
  Source.publicAttribution

energexGasRollout2004 : EnergyLineageReceipt
energexGasRollout2004 = energy-lineage-receipt
  gasBuildout2004
  abcSpringfieldGasRollout
  "In 2004, ABC reported Energex and Springfield Land Corporation planning a combined gas/electricity network at Springfield, with Energex referring to 8,000 gas connections."
  secondaryLocatorOnly
  false refl

engieNetZeroAlliance2018 : EnergyLineageReceipt
engieNetZeroAlliance2018 = energy-lineage-receipt
  netZeroAlliance2018
  engieSpringfieldAlliance
  "In 2018, ENGIE and Springfield City Group publicly announced a 50-year strategic alliance aimed at making Greater Springfield net zero energy by 2038."
  firstPartyPaid
  false refl

energexNetZeroStudy : EnergyLineageReceipt
energexNetZeroStudy = energy-lineage-receipt
  electrificationPlanning2020s
  energexSpringfieldNetZeroStudy
  "The Energy Queensland/Energex case study examines how greenfield-development planning, distributed energy resources and electrification affect network design in partnership with Springfield City Group."
  governmentPrimaryPaid
  false refl

springfieldEnergyLineageSources : List Source.AttributedSource
springfieldEnergyLineageSources =
  abcSpringfieldGasRollout ∷
  engieSpringfieldAlliance ∷
  energexSpringfieldNetZeroStudy ∷
  []

------------------------------------------------------------------------
-- Residual: did later transition policy actually retire or avoid gas endpoints?
------------------------------------------------------------------------

record TransitionResidual : Set where
  constructor transition-residual
  field
    label : String
    missingObject : String
    whyNeeded : String
    paid : Bool

open TransitionResidual public

gasLegacyVersusTransitionResidual : TransitionResidual
gasLegacyVersusTransitionResidual = transition-residual
  "Springfield legacy-gas versus net-zero transition"
  "Project-by-project gas-reticulation policy, dwelling appliance specifications, gas-connection counts over time, any gas-disconnection/decommissioning plan, and the 2018/2020 transition roadmaps' treatment of existing gas infrastructure."
  "A net-zero alliance and electrification planning do not themselves show whether the earlier gas network was retired, frozen, expanded, or carried into later residential projects."
  false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data HistoricalGasBuildoutProvesCurrentFossilPolicy : Set where
data NetZeroAllianceProvesGasRemoval : Set where
data ElectrificationStudyProvesExistingGasDecommissioning : Set where
data ENGIEAllianceProvesNoFossilInterest : Set where

historicalGasBuildoutDoesNotProveCurrentFossilPolicy : HistoricalGasBuildoutProvesCurrentFossilPolicy → ⊥
historicalGasBuildoutDoesNotProveCurrentFossilPolicy ()

netZeroAllianceDoesNotProveGasRemoval : NetZeroAllianceProvesGasRemoval → ⊥
netZeroAllianceDoesNotProveGasRemoval ()

electrificationStudyDoesNotProveExistingGasDecommissioning : ElectrificationStudyProvesExistingGasDecommissioning → ⊥
electrificationStudyDoesNotProveExistingGasDecommissioning ()

engieAllianceDoesNotProveNoFossilInterest : ENGIEAllianceProvesNoFossilInterest → ⊥
engieAllianceDoesNotProveNoFossilInterest ()

------------------------------------------------------------------------
-- Pareto policy.
------------------------------------------------------------------------

record EnergyTransitionPareto : Set where
  constructor energy-transition-pareto
  field
    gasBuildoutAgreementFirst : Bool
    connectionCountsThroughTimeSecond : Bool
    projectSpecificationsThird : Bool
    netZeroRoadmapTreatmentOfGasFourth : Bool
    decommissioningOrExpansionRecordsFifth : Bool
    beneficiaryAnalysisAfterAssetAndDemandReceipts : Bool
    chronologyMayGenerateHypothesis : Bool
    chronologyMayProveIntent : Bool

canonicalEnergyTransitionPareto : EnergyTransitionPareto
canonicalEnergyTransitionPareto = energy-transition-pareto
  true true true true true true true false
