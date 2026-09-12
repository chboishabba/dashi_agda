module DASHI.Culture.MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 7: ALL-TWENTY SCIENCE DEPTH + CUSTODY PROGRESS
------------------------------------------------------------------------

record Round7ScientistProgress : Set where
  constructor round7-scientist-progress
  field
    person : String
    scienceDepth : String
    round7ScienceDelta : String
    scienceNextLeaf : String
    custodyNextLeaf : String
    round7PromotedDepth : Bool

open Round7ScientistProgress public

nunoRound7 = round7-scientist-progress
  "Nuno F. G. Loureiro"
  "finite witness"
  "existing KREHM/Hermite/plasmoid finite machinery retained; no invented new Viriato benchmark"
  "source-weld one Viriato/KREHM benchmark and executable repository/runtime receipt"
  "named repository/grant/simulation-state successor"
  false

leblancRound7 = round7-scientist-progress
  "typed mechanism"
  "FSP I&C gap/qualification surface retained; finite source-exact acceptance/failure matrix still open"
  "formalise one exact sensor/qualification matrix with finite acceptance/failure witness"
  "first dated TechMat roster revision and calibration/failure-data handover"
  false

maiwaldRound7 = round7-scientist-progress
  "equation depth"
  "action-spectroscopy/QIT equation machinery retained; DOI-linked finite spectrum remains open"
  "instantiate one protonated-valine tagged-ion spectrum with calibrated action response"
  "raw/reduced spectra, calibration and notebook custody"
  false

rezaRound7 = round7-scientist-progress
  "finite witness"
  "alloy tradeoff/Pareto witnesses retained; application descendant still needs source-exact operating-window finite witness"
  "add MONDALOY/enamel descendant oxygen-service operating-window witness"
  "Boeing/UTC/Rocketdyne assignment and process-window custodian"
  false

grillmairRound7 = round7-scientist-progress
  "executable witness"
  "matched-filter distance-scan executable machinery retained"
  "bind one source-exact stream slice and orbit-fit uncertainty receipt"
  "stream maps/catalogues and unfinished-work custodian"
  false

hicksRound7 = round7-scientist-progress
  "typed mechanism"
  "small-body photometry inference remains source-attributed without one finite source data transform"
  "select one exact lightcurve and formalise measurement-to-rotation/phase inference"
  "2022 JPL departure and unfinished dataset/pipeline handover"
  false

mccaslandRound7 = round7-scientist-progress
  "executable witness"
  "finite Gramian/failure-family engine retained"
  "source-weld finite beam parameters to the historical flexible-structure example"
  "dated DBE role and event-time client/programme carrier"
  false

chavezRound7 = round7-scientist-progress
  "identity gated"
  "Scorpius science remains deliberately blocked from missing-person inheritance"
  "same-person weld before subsystem/calibration deepening"
  "missing-person to LANL engineering-profile identity receipt"
  false

thomasRound7 = round7-scientist-progress
  "equation depth"
  "signalling/target-deconvolution compiler retained"
  "instantiate one Thomas-authored assay/perturbation dataset through the mechanism compiler"
  "lab/project/data successor plus final event carrier"
  false

amyRound7 = round7-scientist-progress
  "programme only"
  "mechanism-comparison machinery retained; no Amy-authored science object manufactured"
  "recover Amy-authored or Amy-recorded equations/apparatus object"
  "Amy-linked NF-1676/EDAA/STRIVES and Institute derivative handover"
  false

ningRound7 = round7-scientist-progress
  "typed mechanism"
  "static/rotating YBCO constraints retained; finite apparatus/confounder comparison remains open"
  "formalise static-versus-rotating apparatus/configuration/control matrix"
  "Army SOW/closeout and NCC8-124 to DAAH01-01-9-R001 continuity"
  false

chenRound7 = round7-scientist-progress
  "finite mechanism witness"
  "added finite graph-specification verification stage witness; explicitly synthetic rather than paper numerical replication"
  "replace synthetic counts with source graph semantics, stimuli, coverage and mismatch oracle"
  "processor/project responsibility successor and event identity"
  true

fengRound7 = round7-scientist-progress
  "typed mechanism"
  "Bayesian/noisy-label and War Skull fibres remain separated"
  "instantiate one finite Bayesian/noisy-label classifier and preserve software same-object firewall"
  "post-2023 War Skull code/project custodian"
  false

zhouRound7 = round7-scientist-progress
  "finite source witness"
  "added source-exact SI thermal datum and finite reported structure/property coordinates"
  "extend to finite multi-sample shrinkage/porosity/thermal portfolio and process relation"
  "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"
  true

liuRound7 = round7-scientist-progress
  "finite mechanism witness"
  "added finite lifecycle/evidence maturity-assessment shape; official score remains unpaid"
  "replace synthetic control/evidence counts with Liu-authored scoring/rubric and a source-exact assessment"
  "dated Liu-to-Liao governance/project transition"
  true

zhangXiaoxinRound7 = round7-scientist-progress
  "finite mechanism witness"
  "added finite whitening-to-CEEMDAN-to-CWT pipeline carrier; source hyperparameters/metrics remain unpaid"
  "replace synthetic series with source dataset, CEEMDAN/wavelet settings, prediction rule and metrics"
  "dated NSMC/Fengyun successor and committee reconstitution"
  true

zhangDaibingRound7 = round7-scientist-progress
  "finite mechanism witness"
  "added finite sensing/fusion/localisation/guidance/control carrier; no specific flight replication claimed"
  "select one DOI and replace synthetic counts with dynamics, gains, geometry and measured errors"
  "Yunzhihang/NUDT project and code custodian"
  true

liMinyongRound7 = round7-scientist-progress
  "finite mechanism witness"
  "added reversible light-state/binding/readout mechanism witness; compound-specific performance remains unpaid"
  "replace synthetic state witness with one exact molecule/probe wavelength, affinity, dose and kinetics"
  "post-loss lab/project/patent/student custodian"
  true

fangRound7 = round7-scientist-progress
  "typed mechanism"
  "active metamaterial/inverse-design owner retained"
  "formalise DOI 10.1016/j.jmps.2025.106144 energy-map/eigenmode finite witness"
  "post-loss BIT project/code/experimental-state handover"
  false

yanRound7 = round7-scientist-progress
  "typed mechanism"
  "thermal-excitation inlet-control owner retained"
  "recover source geometry/power/response values and add finite shock/separation witness"
  "post-loss NPU inlet/plasma-flow-control project successor"
  false

twentyScientistRound7Progress : List Round7ScientistProgress
twentyScientistRound7Progress =
  nunoRound7 ∷ leblancRound7 ∷ maiwaldRound7 ∷ rezaRound7 ∷ grillmairRound7 ∷
  hicksRound7 ∷ mccaslandRound7 ∷ chavezRound7 ∷ thomasRound7 ∷ amyRound7 ∷ ningRound7 ∷
  chenRound7 ∷ fengRound7 ∷ zhouRound7 ∷ liuRound7 ∷ zhangXiaoxinRound7 ∷
  zhangDaibingRound7 ∷ liMinyongRound7 ∷ fangRound7 ∷ yanRound7 ∷ []

round7ScientificCohortCount : Nat
round7ScientificCohortCount = 20

round7EveryScientistTouched : Bool
round7EveryScientistTouched = true

round7EveryScientistHasScienceLeaf : Bool
round7EveryScientistHasScienceLeaf = true

round7EveryScientistHasCustodyLeaf : Bool
round7EveryScientistHasCustodyLeaf = true

finiteWitnessDoesNotCreateHistoricalDeployment : Bool
finiteWitnessDoesNotCreateHistoricalDeployment = false

syntheticWitnessDoesNotBecomeSourceResult : Bool
syntheticWitnessDoesNotBecomeSourceResult = false

finiteMechanismWitnessDoesNotCreateEventCause : Bool
finiteMechanismWitnessDoesNotCreateEventCause = false
