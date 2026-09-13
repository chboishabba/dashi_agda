module DASHI.Culture.MissingDeceasedTwentyScientistRound8SourceReplayProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 8: SOURCE-EXACT REPLAY PROGRESS
-- Every retained scientist remains live. Four science lanes are promoted from
-- synthetic/qualitative finite witness toward source-exact replay coordinates;
-- the other sixteen retain one explicit science leaf and one custody leaf.
------------------------------------------------------------------------

record Round8ScientistProgress : Set where
  constructor round8-scientist-progress
  field
    person : String
    currentScienceState : String
    round8Delta : String
    sourceReplayPromoted : Bool
    nextScienceReplayLeaf : String
    nextCustodyLeaf : String

open Round8ScientistProgress public

nuno = round8-scientist-progress "Nuno F. G. Loureiro"
  "finite KREHM/Hermite/plasmoid machinery"
  "retained for source-exact Viriato benchmark/runtime weld"
  false
  "bind one published Viriato benchmark initial condition, closure and numerical output to executable owner"
  "repository maintainer, grant reassignment and simulation-state custodian"

leblanc = round8-scientist-progress "Joshua Kyle LeBlanc"
  "source-exact finite NASA FSP notional environment/sensor carrier"
  "retained; next replay is device-level qualification/failure evidence"
  false
  "one named sensor/device row with qualification protocol, calibration and failure envelope"
  "first real post-loss SNP I&C TechMat roster/handover"

maiwald = round8-scientist-progress "Frank W. Maiwald"
  "finite action-spectrum mechanism with source-exact trap/tag coordinates"
  "promoted to source-exact ValH+ spectral window/tag temperatures/1773 cm^-1 feature"
  true
  "recover raw/supporting spectrum intensities and photodissociation-time table for finite replay"
  "raw/reduced spectra, calibration files, notebooks and SURP handover"

reza = round8-scientist-progress "Monica Jacinto / Monica Reza"
  "finite alloy tradeoff/Pareto owners"
  "retained; source-exact descendant coating/enamel operating window remains highest science leaf"
  false
  "weld MONDALOY/enamel composition/process/oxygen-service qualification values to existing alloy tradeoff"
  "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custody"

grillmair = round8-scientist-progress "Carl J. Grillmair"
  "executable matched-filter distance-scan machinery"
  "retained; source data slice/orbit uncertainty remains replay leaf"
  false
  "one source-exact stream catalogue slice, colour-magnitude filter and orbit-fit uncertainty replay"
  "stream maps/catalogues/orbit-fit or unfinished manuscript custodian"

hicks = round8-scientist-progress "Michael David Hicks"
  "finite small-body photometry mechanism witness"
  "retained; replace synthetic lightcurve with one exact observation series"
  false
  "one source lightcurve with timestamps, magnitudes/errors, geometry and period/phase inference"
  "2022 JPL separation and unfinished observing/reduction/data handover"

mccasland = round8-scientist-progress "William Neil McCasland"
  "executable Gramian/failure-family finite engine"
  "retained; historical source-parameter weld remains next replay"
  false
  "bind published beam/plant matrices, candidate locations and failure family to executable engine"
  "dated DBE status and 2025-2026 client/programme carrier"

chavez = round8-scientist-progress "Anthony Chavez"
  "science identity-gated at LANL DARHT/Scorpius carrier"
  "gate retained; no science replay promoted across unpaid person identity"
  false
  "after same-person weld, recover exact Scorpius subsystem geometry/calibration/design responsibility"
  "primary same-person weld between missing-person and LANL engineering identities"

thomas = round8-scientist-progress "Jason R. Thomas"
  "finite signalling/target-deconvolution mechanism witness"
  "retained; actual assay/target-validation data remain source replay leaf"
  false
  "one Thomas-authored assay with perturbation counts/readout plus direct-target validation chain"
  "lab/project/data successor plus final event medical-examiner carrier"

amy = round8-scientist-progress "Amy Eskridge"
  "programme/mechanism-only; technical authorship unresolved"
  "authorship gate retained; no finite technical replay manufactured"
  false
  "recover Amy-authored/recorded equations, apparatus, presentation deck or reviewed technical manuscript"
  "Amy-linked NF-1676/EDAA/STRIVES object and Institute derivative/handover identity"

ning = round8-scientist-progress "Ning Li"
  "source-exact static-versus-rotating YBCO finite apparatus comparison"
  "retained; next science replay is later apparatus continuity/control matrix"
  false
  "recover AC Gravity/NASA/Army apparatus geometry, drive, calibration and control coordinates for comparison"
  "original FY2001 DoD row, Army SOW, closeout/result and apparatus custody"

chen = round8-scientist-progress "Chen Shuming"
  "finite graph-specification hardware-verification reconstruction"
  "retained; exact paper graph/stimulus/coverage example remains source replay leaf"
  false
  "recover graph semantics, stimulus corpus, coverage metric and one mismatch/verification example"
  "processor-specific responsibility and post-loss technical custodian"

feng = round8-scientist-progress "Feng Yanghe"
  "finite Bayesian/noisy-label classifier reconstruction"
  "retained; source equations/example data and War Skull same-object seam remain unpaid"
  false
  "replay one NUDT Press classifier example with model assumptions/noise parameters and outputs"
  "post-2023 War Skull code/project lead and primary event carrier"

zhou = round8-scientist-progress "Zhou Guangyuan"
  "source-exact SI thermal datum plus finite aerogel structure/property witness"
  "retained; multi-sample process/property replay is next"
  false
  "recover source table linking synthesis, shrinkage, porosity, surface area, temperature and conductivity across samples"
  "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"

liu = round8-scientist-progress "Liu Donghao"
  "finite DSMM lifecycle/evidence mechanism reconstruction"
  "retained; authored rubric/scoring remains source replay leaf"
  false
  "recover exact maturity levels, scoring semantics, clauses and one assessed example"
  "dated Liu-to-Liao governance transition and DSMM project custody"

zhangXiaoxin = round8-scientist-progress "Zhang Xiaoxin"
  "finite CEEMDAN-CWT forecast reconstruction"
  "promoted to 229-event Oulu source carrier, 166/63 split, 129/166 accurate, IMF4+IMF5 and 4-24 h timescale"
  true
  "recover exact spectral-whitening/CEEMDAN/CWT parameters, precursor quantisation rule and runnable source code/data"
  "dated NSMC/Fengyun successor and payload/ground-system custody"

zhangDaibing = round8-scientist-progress "Zhang Daibing"
  "finite UAV sensing/localisation/guidance/control reconstruction"
  "retained; select one DOI and source-replay its exact dynamics/control/test geometry"
  false
  "recover state definition, equations/control law, gains, sensor model and error series for one paper"
  "Yunzhihang/NUDT project and code custodian"

liMinyong = round8-scientist-progress "Li Minyong"
  "finite photoswitch/probe mechanism reconstruction"
  "retained; one exact compound/probe source replay remains next"
  false
  "recover molecule/probe, wavelength, photostationary state, affinity/selectivity, dose and readout kinetics"
  "post-loss lab/project/patent/student custodian"

fang = round8-scientist-progress "Fang Daining"
  "finite inverse-design mechanism witness"
  "promoted to source-exact design objective plus experimentally verified negative-group-velocity dispersion claim"
  true
  "recover full energy functional, unit-cell geometry/material constants and computed/experimental band structure"
  "post-loss BIT project/code/IP handover"

yan = round8-scientist-progress "Yan Hong"
  "finite Mach-5 thermal-excitation mechanism witness"
  "promoted to four source-exact E/N/S actuator cases and qualitative response ordering"
  true
  "recover geometry, mesh/boundaries, heat-source model and shock-angle/separation response curves"
  "named NPU flow-control project/code/data successor"

round8TwentyScientistProgress : List Round8ScientistProgress
round8TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round8ScientificCohortCount : Nat
round8ScientificCohortCount = 20

round8SourceReplayPromotionCount : Nat
round8SourceReplayPromotionCount = 4

round8EveryScientistTouched : Bool
round8EveryScientistTouched = true

sourceReplayDoesNotPayHistoricalDeployment : Bool
sourceReplayDoesNotPayHistoricalDeployment = false

sourceReplayDoesNotPayCommonProgramme : Bool
sourceReplayDoesNotPayCommonProgramme = false

sourceReplayDoesNotPayEventCause : Bool
sourceReplayDoesNotPayEventCause = false
