module DASHI.Culture.MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round14ScientistProgress : Set where
  constructor round14-scientist-progress
  field
    person : String
    currentScienceState : String
    round14Delta : String
    sourceDataReplayPromoted : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round14ScientistProgress public

nuno = round14-scientist-progress "Nuno F. G. Loureiro" "finite/executable KREHM-Hermite-plasmoid machinery" "retained; published Viriato benchmark remains the next source-data weld" false "bind exact initial condition, closure, discretisation and benchmark output" "repository maintainer, grant reassignment and simulation-state custodian"
leblanc = round14-scientist-progress "Joshua Kyle LeBlanc" "source-exact FSP I&C environment arithmetic" "retained; device-level calibration/qualification row remains next" false "one named sensor/device with calibration, qualification and failure-response values" "first post-loss SNP I&C TechMat roster/handover"
maiwald = round14-scientist-progress "Frank W. Maiwald" "source spectral-window/tag-temperature reference kernel" "retained; raw intensity/dissociation arrays remain hidden producer" false "raw ValH+ spectrum intensities, calibration and dissociation-time table" "raw/reduced spectra, notebooks and SURP handover"
reza = round14-scientist-progress "Monica Jacinto / Monica Reza" "source-exact alloy example compositions and burn/strength tradeoff" "retained; MONDALOY/enamel descendant numerical process window remains next" false "descendant coating/enamel composition, process and oxygen-service qualification values" "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custodian"
grillmair = round14-scientist-progress "Carl J. Grillmair" "executable matched-filter/distance-scan science" "retained; source catalogue/filter/orbit arrays remain next" false "one exact stream catalogue slice, filter weights and orbit uncertainty replay" "stream-map/catalogue/orbit-fit custodian"
hicks = round14-scientist-progress "Michael David Hicks" "source-bound 3122 Florence photometry campaign" "promoted campaign date/observatory/2.4 h period and radar-consistency coordinates while raw Hicks lightcurve remains unpaid" true "recover Hicks raw lightcurve, viewing geometry and photometric calibration" "2017 campaign data custodian plus 2022 JPL separation/handover"
mccasland = round14-scientist-progress "William Neil McCasland" "executable Gramian/failure-family placement engine" "retained; historical beam matrices remain next source-data replay" false "published plant matrices, candidate locations and failure family" "dated DBE status and 2025-2026 client/programme carrier"
chavez = round14-scientist-progress "Anthony Chavez" "identity-gated DARHT/Scorpius engineering carrier" "identity gate retained; no source-data replay crosses the unpaid same-person seam" false "after identity weld, exact subsystem geometry/calibration/design responsibility" "primary same-person weld between missing-person and LANL identities"
thomas = round14-scientist-progress "Jason R. Thomas" "finite signalling/target-deconvolution carrier" "promoted source-exact macrophage IRF3/NFkB readout topology, PRAK candidate, and PIK-III/NCOA4/FTH1 mechanism coordinates; per-well arrays remain unpaid" true "supporting-information screen matrix, dose-response arrays and proteomics table" "lab/project/data successor plus final ME carrier"
amy = round14-scientist-progress "Amy Eskridge" "programme-level mechanism-discrimination carrier" "authorship gate retained; no technical data replay manufactured" false "Amy-authored/recorded equations, apparatus, deck or reviewed technical manuscript" "Amy-linked NF-1676/EDAA/STRIVES and Institute derivative/handover"
ning = round14-scientist-progress "Ning Li" "static-versus-rotating YBCO apparatus comparison" "promoted exact 2-parts-per-1e8 static bound plus 15 cm / 12000 rpm / <60 G outer / <10 G centre rotating coordinates" true "recover later AC Gravity/Army apparatus geometry, calibration, controls and result table" "FY2001 DoD row, Army SOW, closeout/result and apparatus custody"
chen = round14-scientist-progress "Chen Shuming" "finite graph-specification hardware-verification reconstruction" "retained; exact graph/stimulus/coverage example remains next" false "source graph semantics, stimulus corpus, coverage metric and mismatch example" "processor responsibility and post-loss technical custodian"
feng = round14-scientist-progress "Feng Yanghe" "finite Bayesian/noisy-label classification carrier" "promoted publisher-exact multinomial/Dirichlet, no-preprocessing, automatic filtering, sampling and simulation/real-data method coordinates; numeric example remains blocked" true "book equations, example dataset, noise parameters and classifier outputs" "post-2023 War Skull code/project lead and primary event carrier"
zhou = round14-scientist-progress "Zhou Guangyuan" "source-exact aerogel SI thermal datum" "promoted named PI-D1 and PI-A4 sample coordinates including 674.8 m2/g, BDFA/ODA=1/3, 54.3 mW m-1 K-1 at 200 C, 7.7% shrinkage and ~24 nm pores" true "complete multi-sample synthesis/process/property table and uncertainty" "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"
liu = round14-scientist-progress "Liu Donghao" "finite DSMM lifecycle/evidence carrier" "retained; authored scoring/rubric data remain next" false "maturity levels, scoring semantics, authored clauses and one assessed example" "dated Liu-to-Liao governance transition and project custody"
zhangXiaoxin = round14-scientist-progress "Zhang Xiaoxin" "229-event source forecast replay and reference projection" "retained; algorithm hyperparameters/event-level arrays remain hidden producer" false "whitening/CEEMDAN/CWT parameters, precursor rule and event-level input/output table" "dated NSMC/Fengyun successor and payload/ground-system custody"
zhangDaibing = round14-scientist-progress "Zhang Daibing" "finite UAV guidance/control carrier" "promoted source-exact DFC multi-surface architecture, PSO parameter design, air-wake/deck-motion disturbance model and touchdown-dispersion objective; numeric gains/time series remain unpaid" true "vehicle model, controller gains, disturbance PSDs and touchdown-dispersion series" "Yunzhihang/NUDT project and code custodian"
liMinyong = round14-scientist-progress "Li Minyong" "finite photopharmacology/probe carrier" "retained; compound-specific source data remain next" false "one molecule/probe wavelength, state fraction, affinity, dose and readout kinetics" "post-loss lab/project/patent/student custodian"
fang = round14-scientist-progress "Fang Daining" "source inverse-design objective/reference projection" "retained; solver blocked on energy functional/geometry/band arrays" false "complete energy functional, unit-cell geometry/constants and computed/experimental bands" "post-loss BIT project/code/IP handover"
yan = round14-scientist-progress "Yan Hong" "source-exact four-case Mach-5 thermal-excitation reference kernel" "retained; response curves and solver geometry remain next" false "mesh/boundaries, heat-source model and shock/separation curves" "named NPU flow-control project/code/data successor"

round14TwentyScientistProgress : List Round14ScientistProgress
round14TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round14ScientificCohortCount : Nat
round14ScientificCohortCount = 20

round14SourceDataReplayPromotionCount : Nat
round14SourceDataReplayPromotionCount = 6

round14EveryScientistTouched : Bool
round14EveryScientistTouched = true

sourceDataReplayDoesNotPayHistoricalDeployment : Bool
sourceDataReplayDoesNotPayHistoricalDeployment = false

sourceDataReplayDoesNotPayCustody : Bool
sourceDataReplayDoesNotPayCustody = false

sourceDataReplayDoesNotPayCommonProgramme : Bool
sourceDataReplayDoesNotPayCommonProgramme = false

sourceDataReplayDoesNotPayEventCause : Bool
sourceDataReplayDoesNotPayEventCause = false
