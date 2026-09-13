module DASHI.Culture.MissingDeceasedTwentyScientistRound19CrossPollinationParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round19Progress : Set where
  constructor round19-progress
  field
    person : String
    scienceExecutionState : String
    round19Delta : String
    crossPollinationPromoted : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round19Progress public

nuno = round19-progress "Nuno F. G. Loureiro" "finite/executable KREHM-Hermite-plasmoid machinery" "retained; apply source-producer/materialization ladder once a published Viriato benchmark payload is fixed" false "one source-exact Viriato initial condition, closure, discretisation and output replay" "repository maintainer, grant reassignment and simulation-state custodian"
leblanc = round19-progress "Joshua Kyle LeBlanc" "source-exact FSP I&C environment envelope" "retained; reuse finite qualification-envelope machinery at named-device level" false "one named sensor/device calibration, qualification and failure-response dataset" "first post-loss SNP I&C TechMat roster/handover"
maiwald = round19-progress "Frank W. Maiwald" "ValH+ source replay plus SI manifest" "promoted manifest/integrity/parse ladder from Zhang public-producer architecture" true "materialize and parse SI photodissociation-time/frequency/coordinate tables; bind measured intensity/calibration arrays" "raw/reduced spectra, notebooks and SURP custody"
reza = round19-progress "Monica Jacinto / Monica Reza" "finite alloy composition/burn-strength Pareto machinery" "retained; process-property replay pattern nominated for MONDALOY/enamel descendants" false "source-exact coating/enamel composition, process, oxygen-service qualification and uncertainty" "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custodian"
grillmair = round19-progress "Carl J. Grillmair" "executable matched-filter distance-scan machinery" "promoted Fly-style select/freeze/held-out discipline for source catalogue/filter/orbit replay" true "exact catalogue slice, colour-magnitude filter weights, distance grid, orbit inputs and uncertainty" "stream maps/catalogues/orbit fits or unfinished-manuscript custodian"
hicks = round19-progress "Michael David Hicks" "source-bound 3122 Florence photometry campaign" "retained; materialization ladder applies once raw lightcurve is located" false "raw time/magnitude/error series with viewing geometry and calibration" "campaign-data custodian plus 2022 JPL separation/handover"
mccasland = round19-progress "William Neil McCasland" "executable Gramian/failure-family placement engine" "promoted NDim/RSA requirement-closed finite-family replay over historical source parameters" true "published plant matrices, candidate sensor/actuator sites, failure family and benchmark placements" "dated DBE status and 2025-2026 client/programme carrier"
chavez = round19-progress "Anthony Chavez" "identity-gated DARHT/Scorpius engineering carrier" "identity gate retained; no cross-pollinated technical execution crosses same-person seam" false "same-person weld before exact Scorpius subsystem geometry/calibration replay" "primary same-person weld between missing-person and LANL identities"
thomas = round19-progress "Jason R. Thomas" "source assay/mechanism coordinates" "retained; source-data/materialization ladder applies to supporting-information matrices" false "per-well screen matrix, dose-response arrays and proteomics table" "lab/project/data successor plus final ME carrier"
amy = round19-progress "Amy Eskridge" "programme/mechanism-only carrier" "authorship gate retained; no executable mechanism promoted without Amy-authored/recorded object" false "Amy-authored/recorded equations, apparatus, deck or reviewed manuscript" "Amy-linked NF-1676/EDAA/STRIVES object and Institute handover"
ning = round19-progress "Ning Li" "source-exact static-versus-rotating YBCO comparison" "promoted query-indexed null-comparison discipline: negative observations remain configuration-bounded" true "later AC Gravity/Army apparatus geometry, calibration, controls, raw measurements and closeout" "FY2001 DoD row, Army SOW, closeout/result and apparatus custody"
chen = round19-progress "Chen Shuming" "finite graph-specification hardware-verification reconstruction" "retained; finite-replay pattern applies when exact graph/stimulus corpus is recovered" false "source graph semantics, stimulus corpus, coverage metric and mismatch example" "processor-specific responsibility and technical custodian"
feng = round19-progress "Feng Yanghe" "publisher-exact Bayesian/noisy-label classifier topology" "retained; held-out/freeze discipline nominated but numeric example data remain unpaid" false "book equations, example dataset, noise parameters and classifier outputs" "post-2023 War Skull code/project lead and primary event carrier"
zhou = round19-progress "Zhou Guangyuan" "numeric PI-D1/PI-A4 aerogel process-property replay" "promoted finite measurement plus materialization pattern into process -> structure -> property table route" true "complete multi-sample recipe, uncertainty, thermal curve and scale-up window" "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"
liu = round19-progress "Liu Donghao" "finite DSMM lifecycle/evidence carrier" "retained; requirement-closed evidence-set pattern nominated for one assessed example" false "maturity levels, scoring semantics, authored clauses and assessed evidence bundle" "dated Liu-to-Liao governance transition and project custody"
zhangXiaoxin = round19-progress "Zhang Xiaoxin" "public producer with execution-readiness/materialization state machine" "promoted as canonical manifest -> integrity -> parse -> dependency -> execute cross-domain pattern" true "obtain local Zenodo bytes; verify MD5; parse MAT/code; close dependencies; execute and compare event outputs" "dated NSMC/Fengyun successor and payload/ground-system custody"
zhangDaibing = round19-progress "Zhang Daibing" "DFC/PSO source architecture" "retained; requirement-closed disturbance/test family pattern nominated after vehicle equations are recovered" false "vehicle model, controller gains, disturbance PSDs and touchdown-dispersion series" "Yunzhihang/NUDT project and code custodian"
liMinyong = round19-progress "Li Minyong" "finite photopharmacology/probe carrier" "retained; process-state-readout replay pattern applies at exact compound level" false "one molecule/probe wavelength, state fraction, affinity/selectivity, dose and readout kinetics" "post-loss lab/project/patent/student custodian"
fang = round19-progress "Fang Daining" "source inverse-design objective with hidden numerical producer" "retained; source-producer ladder blocked until energy/geometry/band payload is located" false "complete energy functional, unit-cell geometry/constants, computed/experimental bands and solver" "post-loss BIT project/code/IP handover"
yan = round19-progress "Yan Hong" "source-exact four-case Mach-5 thermal full-text carrier" "retained; materialization pattern applies to response curves and CFD setup once extracted" false "mesh/boundaries, heat-source model, geometry and shock/separation curves" "named NPU flow-control project/code/data successor"

round19TwentyScientistProgress : List Round19Progress
round19TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷
  ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round19ScientificCohortCount : Nat
round19ScientificCohortCount = 20

round19CrossPollinationPromotionCount : Nat
round19CrossPollinationPromotionCount = 6

round19EveryScientistTouched : Bool
round19EveryScientistTouched = true

round19CrossPollinationCreatesHistoricalCollaboration : Bool
round19CrossPollinationCreatesHistoricalCollaboration = false

round19CrossPollinationCreatesCommonCause : Bool
round19CrossPollinationCreatesCommonCause = false

round19CrossPollinationPaysSourceReproduction : Bool
round19CrossPollinationPaysSourceReproduction = false
