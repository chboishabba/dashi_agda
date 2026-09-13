module DASHI.Culture.MissingDeceasedTwentyScientistRound13ReferenceKernelProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round13ScientistProgress : Set where
  constructor round13-scientist-progress
  field
    person : String
    currentScienceKernel : String
    round13Delta : String
    referenceKernelPromoted : Bool
    nextExecutableLeaf : String
    nextCustodyLeaf : String

open Round13ScientistProgress public

nuno = round13-scientist-progress "Nuno F. G. Loureiro" "finite KREHM/Hermite/plasmoid machinery" "retained; source-exact Viriato benchmark/runtime remains next" false "bind one published benchmark initial condition, closure, discretisation and output to executable Viriato owner" "repository maintainer, grant reassignment and simulation-state custodian"
leblanc = round13-scientist-progress "Joshua Kyle LeBlanc" "source-exact FSP I&C finite envelope" "retained; device-level qualification kernel remains next" false "one named sensor/device qualification-calibration-failure replay" "first real post-loss SNP I&C TechMat roster and handover"
maiwald = round13-scientist-progress "Frank W. Maiwald" "source replay over ValH+ spectral anchors" "added executable tag-temperature/spectral-anchor reference subkernel" true "replace source anchors with raw intensity/calibration/dissociation arrays for measured-spectrum replay" "raw/reduced spectra, calibration files, notebooks and SURP handover"
reza = round13-scientist-progress "Monica Jacinto / Monica Reza" "finite alloy burn/strength Pareto machinery" "retained; descendant coating/enamel reference kernel remains next" false "source-exact MONDALOY/enamel composition-process-operating-window replay" "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custodian"
grillmair = round13-scientist-progress "Carl J. Grillmair" "executable matched-filter distance-scan machinery" "retained; source catalogue/orbit reference replay remains next" false "one source stream slice with colour-magnitude filter, distance scan and orbit-fit uncertainty" "stream maps/catalogues/orbit fits or unfinished-manuscript custodian"
hicks = round13-scientist-progress "Michael David Hicks" "source-bound small-body photometry carrier" "retained; exact observation series remains next reference kernel" false "one exact lightcurve with timestamps, calibrated magnitudes/errors, geometry and period inference" "2022 JPL separation and unfinished observing/reduction/data handover"
mccasland = round13-scientist-progress "William Neil McCasland" "executable Gramian/failure-family engine" "retained; historical source-parameter weld remains next" false "bind published beam/plant matrices, candidate locations and failure family to executable engine" "dated DBE status and 2025-2026 client/programme carrier"
chavez = round13-scientist-progress "Anthony Chavez" "identity-gated DARHT/Scorpius science carrier" "identity gate retained; no runtime inheritance promoted" false "after same-person weld, recover exact Scorpius subsystem geometry/calibration/design responsibility" "primary same-person weld between missing-person and LANL engineering identities"
thomas = round13-scientist-progress "Jason R. Thomas" "finite signalling/target-deconvolution witness" "retained; source assay reference kernel remains next" false "one Thomas-authored assay with perturbation/readout counts and direct-target validation" "lab/project/data successor plus final ME carrier"
amy = round13-scientist-progress "Amy Eskridge" "programme/mechanism-only; technical authorship unresolved" "authorship gate retained; no executable technical kernel manufactured" false "recover Amy-authored/recorded equations, apparatus, deck or reviewed technical manuscript" "Amy-linked NF-1676/EDAA/STRIVES object and Institute derivative/handover"
ning = round13-scientist-progress "Ning Li" "source-exact static-versus-rotating apparatus comparison" "retained; later-apparatus reference kernel remains next" false "source-exact AC Gravity/NASA/Army apparatus geometry, drive, calibration and controls comparison" "FY2001 DoD row, Army SOW, closeout/result and apparatus custody"
chen = round13-scientist-progress "Chen Shuming" "finite graph-spec hardware-verification reconstruction" "retained; source graph/stimulus/coverage replay remains next" false "recover exact graph semantics, stimulus corpus, coverage metric and mismatch example" "processor-specific responsibility and post-loss technical custodian"
feng = round13-scientist-progress "Feng Yanghe" "finite Bayesian/noisy-label classifier reconstruction" "retained; source model/example replay remains next" false "replay one NUDT Press classifier example with assumptions, noise parameters and outputs" "post-2023 War Skull code/project lead and primary event carrier"
zhou = round13-scientist-progress "Zhou Guangyuan" "source-exact SI thermal datum plus finite aerogel witness" "retained; multi-sample structure-property reference kernel remains next" false "recover sample table linking synthesis, shrinkage, porosity, surface area, temperature and conductivity" "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"
liu = round13-scientist-progress "Liu Donghao" "finite DSMM lifecycle/evidence reconstruction" "retained; authored rubric/scoring reference kernel remains next" false "recover maturity levels, scoring semantics, authored clauses and one assessed example" "dated Liu-to-Liao governance transition and project custody"
zhangXiaoxin = round13-scientist-progress "Zhang Xiaoxin" "source-exact 229-event forecast replay" "added executable aggregate source-coordinate projection" true "recover whitening/CEEMDAN/CWT hyperparameters, precursor rule and event-level inputs/outputs" "dated NSMC/Fengyun successor and payload/ground-system custody"
zhangDaibing = round13-scientist-progress "Zhang Daibing" "finite UAV guidance/control reconstruction" "retained; one source paper reference kernel remains next" false "recover one paper's state equations, control law, gains, sensor model, geometry and error series" "Yunzhihang/NUDT project and code custodian"
liMinyong = round13-scientist-progress "Li Minyong" "finite photoswitch/probe reconstruction" "retained; compound-specific reference kernel remains next" false "recover one molecule/probe wavelength, state fraction, affinity/selectivity, dose and readout kinetics" "post-loss lab/project/patent/student custodian"
fang = round13-scientist-progress "Fang Daining" "source-exact inverse-design objective/validation replay" "added source-objective reference projection while solver remains blocked on hidden producer" true "recover complete energy functional, unit-cell geometry, constants and band arrays" "post-loss BIT project/code/IP handover"
yan = round13-scientist-progress "Yan Hong" "source-exact four-case Mach-5 thermal replay" "added executable source-case selector and qualitative-response reference kernel" true "recover geometry, mesh/boundaries, heat-source model and shock/separation curves" "named NPU flow-control project/code/data successor"

round13TwentyScientistProgress : List Round13ScientistProgress
round13TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round13ScientificCohortCount : Nat
round13ScientificCohortCount = 20

round13ReferenceKernelPromotionCount : Nat
round13ReferenceKernelPromotionCount = 4

round13EveryScientistTouched : Bool
round13EveryScientistTouched = true

referenceKernelPromotionPaysSourceAlgorithm : Bool
referenceKernelPromotionPaysSourceAlgorithm = false

referenceKernelPromotionPaysHistoricalDeployment : Bool
referenceKernelPromotionPaysHistoricalDeployment = false

referenceKernelPromotionPaysEventCause : Bool
referenceKernelPromotionPaysEventCause = false
