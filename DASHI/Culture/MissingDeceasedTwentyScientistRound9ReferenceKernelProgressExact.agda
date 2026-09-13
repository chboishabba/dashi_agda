module DASHI.Culture.MissingDeceasedTwentyScientistRound9ReferenceKernelProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round9ScientistProgress : Set where
  constructor round9-scientist-progress
  field
    person : String
    currentScienceKernel : String
    round9Delta : String
    referenceKernelPromoted : Bool
    nextExecutableLeaf : String
    nextCustodyLeaf : String

open Round9ScientistProgress public

nuno = round9-scientist-progress "Nuno F. G. Loureiro" "finite KREHM/Hermite/plasmoid machinery" "retained; source-exact Viriato benchmark/runtime remains next" false "bind one published benchmark initial condition, closure, discretisation and output to executable Viriato owner" "repository maintainer, grant reassignment and simulation-state custodian"
leblanc = round9-scientist-progress "Joshua Kyle LeBlanc" "source-exact FSP I&C finite envelope" "retained; device-level qualification kernel remains next" false "one named sensor/device qualification-calibration-failure replay" "first real post-loss SNP I&C TechMat roster and handover"
maiwald = round9-scientist-progress "Frank W. Maiwald" "source replay over ValH+ spectrum anchors" "promoted to executable tag-temperature/spectral-anchor reference subkernel" true "replace source anchors with raw intensity/calibration/dissociation arrays for measured-spectrum replay" "raw/reduced spectra, calibration files, notebooks and SURP handover"
reza = round9-scientist-progress "Monica Jacinto / Monica Reza" "finite alloy burn/strength Pareto machinery" "retained; descendant coating/enamel reference kernel remains next" false "source-exact MONDALOY/enamel composition-process-operating-window replay" "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custodian"
grillmair = round9-scientist-progress "Carl J. Grillmair" "executable matched-filter distance-scan machinery" "retained; source catalogue/orbit reference replay remains next" false "one source stream slice with colour-magnitude filter, distance scan and orbit-fit uncertainty" "stream maps/catalogues/orbit fits or unfinished-manuscript custodian"
hicks = round9-scientist-progress "Michael David Hicks" "finite small-body photometry mechanism" "retained; source observation series remains next reference kernel" false "one exact lightcurve with timestamps, calibrated magnitudes/errors, geometry and period inference" "2022 JPL separation and unfinished observing/reduction/data handover"
mccasland = round9-scientist-progress "William Neil McCasland" "executable Gramian/failure-family engine" "retained; historical source-parameter weld remains next" false "bind published beam/plant matrices, candidate locations and failure family to executable engine" "dated DBE status and 2025-2026 client/programme carrier"
chavez = round9-scientist-progress "Anthony Chavez" "identity-gated DARHT/Scorpius science carrier" "identity gate retained; no runtime inheritance promoted" false "after same-person weld, recover exact Scorpius subsystem geometry/calibration/design responsibility" "primary same-person weld between missing-person and LANL engineering identities"
thomas = round9-scientist-progress "Jason R. Thomas" "finite signalling/target-deconvolution witness" "retained; source assay reference kernel remains next" false "one Thomas-authored assay with perturbation/readout counts and direct-target validation" "lab/project/data successor plus final ME carrier"
amy = round9-scientist-progress "Amy Eskridge" "programme/mechanism-only; technical authorship unresolved" "authorship gate retained; no executable technical kernel manufactured" false "recover Amy-authored/recorded equations, apparatus, deck or reviewed technical manuscript" "Amy-linked NF-1676/EDAA/STRIVES object and Institute derivative/handover"
ning = round9-scientist-progress "Ning Li" "source-exact static-versus-rotating apparatus comparison" "retained; later-apparatus reference kernel remains next" false "source-exact AC Gravity/NASA/Army apparatus geometry, drive, calibration and controls comparison" "FY2001 DoD row, Army SOW, closeout/result and apparatus custody"
chen = round9-scientist-progress "Chen Shuming" "finite graph-spec hardware-verification reconstruction" "retained; source graph/stimulus/coverage replay remains next" false "recover exact graph semantics, stimulus corpus, coverage metric and mismatch example" "processor-specific responsibility and post-loss technical custodian"
feng = round9-scientist-progress "Feng Yanghe" "finite Bayesian/noisy-label classifier reconstruction" "retained; source model/example replay remains next" false "replay one NUDT Press classifier example with assumptions, noise parameters and outputs" "post-2023 War Skull code/project lead and primary event carrier"
zhou = round9-scientist-progress "Zhou Guangyuan" "source-exact SI thermal datum plus finite aerogel witness" "retained; multi-sample structure-property reference kernel remains next" false "recover sample table linking synthesis, shrinkage, porosity, surface area, temperature and conductivity" "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"
liu = round9-scientist-progress "Liu Donghao" "finite DSMM lifecycle/evidence reconstruction" "retained; authored rubric/scoring reference kernel remains next" false "recover maturity levels, scoring semantics, authored clauses and one assessed example" "dated Liu-to-Liao governance transition and project custody"
zhangXiaoxin = round9-scientist-progress "Zhang Xiaoxin" "source-exact forecast replay coordinates" "promoted to executable aggregate source-coordinate projection" true "recover whitening/CEEMDAN/CWT hyperparameters, precursor rule and event-level inputs/outputs" "dated NSMC/Fengyun successor and payload/ground-system custody"
zhangDaibing = round9-scientist-progress "Zhang Daibing" "finite UAV guidance/control reconstruction" "retained; one source paper reference kernel remains next" false "recover one paper's state equations, control law, gains, sensor model, geometry and error series" "Yunzhihang/NUDT project and code custodian"
liMinyong = round9-scientist-progress "Li Minyong" "finite photoswitch/probe reconstruction" "retained; compound-specific reference kernel remains next" false "recover one molecule/probe wavelength, state fraction, affinity/selectivity, dose and readout kinetics" "post-loss lab/project/patent/student custodian"
fang = round9-scientist-progress "Fang Daining" "source-exact inverse-design objective/validation replay" "promoted to reference projection but solver remains blocked on hidden producer" true "recover complete energy functional, unit-cell geometry, constants and band arrays" "post-loss BIT project/code/IP handover"
yan = round9-scientist-progress "Yan Hong" "source-exact four-case Mach-5 thermal replay" "promoted to executable source-case selector and qualitative-response reference kernel" true "recover geometry, mesh/boundaries, heat-source model and shock/separation curves" "named NPU flow-control project/code/data successor"

round9TwentyScientistProgress : List Round9ScientistProgress
round9TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round9ScientificCohortCount : Nat
round9ScientificCohortCount = 20

round9ReferenceKernelPromotionCount : Nat
round9ReferenceKernelPromotionCount = 4

round9EveryScientistTouched : Bool
round9EveryScientistTouched = true

referenceKernelPromotionPaysSourceAlgorithm : Bool
referenceKernelPromotionPaysSourceAlgorithm = false

referenceKernelPromotionPaysHistoricalDeployment : Bool
referenceKernelPromotionPaysHistoricalDeployment = false

referenceKernelPromotionPaysEventCause : Bool
referenceKernelPromotionPaysEventCause = false
