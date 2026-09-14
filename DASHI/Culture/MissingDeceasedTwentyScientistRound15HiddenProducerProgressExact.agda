module DASHI.Culture.MissingDeceasedTwentyScientistRound15HiddenProducerProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round15ScientistProgress : Set where
  constructor round15-progress
  field
    person : String
    scienceState : String
    round15Delta : String
    hiddenProducerPromoted : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round15ScientistProgress public

nuno = round15-progress "Nuno F. G. Loureiro" "KREHM/Hermite/plasmoid execution machinery" "retained" false "source-exact Viriato benchmark initial condition/closure/discretisation/output" "repo/grant/simulation-state successor"
leblanc = round15-progress "Joshua Kyle LeBlanc" "FSP I&C source envelope" "retained" false "named device qualification/calibration/failure row" "post-loss TechMat roster/handover"
maiwald = round15-progress "Frank W. Maiwald" "ValH+ source replay" "promoted free SI manifest: five figures, four tables, dissociation times, coordinates, vibrational frequencies" true "parse SI tables/photodissociation times; recover raw measured spectrum and calibration" "raw/reduced spectra, notebooks, SURP custody"
reza = round15-progress "Monica Jacinto / Monica Reza" "alloy burn-strength Pareto" "retained" false "MONDALOY/enamel descendant composition/process/qualification data" "assignment/process-window custody"
grillmair = round15-progress "Carl J. Grillmair" "matched-filter executable stream inference" "retained" false "exact catalogue/filter/orbit uncertainty replay" "stream data/manuscript custodian"
hicks = round15-progress "Michael David Hicks" "3122 Florence source campaign carrier" "retained after round14 bounded promotion" false "raw lightcurve with geometry/calibration" "campaign/JPL handover custody"
mccasland = round15-progress "William Neil McCasland" "Gramian/failure-family executable placement" "retained" false "historical plant matrices/candidate locations/failure family" "DBE client/programme carrier"
chavez = round15-progress "Anthony Chavez" "identity-gated DARHT/Scorpius carrier" "gate retained" false "same-person weld before subsystem replay" "primary identity weld"
thomas = round15-progress "Jason R. Thomas" "source assay/mechanism coordinates" "retained after round14 bounded promotion" false "per-well matrix, dose-response arrays, proteomics table" "lab/project/data successor; ME carrier"
amy = round15-progress "Amy Eskridge" "programme/mechanism-only carrier" "authorship gate retained" false "Amy-authored/recorded equations/apparatus/deck/manuscript" "NF-1676/EDAA/STRIVES + Institute handover"
ning = round15-progress "Ning Li" "source numeric static/rotating YBCO comparison" "retained after round14 numeric promotion" false "later AC Gravity/Army apparatus geometry/calibration/control/result table" "FY2001 row/SOW/closeout/apparatus custody"
chen = round15-progress "Chen Shuming" "graph-spec hardware verification finite carrier" "retained" false "source graph/stimulus/coverage/mismatch example" "processor technical custodian"
feng = round15-progress "Feng Yanghe" "publisher-exact classifier topology" "retained after round14 bounded promotion" false "book equations, example data, noise parameters, outputs" "War Skull code/project successor"
zhou = round15-progress "Zhou Guangyuan" "numeric PI-D1/PI-A4 process-property replay" "retained after round14 numeric promotion" false "complete multi-sample table, recipe and uncertainty" "patent/process/enterprise custody"
liu = round15-progress "Liu Donghao" "DSMM lifecycle/maturity carrier" "retained" false "authored rubric, levels, scoring, assessed example" "dated Liu-to-Liao transition/project custody"
zhangXiaoxin = round15-progress "Zhang Xiaoxin" "229-event forecast source replay" "promoted algorithm-producer depth: public SWM/CEEMDAN/CWT equations visible, row-level data/hyperparameters still missing" true "event rows + exact hyperparameters + precursor quantisation + code" "NSMC/Fengyun successor/data custody"
zhangDaibing = round15-progress "Zhang Daibing" "DFC/PSO source architecture" "retained after round14 bounded promotion" false "vehicle model, gains, disturbance PSDs, touchdown series" "Yunzhihang/NUDT code/project custodian"
liMinyong = round15-progress "Li Minyong" "photopharmacology/probe finite carrier" "retained" false "exact molecule/probe wavelength/state fraction/affinity/dose/kinetics" "lab/project/patent/student custodian"
fang = round15-progress "Fang Daining" "inverse-design source objective" "promoted explicit hidden-producer debt; solver remains blocked" true "energy functional, unit-cell geometry, constants, computed/experimental bands" "BIT project/code/IP handover"
yan = round15-progress "Yan Hong" "four-case Mach-5 thermal source replay" "promoted full-text producer-depth: article/method/cases visible, response arrays/mesh/boundaries still missing" true "response curves + geometry + heat model + mesh/boundaries" "NPU project/code/data successor"

round15TwentyScientistProgress : List Round15ScientistProgress
round15TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷
  ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round15ScientificCohortCount : Nat
round15ScientificCohortCount = 20

round15HiddenProducerPromotionCount : Nat
round15HiddenProducerPromotionCount = 4

round15EveryScientistTouched : Bool
round15EveryScientistTouched = true

hiddenProducerProgressPaysHistoricalDeployment : Bool
hiddenProducerProgressPaysHistoricalDeployment = false

hiddenProducerProgressPaysCustody : Bool
hiddenProducerProgressPaysCustody = false

hiddenProducerProgressPaysCommonProgramme : Bool
hiddenProducerProgressPaysCommonProgramme = false
