module DASHI.Culture.MissingDeceasedTwentyScientistRound16PublicProducerProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round16Progress : Set where
  constructor round16-progress
  field
    person : String
    scienceState : String
    round16Delta : String
    publicProducerPromoted : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round16Progress public

nuno = round16-progress "Nuno F. G. Loureiro" "KREHM/Hermite/plasmoid execution machinery" "retained" false "Viriato benchmark IC/closure/discretisation/output" "repo/grant/simulation-state successor"
leblanc = round16-progress "Joshua Kyle LeBlanc" "FSP I&C source envelope" "retained" false "named device qualification/calibration/failure row" "post-loss TechMat roster/handover"
maiwald = round16-progress "Frank W. Maiwald" "ValH+ source replay plus SI manifest" "retained; SI now finite acquisition object" false "parse SI photodissociation-time/frequency/coordinate tables; recover raw measured intensity/calibration arrays" "raw/reduced spectra/notebooks/SURP custody"
reza = round16-progress "Monica Jacinto / Monica Reza" "alloy burn-strength Pareto" "retained" false "MONDALOY/enamel descendant process/qualification data" "assignment/process-window custody"
grillmair = round16-progress "Carl J. Grillmair" "matched-filter executable stream inference" "retained" false "exact catalogue/filter/orbit uncertainty replay" "stream data/manuscript custodian"
hicks = round16-progress "Michael David Hicks" "3122 Florence campaign carrier" "retained" false "raw lightcurve/geometry/calibration" "campaign/JPL handover custody"
mccasland = round16-progress "William Neil McCasland" "Gramian/failure-family executable placement" "retained" false "historical plant matrices/candidate locations/failure family" "DBE client/programme carrier"
chavez = round16-progress "Anthony Chavez" "identity-gated DARHT/Scorpius carrier" "gate retained" false "same-person weld before subsystem replay" "primary identity weld"
thomas = round16-progress "Jason R. Thomas" "source assay/mechanism coordinates" "retained" false "per-well matrix/dose-response/proteomics table" "lab/project/data successor; ME carrier"
amy = round16-progress "Amy Eskridge" "programme/mechanism-only carrier" "authorship gate retained" false "Amy-authored/recorded equations/apparatus/deck/manuscript" "NF-1676/EDAA/STRIVES + Institute handover"
ning = round16-progress "Ning Li" "source numeric static/rotating YBCO comparison" "retained" false "later AC Gravity/Army apparatus geometry/calibration/control/result table" "FY2001 row/SOW/closeout/apparatus custody"
chen = round16-progress "Chen Shuming" "graph-spec hardware verification finite carrier" "retained" false "source graph/stimulus/coverage/mismatch example" "processor technical custodian"
feng = round16-progress "Feng Yanghe" "publisher-exact classifier topology" "retained" false "book equations/example data/noise parameters/outputs" "War Skull code/project successor"
zhou = round16-progress "Zhou Guangyuan" "numeric PI-D1/PI-A4 process-property replay" "retained" false "complete multi-sample table/recipe/uncertainty" "patent/process/enterprise custody"
liu = round16-progress "Liu Donghao" "DSMM lifecycle/maturity carrier" "retained" false "authored rubric/levels/scoring/assessed example" "dated Liu-to-Liao transition/project custody"
zhangXiaoxin = round16-progress "Zhang Xiaoxin" "229-event forecast replay" "promoted from hidden producer to public producer: publisher-linked Data Set S1, processed-data DOI, code DOI, exact MAT file names/sizes/MD5, 30-min Oulu carrier, 1.2x threshold and 50.4 h mean lead time" true "download and parse MAT payloads; inspect exact code manifest; execute producer and compare event-level outputs" "NSMC/Fengyun successor/data custody"
zhangDaibing = round16-progress "Zhang Daibing" "DFC/PSO source architecture" "retained" false "vehicle model/gains/disturbance PSD/touchdown series" "Yunzhihang/NUDT code/project custodian"
liMinyong = round16-progress "Li Minyong" "photopharmacology/probe finite carrier" "retained" false "exact molecule/wavelength/state fraction/affinity/dose/kinetics" "lab/project/patent/student custodian"
fang = round16-progress "Fang Daining" "inverse-design source objective with numerical producer debt" "retained" false "energy functional/unit-cell geometry/constants/band arrays/code" "BIT project/code/IP handover"
yan = round16-progress "Yan Hong" "four-case Mach-5 full-text producer surface" "retained" false "response curves/geometry/heat model/mesh/boundaries" "NPU project/code/data successor"

round16TwentyScientistProgress : List Round16Progress
round16TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷
  ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round16ScientificCohortCount : Nat
round16ScientificCohortCount = 20

round16PublicProducerPromotionCount : Nat
round16PublicProducerPromotionCount = 1

round16EveryScientistTouched : Bool
round16EveryScientistTouched = true

publicProducerProgressPaysExecution : Bool
publicProducerProgressPaysExecution = false

publicProducerProgressPaysHistoricalDeployment : Bool
publicProducerProgressPaysHistoricalDeployment = false

publicProducerProgressPaysCustody : Bool
publicProducerProgressPaysCustody = false
