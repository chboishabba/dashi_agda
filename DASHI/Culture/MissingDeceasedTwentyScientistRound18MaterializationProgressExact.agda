module DASHI.Culture.MissingDeceasedTwentyScientistRound18MaterializationProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round18Progress : Set where
  constructor round18-progress
  field
    person : String
    scienceState : String
    round18Delta : String
    materializationPromoted : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round18Progress public

nuno = round18-progress "Nuno F. G. Loureiro" "KREHM/Hermite/plasmoid execution machinery" "retained" false "materialize one source-exact Viriato benchmark and execute" "repo/grant/simulation-state successor"
leblanc = round18-progress "Joshua Kyle LeBlanc" "FSP I&C source envelope" "retained" false "materialize one named device qualification/calibration/failure record" "post-loss TechMat roster/handover"
maiwald = round18-progress "Frank W. Maiwald" "ValH+ replay plus SI manifest" "retained; SI package remains next materialization candidate" false "materialize/parse SI tables and photodissociation-time/frequency/coordinate payload" "raw/reduced spectra/notebooks/SURP custody"
reza = round18-progress "Monica Jacinto / Monica Reza" "alloy burn-strength Pareto" "retained" false "materialize descendant MONDALOY/enamel process/qualification dataset" "assignment/process-window custody"
grillmair = round18-progress "Carl J. Grillmair" "matched-filter executable stream inference" "retained" false "materialize exact stream catalogue/filter/orbit slice" "stream data/manuscript custodian"
hicks = round18-progress "Michael David Hicks" "3122 Florence campaign carrier" "retained" false "materialize raw lightcurve/geometry/calibration" "campaign/JPL handover custody"
mccasland = round18-progress "William Neil McCasland" "Gramian/failure-family executable placement" "retained" false "materialize historical plant matrices/candidate/failure family" "DBE client/programme carrier"
chavez = round18-progress "Anthony Chavez" "identity-gated DARHT/Scorpius carrier" "identity gate retained" false "same-person weld before materializing technical payload" "primary identity weld"
thomas = round18-progress "Jason R. Thomas" "source assay/mechanism coordinates" "retained" false "materialize per-well/dose-response/proteomics payload" "lab/project/data successor; ME carrier"
amy = round18-progress "Amy Eskridge" "programme/mechanism-only carrier" "authorship gate retained" false "recover Amy-authored/recorded technical object before materialization" "NF-1676/EDAA/STRIVES + Institute handover"
ning = round18-progress "Ning Li" "source numeric static/rotating YBCO comparison" "retained" false "materialize later AC Gravity/Army apparatus/calibration/control/result records" "FY2001 row/SOW/closeout/apparatus custody"
chen = round18-progress "Chen Shuming" "graph-spec hardware verification finite carrier" "retained" false "materialize graph/stimulus/coverage/mismatch example" "processor technical custodian"
feng = round18-progress "Feng Yanghe" "publisher-exact classifier topology" "retained" false "materialize book equations/example data/noise/output replay" "War Skull code/project successor"
zhou = round18-progress "Zhou Guangyuan" "numeric PI-D1/PI-A4 process-property replay" "retained" false "materialize complete multi-sample process/property table" "patent/process/enterprise custody"
liu = round18-progress "Liu Donghao" "DSMM lifecycle/maturity carrier" "retained" false "materialize authored scoring rubric and assessed example" "dated Liu-to-Liao transition/project custody"
zhangXiaoxin = round18-progress "Zhang Xiaoxin" "public producer execution-readiness manifest" "promoted explicit remote-manifest-only materialization state; no local bytes/hash verification/parsing/execution claimed" true "obtain local Zenodo data/code bytes; verify MD5; parse MAT/code; close dependencies; execute and compare" "NSMC/Fengyun successor/data custody"
zhangDaibing = round18-progress "Zhang Daibing" "DFC/PSO source architecture" "retained" false "materialize vehicle model/gains/disturbance/touchdown data" "Yunzhihang/NUDT code/project custodian"
liMinyong = round18-progress "Li Minyong" "photopharmacology/probe finite carrier" "retained" false "materialize compound/wavelength/state/affinity/dose/kinetics data" "lab/project/patent/student custodian"
fang = round18-progress "Fang Daining" "inverse-design objective with hidden numerical producer" "retained; materialization blocked by missing producer" false "energy functional/unit-cell/constants/bands/code" "BIT project/code/IP handover"
yan = round18-progress "Yan Hong" "four-case Mach-5 full-text producer" "retained" false "materialize response arrays/geometry/heat model/mesh" "NPU project/code/data successor"

round18TwentyScientistProgress : List Round18Progress
round18TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷
  ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round18ScientificCohortCount : Nat
round18ScientificCohortCount = 20

round18MaterializationPromotionCount : Nat
round18MaterializationPromotionCount = 1

round18EveryScientistTouched : Bool
round18EveryScientistTouched = true

materializationDoesNotPayExecution : Bool
materializationDoesNotPayExecution = false

materializationDoesNotPayHistoricalDeployment : Bool
materializationDoesNotPayHistoricalDeployment = false

materializationDoesNotPayCustody : Bool
materializationDoesNotPayCustody = false
