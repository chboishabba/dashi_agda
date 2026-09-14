module DASHI.Culture.MissingDeceasedTwentyScientistRound17ProducerExecutionProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round17Progress : Set where
  constructor round17-progress
  field
    person : String
    scienceExecutionState : String
    round17Delta : String
    executionReadinessPromoted : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round17Progress public

nuno = round17-progress "Nuno F. G. Loureiro" "finite/executable KREHM-Hermite-plasmoid machinery" "retained" false "source-exact Viriato benchmark execution" "repo/grant/simulation-state successor"
leblanc = round17-progress "Joshua Kyle LeBlanc" "source-exact FSP I&C envelope" "retained" false "named device qualification/calibration/failure execution row" "post-loss TechMat roster/handover"
maiwald = round17-progress "Frank W. Maiwald" "source replay + SI manifest" "retained; SI parsing remains higher priority than synthetic execution" false "parse photodissociation-time/frequency/coordinate SI and measured intensity/calibration payload" "raw/reduced spectra/notebooks/SURP custody"
reza = round17-progress "Monica Jacinto / Monica Reza" "finite alloy burn-strength Pareto" "retained" false "MONDALOY/enamel descendant process/qualification replay" "assignment/process-window custody"
grillmair = round17-progress "Carl J. Grillmair" "matched-filter executable stream inference" "retained" false "source catalogue/filter/orbit uncertainty execution" "stream data/manuscript custodian"
hicks = round17-progress "Michael David Hicks" "3122 Florence source campaign carrier" "retained" false "raw lightcurve/geometry/calibration execution" "campaign/JPL handover custody"
mccasland = round17-progress "William Neil McCasland" "Gramian/failure-family executable placement" "retained" false "historical plant matrices/candidate/failure replay" "DBE client/programme carrier"
chavez = round17-progress "Anthony Chavez" "identity-gated DARHT/Scorpius carrier" "identity gate retained" false "same-person weld before technical execution" "primary identity weld"
thomas = round17-progress "Jason R. Thomas" "source assay/mechanism coordinates" "retained" false "per-well/dose-response/proteomics execution carrier" "lab/project/data successor; ME carrier"
amy = round17-progress "Amy Eskridge" "programme/mechanism-only carrier" "authorship gate retained" false "Amy-authored/recorded technical object before execution" "NF-1676/EDAA/STRIVES + Institute handover"
ning = round17-progress "Ning Li" "source numeric static/rotating YBCO comparison" "retained" false "later AC Gravity/Army apparatus/calibration/control/result execution" "FY2001 row/SOW/closeout/apparatus custody"
chen = round17-progress "Chen Shuming" "finite graph-spec hardware verification" "retained" false "source graph/stimulus/coverage/mismatch execution" "processor technical custodian"
feng = round17-progress "Feng Yanghe" "publisher-exact classifier topology" "retained" false "book equations/example data/noise/output replay" "War Skull code/project successor"
zhou = round17-progress "Zhou Guangyuan" "numeric PI-D1/PI-A4 process-property replay" "retained" false "complete multi-sample process-property execution table" "patent/process/enterprise custody"
liu = round17-progress "Liu Donghao" "DSMM lifecycle/maturity carrier" "retained" false "authored scoring rubric + assessed example execution" "dated Liu-to-Liao transition/project custody"
zhangXiaoxin = round17-progress "Zhang Xiaoxin" "public data/code producer located" "promoted to explicit execution-readiness manifest; no payload parse or rerun claimed" true "download deposits; verify hashes; parse MAT schemas; inspect code/dependencies; rerun and compare event outputs" "NSMC/Fengyun successor/data custody"
zhangDaibing = round17-progress "Zhang Daibing" "DFC/PSO source architecture" "retained" false "vehicle model/gains/disturbance/touchdown execution" "Yunzhihang/NUDT code/project custodian"
liMinyong = round17-progress "Li Minyong" "photopharmacology/probe finite carrier" "retained" false "compound/wavelength/state/affinity/dose/kinetics replay" "lab/project/patent/student custodian"
fang = round17-progress "Fang Daining" "inverse-design objective with hidden numerical producer" "retained; execution blocked" false "energy functional/unit-cell/constants/bands/code" "BIT project/code/IP handover"
yan = round17-progress "Yan Hong" "four-case Mach-5 full-text producer" "retained" false "response arrays/geometry/heat model/mesh execution" "NPU project/code/data successor"

round17TwentyScientistProgress : List Round17Progress
round17TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷
  ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round17ScientificCohortCount : Nat
round17ScientificCohortCount = 20

round17ExecutionReadinessPromotionCount : Nat
round17ExecutionReadinessPromotionCount = 1

round17EveryScientistTouched : Bool
round17EveryScientistTouched = true

executionReadinessPaysExecution : Bool
executionReadinessPaysExecution = false

executionReadinessPaysHistoricalDeployment : Bool
executionReadinessPaysHistoricalDeployment = false

executionReadinessPaysCustody : Bool
executionReadinessPaysCustody = false
