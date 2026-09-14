module DASHI.Culture.MissingDeceasedTwentyScientistRound19MissingObjectCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round19MissingObjectCoverage : Set where
  constructor round19-missing-object-coverage
  field
    person : String
    strongestRealObjectClass : String
    fitClass : String
    coverageDelta : String
    nextTechnicalLeaf : String
    nextHistoricalLeaf : String

open Round19MissingObjectCoverage public

nuno = round19-missing-object-coverage "Nuno F. G. Loureiro" "space/high-energy plasma-rich research object" "methodTransfer" "plasma/reconnection fibre retained without forcing propulsion identity" "source one exact plasma-rich apparatus/mission geometry" "literal shared facility/work-package receipt only"
leblanc = round19-missing-object-coverage "Joshua Kyle LeBlanc" "space/fission research platform" "directSourceFit" "FSP I&C remains direct ordinary-engineering fit" "exact I&C qualification/failure matrix" "post-loss same-work-package roster"
maiwald = round19-missing-object-coverage "Frank W. Maiwald" "molecular/high-energy diagnostics platform" "directSourceFit" "action spectroscopy retains direct diagnostic role" "raw spectrum/calibration replay" "JPL instrument/work-package identity"
reza = round19-missing-object-coverage "Monica Jacinto / Monica Reza" "rocket/oxidising-hot-section materials object" "directSourceFit" "oxygen-service alloy remains direct booster/material fit" "component/process qualification window" "pre-2013 AFRL Mondaloy programme receipt"
grillmair = round19-missing-object-coverage "Carl J. Grillmair" "wide-field astronomical survey / stellar-stream platform" "directSourceFit" "new real-object class removes prior analogy-only status" "catalogue/filter/orbit/uncertainty replay" "exact survey/work-package/custody receipt"
hicks = round19-missing-object-coverage "Michael David Hicks" "planetary small-body observatory / survey platform" "directSourceFit" "new real-object class removes prior analogy-only status" "raw lightcurve/geometry/calibration replay" "exact campaign/project/custody receipt"
mccasland = round19-missing-object-coverage "William Neil McCasland" "space/vehicle/high-energy control object" "methodTransfer" "fault-tolerant placement remains reusable method fit" "exact plant/failure-family finite replay" "named programme review/tasking receipt"
chavez = round19-missing-object-coverage "Anthony Chavez" "high-energy experimental facility" "directSourceFit identity-gated" "technical object fit retained behind identity gate" "same-person weld plus exact DARHT/Scorpius subsystem" "shared programme search only after identity"
thomas = round19-missing-object-coverage "Jason R. Thomas" "molecular-biology research platform" "directSourceFit" "assay/signalling subsystem remains direct" "supporting-information matrix" "lab/project succession receipt"
amy = round19-missing-object-coverage "Amy Eskridge" "precision/null-test research facility" "analogyOnly programme-gated" "mechanism-discrimination role retained without invented apparatus authorship" "Amy-authored/recorded technical object" "shared AC Gravity/Army object only on literal receipt"
ning = round19-missing-object-coverage "Ning Li" "precision-force / superconducting-gravity test facility" "directSourceFit" "static/rotating YBCO tests remain direct benign test-object fit" "later apparatus plus Army SOW/closeout" "enumerate DAAH01-01-9-R001 people/facilities"
chen = round19-missing-object-coverage "Chen Shuming" "digital control/hardware-verification research object" "methodTransfer" "verification fibre remains reusable across multiple real objects" "exact graph/spec/stimulus/coverage replay" "exact NUDT task/project identifier"
feng = round19-missing-object-coverage "Feng Yanghe" "robust classification / decision-support research platform" "directSourceFit" "new real-object class removes prior analogy-only status without asserting War Skull same-object identity" "equations/priors/example data/metrics" "literal War Skull task/code same-object receipt"
zhou = round19-missing-object-coverage "Zhou Guangyuan" "extreme-environment thermal-material object" "engineeringTransfer" "aerogel thermal-management fit retained" "complete process/property/qualification table" "DNL2200 grant/patent/transfer identifiers"
liu = round19-missing-object-coverage "Liu Donghao" "research-data governance across real platforms" "methodTransfer" "DSMM remains governance method rather than physical subsystem" "exact maturity rubric and lifecycle instantiation" "dated national project/company identifiers"
zhangXiaoxin = round19-missing-object-coverage "Zhang Xiaoxin" "space/fission research platform" "directSourceFit" "space-weather forecasting remains direct mission-environment fit" "event-level forecast/payload interface" "Fengyun project/participant identifiers"
zhangDaibing = round19-missing-object-coverage "Zhang Daibing" "vehicle/autonomy research object" "methodTransfer" "control/autonomy fit retained with vehicle-specific qualification debt" "vehicle model/gains/disturbance/test series" "NUDT task/code/programme receipt"
liMinyong = round19-missing-object-coverage "Li Minyong" "molecular-biology research platform" "directSourceFit" "photopharmacology/probe subsystem remains direct" "molecule wavelength-state-binding-readout replay" "grant/patent/project custody identifiers"
fang = round19-missing-object-coverage "Fang Daining" "extreme-environment structural/metamaterial object" "engineeringTransfer" "structural/metamaterial transfer retained" "energy functional/geometry/band/load replay" "national project/grant participant identifiers"
yan = round19-missing-object-coverage "Yan Hong" "combined rocket+scramjet / hypersonic inlet object" "directSourceFit" "thermal-excitation/SBLI science remains direct airbreathing-side fit" "mesh/source model/response curves" "NPU/national hypersonic project identifiers"

round19All : List Round19MissingObjectCoverage
round19All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round19ScientificCohortCount : Nat
round19ScientificCohortCount = 20

round19EveryScientistTouched : Bool
round19EveryScientistTouched = true

round19NoFitCount : Nat
round19NoFitCount = 0

round19HistoricalParticipationPromotionCount : Nat
round19HistoricalParticipationPromotionCount = 0

round19H2PromotionCount : Nat
round19H2PromotionCount = 0

round19H3PromotionCount : Nat
round19H3PromotionCount = 0

round19ObjectCoverageDoesNotPayHistoricalLink : Bool
round19ObjectCoverageDoesNotPayHistoricalLink = false

round19SearchResidualCreatesKnownAbsence : Bool
round19SearchResidualCreatesKnownAbsence = false
