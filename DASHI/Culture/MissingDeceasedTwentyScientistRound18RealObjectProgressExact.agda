module DASHI.Culture.MissingDeceasedTwentyScientistRound18RealObjectProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round18RealObjectProgress : Set where
  constructor round18-real-object-progress
  field
    person : String
    strongestCurrentObject : String
    strongestFitClass : String
    freshDelta : String
    nextObjectLeaf : String
    nextHistoricalReceiptLeaf : String

open Round18RealObjectProgress public

nuno = round18-real-object-progress "Nuno F. G. Loureiro" "space/fission or high-energy platform" "methodTransfer" "plasma/reconnection science now sits as a method-level environmental/high-energy modelling fibre rather than being forced into propulsion hardware" "instantiate a sourced plasma-rich application geometry" "search only after a literal shared project/facility identifier appears"
leblanc = round18-real-object-progress "Joshua Kyle LeBlanc" "space/fission research platform" "directSourceFit" "FSP I&C now anchors the ordinary-engineering space-platform object" "recover exact I&C gap/qualification matrix" "post-loss TechMat roster and same-work-package participant receipts"
maiwald = round18-real-object-progress "Frank W. Maiwald" "molecular-biology platform" "directSourceFit" "action spectroscopy is now a direct molecular-diagnostics subsystem and a method-level high-energy diagnostic" "raw spectrum/calibration replay" "JPL work-package/instrument ID if searching cross-person history"
reza = round18-real-object-progress "Monica Jacinto / Monica Reza" "combined rocket+scramjet vehicle, booster side" "directSourceFit" "oxygen-service alloy now lands primarily on stored-oxidizer rocket service while scramjet use remains transfer-only" "component/process/qualification window" "pre-2013 Mondaloy programme/work-package identifiers and named participants"
grillmair = round18-real-object-progress "Carl J. Grillmair" "none of current four physical subsystem objects" "analogyOnly" "stellar-stream inference remains correctly outside the current object set rather than being shoehorned" "add a real astronomical survey/observatory object" "search catalogue/survey/work-package identity only on that sourced object"
hicks = round18-real-object-progress "Michael David Hicks" "none of current four physical subsystem objects" "analogyOnly" "small-body photometry is preserved as mission/payload science, not propulsion/control machinery" "add a planetary-observatory/survey object" "recover shared survey/project identifier before cross-person promotion"
mccasland = round18-real-object-progress "William Neil McCasland" "combined vehicle / space platform / high-energy facility" "methodTransfer" "fault-tolerant placement now appears as a reusable cross-object method rather than a programme-specific claim" "instantiate exact plant/site/failure family" "literal programme review/tasking document before H2"
chavez = round18-real-object-progress "Anthony Chavez" "high-energy experimental facility" "directSourceFit identity-gated" "DARHT/Scorpius maps cleanly to the high-energy-facility class but identity remains the prerequisite" "same-person identity weld plus exact subsystem task" "cross-case programme search only after identity weld"
thomas = round18-real-object-progress "Jason R. Thomas" "molecular-biology platform" "directSourceFit" "signalling/ferritinophagy work now occupies a concrete assay/validation subsystem" "supporting-information matrix and target-validation replay" "lab/project succession remains separate from event cause"
amy = round18-real-object-progress "Amy Eskridge" "high-energy precision/null-test facility" "analogyOnly programme-gated" "mechanism-discrimination material now informs null-test requirements without being promoted to authored apparatus science" "recover Amy-authored/recorded technical object" "search AC Gravity/DAAH01 identifiers only after object identity is paid"
ning = round18-real-object-progress "Ning Li" "high-energy precision-force facility" "directSourceFit" "published static/rotating YBCO experiments now have a natural benign precision-test object" "later apparatus/calibration plus Army SOW/closeout" "enumerate personnel/facility/subcontract identifiers on DAAH01-01-9-R001"
chen = round18-real-object-progress "Chen Shuming" "combined vehicle / space platform / high-energy facility" "methodTransfer" "hardware verification is now explicitly reusable across digital control/instrumentation objects" "one exact graph/specification/stimulus/coverage replay" "exact NUDT task/project identifier before programme inference"
feng = round18-real-object-progress "Feng Yanghe" "no low-invention current object subsystem" "analogyOnly" "Bayesian/noisy-label methods remain broad decision-science adjacency rather than a forced subsystem" "recover exact algorithm/equation/dataset then source a consuming object" "exact military task/code/work-package identifier"
zhou = round18-real-object-progress "Zhou Guangyuan" "combined vehicle / space platform / high-energy facility" "engineeringTransfer" "polyimide aerogel now appears consistently as a thermal-management candidate across multiple extreme environments" "complete process/property table plus environment-specific qualification" "DNL2200 grant/patent/enterprise-transfer cross-identifiers"
liu = round18-real-object-progress "Liu Donghao" "space/high-energy/molecular research platforms" "methodTransfer" "DSMM now has a cross-object research-data governance role without being miscast as a physical mechanism" "exact maturity rubric and one platform lifecycle instantiation" "dated national project/company governance identifiers"
zhangXiaoxin = round18-real-object-progress "Zhang Xiaoxin" "space/fission research platform" "directSourceFit" "space-weather forecasting now lands directly on an ordinary long-duration space platform" "event-level forecast data and payload/calibration interface" "Fengyun project/participant identifiers"
zhangDaibing = round18-real-object-progress "Zhang Daibing" "combined vehicle / space platform" "methodTransfer" "guidance/autonomy remains transferable only after vehicle-specific dynamics and qualification" "exact vehicle model/gains/disturbance/test series" "NUDT programme/code/task identifier"
liMinyong = round18-real-object-progress "Li Minyong" "molecular-biology platform" "directSourceFit" "photopharmacology/probe science now has a natural molecular-control subsystem" "one molecule wavelength-state-binding-readout-kinetics replay" "grant/project/patent co-custody identifiers"
fang = round18-real-object-progress "Fang Daining" "combined vehicle / space platform / high-energy facility" "engineeringTransfer" "extreme-environment mechanics/metamaterial work now maps to qualified structural roles without implying a specific vehicle" "energy functional, geometry, band data and environment-specific loads" "national project/grant and cross-institution participant identifiers"
yan = round18-real-object-progress "Yan Hong" "combined rocket+scramjet vehicle, airbreathing side" "directSourceFit" "Mach-5 inlet/SBLI science now anchors the scramjet-side object directly" "mesh, thermal-source model, response curves and inlet qualification" "NPU/national hypersonic project identifiers and partner roster"

round18All : List Round18RealObjectProgress
round18All = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round18ScientificCohortCount : Nat
round18ScientificCohortCount = 20

round18EveryScientistTouched : Bool
round18EveryScientistTouched = true

round18HistoricalParticipationPromotionCount : Nat
round18HistoricalParticipationPromotionCount = 0

round18H2PromotionCount : Nat
round18H2PromotionCount = 0

round18H3PromotionCount : Nat
round18H3PromotionCount = 0

round18NoFitMayNominateMissingObjectClass : Bool
round18NoFitMayNominateMissingObjectClass = true

round18ObjectFitCreatesCommonCause : Bool
round18ObjectFitCreatesCommonCause = false
