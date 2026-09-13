module DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact as E
import DASHI.Culture.MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact as F
import DASHI.Culture.MissingDeceasedTwentyScientistScienceSourceReplayBidiExact as S
import DASHI.Programmes.CoreReferenceCorrectionExact as Ref

data RuntimeReadiness : Set where
  sourceReplayReady finiteWitnessReady identityOrAuthorshipGated : RuntimeReadiness

record ReferenceRuntimeSlot : Set where
  constructor reference-runtime-slot
  field
    person : String
    embodiedSlot : E.EmbodiedTechnologySlot
    readiness : RuntimeReadiness
    referenceRunnable : Bool
    sourceExactReplayAvailable : Bool
    runtimeInput : String
    runtimeOutput : String
    reverseReplacementLeaf : String

open ReferenceRuntimeSlot public

mkFinite : String → E.EmbodiedTechnologySlot → String → String → String → ReferenceRuntimeSlot
mkFinite person slot input output reverse = reference-runtime-slot person slot finiteWitnessReady true false input output reverse

mkReplay : String → E.EmbodiedTechnologySlot → String → String → String → ReferenceRuntimeSlot
mkReplay person slot input output reverse = reference-runtime-slot person slot sourceReplayReady true true input output reverse

mkGated : String → E.EmbodiedTechnologySlot → String → ReferenceRuntimeSlot
mkGated person slot reverse = reference-runtime-slot person slot identityOrAuthorshipGated false false
  "gated: formal input cannot be inherited yet" "no reference execution promoted" reverse

nunoRuntime = mkFinite "Nuno F. G. Loureiro" E.nunoSlot "finite KREHM/Hermite/plasmoid coordinates" "reduced-kinetic plasma reference-state summary" "source-exact Viriato benchmark/runtime output"
leblancRuntime = mkFinite "Joshua Kyle LeBlanc" E.leblancSlot "source-exact notional FSP environment plus finite sensor/function carrier" "qualification-gap and sensor-role plan" "named candidate devices, calibration/failure and qualification"
maiwaldRuntime = mkReplay "Frank W. Maiwald" E.maiwaldSlot "source replay plus SI inventory: ValH+ window/tag temperatures/1773 cm^-1 feature" "tag/action-spectrum discrimination plan" "raw experimental intensity array and absolute calibration"
rezaRuntime = mkFinite "Monica Jacinto / Monica Reza" E.rezaSlot "source compositions plus finite burn-strength tradeoff" "oxygen-service material tradeoff plan" "MONDALOY/enamel process and qualification window"
grillmairRuntime = mkReplay "Carl J. Grillmair" E.grillmairSlot "source replay: four-stream ensemble geometry and Molonglo/ATLAS offset" "stellar-stream inference replay plan" "catalogue slice, matched-filter weights and orbit uncertainty"
hicksRuntime = mkReplay "Michael David Hicks" E.hicksSlot "source replay: Florence Table Mountain participation and 2.4 h campaign period" "rotation/phase inference replay plan" "Hicks lightcurve array, viewing geometry and calibration"
mccaslandRuntime = mkFinite "William Neil McCasland" E.mccaslandSlot "finite Gramian placement/failure-family engine" "resilient sensor/actuator placement plan" "historical plant matrices/candidate locations/failure family"
chavezRuntime = mkGated "Anthony Chavez" E.chavezSlot "pay primary same-person weld before inheriting LANL/Scorpius technical state"
thomasRuntime = mkFinite "Jason R. Thomas" E.thomasSlot "finite signalling perturbation/readout carrier" "assay-to-target validation plan" "Thomas-authored assay and target-deconvolution data"
amyRuntime = mkGated "Amy Eskridge" E.amySlot "recover Amy-authored/recorded technical equations/apparatus and source identity"
ningRuntime = mkFinite "Ning Li" E.ningSlot "source-exact static-versus-rotating YBCO apparatus comparison" "null-test/configuration discriminator plan" "later AC Gravity/Army apparatus and controls"
chenRuntime = mkFinite "Chen Shuming" E.chenSlot "finite graph-specification verification carrier" "hardware verification residual plan" "source graph, stimuli, coverage and mismatch oracle"
fengRuntime = mkFinite "Feng Yanghe" E.fengSlot "finite Bayesian/noisy-label classifier" "noise-robust classification plan" "source model/data plus separate War Skull weld"
zhouRuntime = mkReplay "Zhou Guangyuan" E.zhouSlot "source replay: finite aerogel shrinkage/porosity/surface-area/thermal portfolio" "thermal material process/property replay plan" "multi-sample synthesis/property table and process window"
liuRuntime = mkFinite "Liu Donghao" E.liuSlot "finite DSMM lifecycle/evidence carrier" "data-security maturity residual plan" "authored rubric/scoring and assessed example"
zhangXiaoxinRuntime = mkReplay "Zhang Xiaoxin" E.zhangXiaoxinSlot "source replay: 229-event carrier with 129/166 finite recall witness" "space-weather forecast replay plan" "exact whitening/CEEMDAN/CWT hyperparameters, code/data"
zhangDaibingRuntime = mkFinite "Zhang Daibing" E.zhangDaibingSlot "finite UAV sensing/localisation/guidance/control carrier" "autonomy/control replay plan" "one DOI exact dynamics/gains/sensor/error series"
liMinyongRuntime = mkFinite "Li Minyong" E.liMinyongSlot "finite light-state/binding/readout carrier" "photochemical assay/control plan" "one exact molecule/probe and kinetics"
fangRuntime = mkReplay "Fang Daining" E.fangSlot "source replay: energy-design objective and negative-group-velocity claim" "metamaterial inverse-design replay plan" "full energy functional, geometry/constants and bands"
yanRuntime = mkReplay "Yan Hong" E.yanSlot "source replay: four Mach-5 actuator cases and qualitative ordering" "thermal flow-control replay plan" "heat-source model, geometry and shock/separation curves"

referenceRuntimeSlots : List ReferenceRuntimeSlot
referenceRuntimeSlots = nunoRuntime ∷ leblancRuntime ∷ maiwaldRuntime ∷ rezaRuntime ∷ grillmairRuntime ∷ hicksRuntime ∷ mccaslandRuntime ∷ chavezRuntime ∷ thomasRuntime ∷ amyRuntime ∷ ningRuntime ∷ chenRuntime ∷ fengRuntime ∷ zhouRuntime ∷ liuRuntime ∷ zhangXiaoxinRuntime ∷ zhangDaibingRuntime ∷ liMinyongRuntime ∷ fangRuntime ∷ yanRuntime ∷ []

referenceRuntimeSlotsCount : Nat
referenceRuntimeSlotsCount = 20
referenceRunnableSlotCount : Nat
referenceRunnableSlotCount = 18
referenceGatedSlotCount : Nat
referenceGatedSlotCount = 2
sourceReplayRuntimeSlotCount : Nat
sourceReplayRuntimeSlotCount = 7

record ReferenceApplicationPlan : Set where
  constructor reference-application-plan
  field
    application : E.CompositeApplication
    requiredRoles : List E.EmbodiedSubsystemRole
    reverseNeeds : List String
    formalOwner : String
    runtimeBoundary : String
open ReferenceApplicationPlan public

referencePlanFor : E.CompositeApplication → ReferenceApplicationPlan
referencePlanFor application = reference-application-plan application (E.requiredRoles application) (E.reverseNeedsFor application)
  "DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact"
  "Reference execution plans roles/residuals only; it does not define Agda semantics, source replication, historical deployment or person possession."

longDurationReferencePlan = referencePlanFor E.longDurationSciencePlatform
extremeEnvironmentReferencePlan = referencePlanFor E.extremeEnvironmentResearchTestbed
autonomousSurveyReferencePlan = referencePlanFor E.autonomousRemoteSurveyPlatform
multiDomainLabReferencePlan = referencePlanFor E.multiDomainResearchLaboratory

referenceImplementationBoundary : Ref.CoreReferenceCorrectionBoundary
referenceImplementationBoundary = Ref.canonicalCoreReferenceCorrectionBoundary
referenceRuntimeDefinesFormalSemantics : Bool
referenceRuntimeDefinesFormalSemantics = false
referenceRuntimePaysSourceReplay : Bool
referenceRuntimePaysSourceReplay = false
referenceRuntimePaysHistoricalDeployment : Bool
referenceRuntimePaysHistoricalDeployment = false
referenceRuntimePaysPersonPossession : Bool
referenceRuntimePaysPersonPossession = false
referenceRuntimeCanEmitReverseAcquisitionPlan : Bool
referenceRuntimeCanEmitReverseAcquisitionPlan = true
