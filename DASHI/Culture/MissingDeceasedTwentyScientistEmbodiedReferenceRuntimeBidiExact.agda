module DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact as E
import DASHI.Culture.MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact as F
import DASHI.Culture.MissingDeceasedTwentyScientistScienceSourceReplayBidiExact as S
import DASHI.Programmes.CoreReferenceCorrectionExact as Ref

------------------------------------------------------------------------
-- REFERENCE RUNTIME BIDI
--
-- The embodied Agda object remains the formal owner.  This module exposes the
-- finite/source-replay readiness needed by a reference runtime and compiles a
-- composite application request back into the role/evidence residuals already
-- owned by the embodied BIDI.  A runtime trace is therefore an execution or
-- parity receipt, never a replacement for Agda semantics or source evidence.
------------------------------------------------------------------------

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
mkFinite person slot input output reverse =
  reference-runtime-slot person slot finiteWitnessReady true false input output reverse

mkReplay : String → E.EmbodiedTechnologySlot → String → String → String → ReferenceRuntimeSlot
mkReplay person slot input output reverse =
  reference-runtime-slot person slot sourceReplayReady true true input output reverse

mkGated : String → E.EmbodiedTechnologySlot → String → ReferenceRuntimeSlot
mkGated person slot reverse =
  reference-runtime-slot person slot identityOrAuthorshipGated false false
    "gated: formal input cannot be inherited yet"
    "no reference execution promoted"
    reverse

nunoRuntime = mkFinite "Nuno F. G. Loureiro" E.nunoSlot
  "finite KREHM/Hermite/plasmoid coordinates"
  "reduced-kinetic plasma reference-state summary"
  "replace finite/reconstructed benchmark with source-exact Viriato initial condition, closure and runtime output"

leblancRuntime = mkFinite "Joshua Kyle LeBlanc" E.leblancSlot
  "source-exact notional FSP environment plus finite sensor/function carrier"
  "qualification-gap and sensor-role plan"
  "bind named candidate devices, calibration/failure evidence and qualification protocols"

maiwaldRuntime = mkReplay "Frank W. Maiwald" E.maiwaldSlot
  "source replay: 1000-1900 cm^-1 ValH+ window, tag temperatures and highlighted feature"
  "tag/action-spectrum discrimination plan"
  "replace source coordinates without intensity array by raw/supporting spectrum and calibration data"

rezaRuntime = mkFinite "Monica Jacinto / Monica Reza" E.rezaSlot
  "source compositions plus finite burn-strength tradeoff witnesses"
  "oxygen-service material tradeoff plan"
  "add source-exact MONDALOY/enamel descendant process and qualification window"

grillmairRuntime = mkFinite "Carl J. Grillmair" E.grillmairSlot
  "executable matched-filter/distance-scan witness"
  "weak stellar-stream signal candidate plan"
  "bind one source catalogue slice, colour-magnitude filter and orbit uncertainty receipt"

hicksRuntime = mkFinite "Michael David Hicks" E.hicksSlot
  "finite small-body photometry/phase carrier"
  "rotation/phase inference shape"
  "replace synthetic series with source lightcurve, viewing geometry and calibration"

mccaslandRuntime = mkFinite "William Neil McCasland" E.mccaslandSlot
  "finite Gramian placement/failure-family engine"
  "resilient sensor/actuator placement plan"
  "source-weld historical plant matrices, candidate locations and failure family"

chavezRuntime = mkGated "Anthony Chavez" E.chavezSlot
  "pay primary same-person weld before inheriting LANL/Scorpius technical state"

thomasRuntime = mkFinite "Jason R. Thomas" E.thomasSlot
  "finite signalling perturbation/readout/validation carrier"
  "assay-to-target validation plan"
  "replace synthetic counts with Thomas-authored assay and target-deconvolution data"

amyRuntime = mkGated "Amy Eskridge" E.amySlot
  "recover Amy-authored/recorded technical equations/apparatus and source identity before execution"

ningRuntime = mkFinite "Ning Li" E.ningSlot
  "source-exact static-versus-rotating YBCO apparatus comparison"
  "null-test/configuration discriminator plan"
  "recover later AC Gravity/Army apparatus, controls and same-object continuity"

chenRuntime = mkFinite "Chen Shuming" E.chenSlot
  "finite graph-specification verification carrier"
  "hardware verification residual plan"
  "replace synthetic counts with source graph, stimuli, coverage and mismatch oracle"

fengRuntime = mkFinite "Feng Yanghe" E.fengSlot
  "finite Bayesian/noisy-label classification carrier"
  "noise-robust classification plan"
  "replace synthetic samples with source model/data and independently weld any War Skull implementation"

zhouRuntime = mkFinite "Zhou Guangyuan" E.zhouSlot
  "source-exact SI thermal datum plus finite aerogel property carrier"
  "thermal material process/property plan"
  "recover multi-sample synthesis/property table and process-window relation"

liuRuntime = mkFinite "Liu Donghao" E.liuSlot
  "finite DSMM lifecycle/evidence carrier"
  "data-security maturity residual plan"
  "replace synthetic evidence counts with authored rubric, scoring and assessed example"

zhangXiaoxinRuntime = mkReplay "Zhang Xiaoxin" E.zhangXiaoxinSlot
  "source replay: 229-event Oulu carrier, split/accuracy and IMF/time-scale coordinates"
  "space-weather forecast replay plan"
  "recover exact whitening/CEEMDAN/CWT hyperparameters, precursor rule and runnable code/data"

zhangDaibingRuntime = mkFinite "Zhang Daibing" E.zhangDaibingSlot
  "finite UAV sensing/localisation/guidance/control carrier"
  "autonomy/control replay plan"
  "select one DOI and bind exact dynamics, gains, sensor model, geometry and error series"

liMinyongRuntime = mkFinite "Li Minyong" E.liMinyongSlot
  "finite light-state/binding/readout carrier"
  "photochemical assay/control plan"
  "bind one exact molecule/probe, wavelength, affinity, dose, calibration and kinetics"

fangRuntime = mkReplay "Fang Daining" E.fangSlot
  "source replay: force-field energy-design objective and verified negative-group-velocity claim"
  "metamaterial inverse-design replay plan"
  "recover full energy functional, unit-cell geometry, constants and band arrays"

yanRuntime = mkReplay "Yan Hong" E.yanSlot
  "source replay: four Mach-5 actuator cases and qualitative response ordering"
  "thermal flow-control replay plan"
  "recover heat-source model, geometry/mesh/boundaries and shock/separation curves"

referenceRuntimeSlots : List ReferenceRuntimeSlot
referenceRuntimeSlots =
  nunoRuntime ∷ leblancRuntime ∷ maiwaldRuntime ∷ rezaRuntime ∷ grillmairRuntime ∷
  hicksRuntime ∷ mccaslandRuntime ∷ chavezRuntime ∷ thomasRuntime ∷ amyRuntime ∷
  ningRuntime ∷ chenRuntime ∷ fengRuntime ∷ zhouRuntime ∷ liuRuntime ∷
  zhangXiaoxinRuntime ∷ zhangDaibingRuntime ∷ liMinyongRuntime ∷ fangRuntime ∷
  yanRuntime ∷ []

referenceRuntimeSlotsCount : Nat
referenceRuntimeSlotsCount = 20

referenceRunnableSlotCount : Nat
referenceRunnableSlotCount = 18

referenceGatedSlotCount : Nat
referenceGatedSlotCount = 2

sourceReplayRuntimeSlotCount : Nat
sourceReplayRuntimeSlotCount = 4

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
referencePlanFor application = reference-application-plan
  application
  (E.requiredRoles application)
  (E.reverseNeedsFor application)
  "DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact"
  "Reference execution plans roles/residuals only; it does not define Agda semantics, source replication, historical deployment or person possession."

longDurationReferencePlan : ReferenceApplicationPlan
longDurationReferencePlan = referencePlanFor E.longDurationSciencePlatform

extremeEnvironmentReferencePlan : ReferenceApplicationPlan
extremeEnvironmentReferencePlan = referencePlanFor E.extremeEnvironmentResearchTestbed

autonomousSurveyReferencePlan : ReferenceApplicationPlan
autonomousSurveyReferencePlan = referencePlanFor E.autonomousRemoteSurveyPlatform

multiDomainLabReferencePlan : ReferenceApplicationPlan
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
