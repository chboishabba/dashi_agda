module DASHI.Culture.MissingDeceasedTwentyScientistScienceImplementationCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SCIENCE IMPLEMENTATION DEPTH COVERAGE
--
-- A roster row can be source-attributed without having a mechanism owner, and a
-- typed mechanism can exist without an executable/finite witness.  This ledger
-- makes those stages explicit so Pareto routing can deepen the weakest science
-- rather than merely counting files.
------------------------------------------------------------------------

data ScienceImplementationDepth : Set where
  sourceAttributed typedMechanism equationDepth finiteWitness executableWitness
  identityGated programmeOnly : ScienceImplementationDepth

record ScienceImplementationCoverage : Set where
  constructor science-implementation-coverage
  field
    person : String
    domainOwner : String
    currentDepth : ScienceImplementationDepth
    paidKernel : String
    nextDepthLeaf : String
    domainOwnerPresent : Bool

open ScienceImplementationCoverage public

nunoCoverage = science-implementation-coverage
  "Nuno F. G. Loureiro"
  "LoureiroViriatoPlasmoidBidiExact + LoureiroKREHMHermiteEquationDepthExact + finite crossover/computation owners"
  finiteWitness
  "KREHM/KRMHD Fourier-Hermite equations, plasmoid/crossover machinery and finite computations"
  "weld source-exact Viriato benchmark cases to executable repository/runtime receipts"
  true

leblancCoverage = science-implementation-coverage
  "Joshua Kyle LeBlanc"
  "LeBlancFissionSurfacePowerICBidiExact + qualification-depth/sensor-matrix owners"
  typedMechanism
  "FSP I&C maturation, sensing, qualification coordinates"
  "close one source-exact sensor/qualification matrix with finite acceptance/failure witness"
  true

maiwaldCoverage = science-implementation-coverage
  "Frank W. Maiwald"
  "MaiwaldActionSpectroscopyBidiExact + QIT equation-depth/Mathieu-action compiler owners"
  equationDepth
  "QIT/action-spectroscopy physics and response compiler"
  "instantiate one DOI-linked tagged-ion spectrum with calibrated finite response data"
  true

rezaCoverage = science-implementation-coverage
  "Monica Jacinto / Monica Reza"
  "RezaBurnResistantAlloyBidiExact + tradeoff-depth/Pareto/finite non-dominance owners"
  finiteWitness
  "source compositions, oxygen burn/strength tradeoff and finite Pareto witnesses"
  "add source-exact MONDALOY coating/enamel descendant operating-window witness"
  true

grillmairCoverage = science-implementation-coverage
  "Carl J. Grillmair"
  "GrillmairStellarStreamBidiExact + matched-filter/orbit depth + executable distance-scan owners"
  executableWitness
  "matched-filter stellar-stream detection and finite distance scan"
  "bind one source-exact stream data slice and orbit-fit uncertainty receipt"
  true

hicksCoverage = science-implementation-coverage
  "Michael David Hicks"
  "HicksSmallBodyPhotometryBidiExact + HicksCometAsteroidSpecificWorksBidiExact"
  typedMechanism
  "small-body photometry/spectrophotometry and physical inference"
  "formalise one exact lightcurve dataset transform to rotation/phase result"
  true

mccaslandCoverage = science-implementation-coverage
  "William Neil McCasland"
  "McCaslandFaultTolerantFlexibleStructureControlBidiExact + Gramian/failure-family/beam finite engine"
  executableWitness
  "Gramian placement, failure-family compiler and finite beam engine"
  "source-weld the finite engine parameters to the historical flexible-structure example"
  true

chavezCoverage = science-implementation-coverage
  "Anthony Chavez"
  "AnthonyChavezScorpiusBidiExact; spectrometer-calibration owner remains separate identity"
  identityGated
  "LANL profile pays DARHT/Scorpius engineering carrier"
  "same-person weld first; then deepen source-exact subsystem geometry/calibration"
  true

thomasCoverage = science-implementation-coverage
  "Jason R. Thomas"
  "JasonThomasSignallingBidiExact + STING/ferritinophagy depth + target-deconvolution compiler"
  equationDepth
  "chemical-biology mechanism and target-deconvolution pipeline"
  "instantiate one Thomas-authored assay/perturbation dataset through the compiler"
  true

amyCoverage = science-implementation-coverage
  "Amy Eskridge"
  "AmyEskridgeGravityMechanismCrossPollinationExact"
  programmeOnly
  "programme-level mechanism discrimination is typed; conventional Amy-authored science object unresolved"
  "recover Amy-authored/recorded equations or apparatus object before deeper proof implementation"
  true

ningCoverage = science-implementation-coverage
  "Ning Li"
  "LiTorr theory owners + NingLiYBCOGravityConstraintBidiExact + rotating-field constraint owner"
  typedMechanism
  "theory plus source-exact static/rotating experimental constraints"
  "formalise finite apparatus/configuration comparison with control/confounder matrix"
  true

chenCoverage = science-implementation-coverage
  "Chen Shuming"
  "DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact"
  typedMechanism
  "graph-specification/simulation verification pipeline"
  "recover graph semantics, stimulus corpus and coverage metric; then add finite verification witness"
  true

fengCoverage = science-implementation-coverage
  "Feng Yanghe"
  "DASHI.GameTheory.FengYangheMilitaryAIGameStatisticsBidiExact"
  typedMechanism
  "Bayesian/noisy-label statistical methods and separately War Skull decision-agent science"
  "instantiate one finite Bayesian/noisy-label classifier and preserve same-object firewall to War Skull code"
  true

zhouCoverage = science-implementation-coverage
  "Zhou Guangyuan"
  "DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact"
  finiteWitness
  "SI-typed 473.15 K thermal-conductivity datum plus structure/process/property stages"
  "add source-exact shrinkage/porosity/thermal-bound finite portfolio and process-window relation"
  true

liuCoverage = science-implementation-coverage
  "Liu Donghao"
  "DASHI.ComputerScience.LiuDonghaoDSMMBidiExact"
  typedMechanism
  "data-lifecycle DSMM maturity/evidence pipeline"
  "recover exact authored assessment rubric/scoring and formalise a finite maturity-evaluation example"
  true

zhangXiaoxinCoverage = science-implementation-coverage
  "Zhang Xiaoxin"
  "DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastBidiExact"
  typedMechanism
  "spectral-whitening plus CEEMDAN-CWT forecast stages"
  "recover exact parameters/data split/metrics and implement a finite forecast witness"
  true

zhangDaibingCoverage = science-implementation-coverage
  "Zhang Daibing"
  "DASHI.Control.ZhangDaibingUAVControlBidiExact"
  typedMechanism
  "UAV sensing/localisation/guidance/control pipeline"
  "select one DOI object, recover dynamics/control law/gains/test geometry, and implement finite tracking witness"
  true

liMinyongCoverage = science-implementation-coverage
  "Li Minyong"
  "DASHI.Biology.LiMinyongPhotopharmacologyBidiExact"
  typedMechanism
  "light -> photoswitch/probe state -> target binding -> readout -> reversibility pipeline"
  "select one exact molecule/probe and add source-exact wavelength/binding/readout finite witness"
  true

fangCoverage = science-implementation-coverage
  "Fang Daining"
  "DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact"
  typedMechanism
  "active mechanical metamaterial / inverse-design mechanism"
  "formalise DOI 10.1016/j.jmps.2025.106144 energy-map/eigenmode finite witness"
  true

yanCoverage = science-implementation-coverage
  "Yan Hong"
  "DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact"
  typedMechanism
  "thermal-excitation high-speed inlet flow-control mechanism"
  "recover source-exact geometry/power/response values and add finite shock/separation witness"
  true

twentyScientistScienceImplementationCoverage : List ScienceImplementationCoverage
twentyScientistScienceImplementationCoverage =
  nunoCoverage ∷ leblancCoverage ∷ maiwaldCoverage ∷ rezaCoverage ∷
  grillmairCoverage ∷ hicksCoverage ∷ mccaslandCoverage ∷ chavezCoverage ∷
  thomasCoverage ∷ amyCoverage ∷ ningCoverage ∷ chenCoverage ∷ fengCoverage ∷
  zhouCoverage ∷ liuCoverage ∷ zhangXiaoxinCoverage ∷ zhangDaibingCoverage ∷
  liMinyongCoverage ∷ fangCoverage ∷ yanCoverage ∷ []

scienceImplementationCoverageCount : Nat
scienceImplementationCoverageCount = 20

allTwentyHaveDomainOwner : Bool
allTwentyHaveDomainOwner = true

typedMechanismDoesNotEqualExecutableWitness : Bool
typedMechanismDoesNotEqualExecutableWitness = true

sourceAttributionDoesNotEqualMechanismProof : Bool
sourceAttributionDoesNotEqualMechanismProof = true

identityGatedScienceCannotBeInheritedBeforeWeld : Bool
identityGatedScienceCannotBeInheritedBeforeWeld = true
