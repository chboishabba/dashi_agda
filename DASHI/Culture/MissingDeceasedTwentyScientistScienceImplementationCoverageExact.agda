module DASHI.Culture.MissingDeceasedTwentyScientistScienceImplementationCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

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

nunoCoverage = science-implementation-coverage "Nuno F. G. Loureiro"
  "LoureiroViriatoPlasmoidBidiExact + KREHM/Hermite/finite computation owners"
  finiteWitness
  "KREHM/KRMHD Fourier-Hermite equations, plasmoid machinery and finite computations"
  "source-exact Viriato benchmark replay"
  true

leblancCoverage = science-implementation-coverage "Joshua Kyle LeBlanc"
  "LeBlancFissionSurfacePowerICBidiExact + LeBlancFSPICFiniteWitnessExact"
  finiteWitness
  "FSP I&C environment/sensor/function and finite qualification-gap carrier"
  "named device qualification/calibration/failure matrix"
  true

maiwaldCoverage = science-implementation-coverage "Frank W. Maiwald"
  "MaiwaldActionSpectroscopyBidiExact + finite/source-replay owners"
  finiteWitness
  "QIT/action-spectroscopy physics plus source spectral coordinates"
  "raw experimental action-spectrum intensity/calibration replay"
  true

rezaCoverage = science-implementation-coverage "Monica Jacinto / Monica Reza"
  "RezaBurnResistantAlloyBidiExact + tradeoff/Pareto/finite non-dominance owners"
  finiteWitness
  "source compositions, oxygen burn/strength tradeoff and finite Pareto witnesses"
  "source-exact MONDALOY/enamel process/qualification window"
  true

grillmairCoverage = science-implementation-coverage "Carl J. Grillmair"
  "GrillmairStellarStreamBidiExact + executable matched-filter/distance-scan + source replay"
  executableWitness
  "matched-filter stellar-stream detection, finite distance scan and source ensemble geometry"
  "catalogue/filter/orbit-uncertainty replay"
  true

hicksCoverage = science-implementation-coverage "Michael David Hicks"
  "HicksSmallBodyPhotometryBidiExact + finite/source-replay owners"
  finiteWitness
  "small-body photometry/phase inference plus Florence campaign source coordinates"
  "source lightcurve array, viewing geometry and calibration"
  true

mccaslandCoverage = science-implementation-coverage "William Neil McCasland"
  "McCaslandFaultTolerantFlexibleStructureControlBidiExact + Gramian finite engine"
  executableWitness
  "Gramian placement, failure-family compiler and finite beam engine"
  "historical source plant/candidate/failure-family weld"
  true

chavezCoverage = science-implementation-coverage "Anthony Chavez"
  "AnthonyChavezScorpiusBidiExact"
  identityGated
  "LANL profile pays DARHT/Scorpius engineering carrier only"
  "same-person weld first; then exact subsystem geometry/calibration"
  true

thomasCoverage = science-implementation-coverage "Jason R. Thomas"
  "JasonThomasSignallingBidiExact + JasonThomasSignallingFiniteWitnessExact"
  finiteWitness
  "chemical-biology perturbation/readout/target-deconvolution finite carrier"
  "one Thomas-authored source assay replay"
  true

amyCoverage = science-implementation-coverage "Amy Eskridge"
  "AmyEskridgeGravityMechanismCrossPollinationExact"
  programmeOnly
  "programme-level mechanism discrimination is typed; Amy-authored technical science remains unresolved"
  "recover Amy-authored/recorded equations or apparatus before execution"
  true

ningCoverage = science-implementation-coverage "Ning Li"
  "LiTorr theory + static/rotating YBCO finite apparatus comparison"
  finiteWitness
  "theory plus source-exact static/rotating experimental constraint comparison"
  "later apparatus/control/calibration replay"
  true

chenCoverage = science-implementation-coverage "Chen Shuming"
  "ChenShumingGraphHardwareVerificationBidiExact + FiniteWitnessExact"
  finiteWitness
  "finite graph-specification/simulation verification carrier"
  "source graph/stimulus/coverage/mismatch replay"
  true

fengCoverage = science-implementation-coverage "Feng Yanghe"
  "FengYangheMilitaryAIGameStatisticsBidiExact + ClassificationFiniteWitnessExact"
  finiteWitness
  "finite Bayesian/noisy-label classifier carrier"
  "source equations/data/noise-parameter replay"
  true

zhouCoverage = science-implementation-coverage "Zhou Guangyuan"
  "ZhouGuangyuanPolyimideAerogelBidiExact + finite/source-replay owners"
  finiteWitness
  "SI thermal datum plus source shrinkage/porosity/surface-area/stability portfolio"
  "multi-sample process/property/uncertainty replay"
  true

liuCoverage = science-implementation-coverage "Liu Donghao"
  "LiuDonghaoDSMMBidiExact + DSMMFiniteWitnessExact"
  finiteWitness
  "finite lifecycle-wide data-security maturity/evidence carrier"
  "authored rubric/scoring and source assessed example"
  true

zhangXiaoxinCoverage = science-implementation-coverage "Zhang Xiaoxin"
  "ZhangXiaoxinGeomagneticForecastBidiExact + finite/source-replay depth owners"
  finiteWitness
  "229-event CEEMDAN-CWT forecast carrier with 129/166 source recall witness"
  "exact decomposition parameters/code/data replay"
  true

zhangDaibingCoverage = science-implementation-coverage "Zhang Daibing"
  "ZhangDaibingUAVControlBidiExact + UAVControlFiniteWitnessExact"
  finiteWitness
  "finite sensing/localisation/guidance/control carrier"
  "one DOI source dynamics/control/test replay"
  true

liMinyongCoverage = science-implementation-coverage "Li Minyong"
  "LiMinyongPhotopharmacologyBidiExact + PhotopharmacologyFiniteWitnessExact"
  finiteWitness
  "finite light/photoswitch/target/readout/reversibility carrier"
  "one exact molecule/probe source replay"
  true

fangCoverage = science-implementation-coverage "Fang Daining"
  "FangDainingActiveMechanicalMetamaterialBidiExact + finite/source-replay owners"
  finiteWitness
  "inverse-design mechanism plus source negative-group-velocity replay coordinates"
  "full energy functional/unit-cell/band-array implementation"
  true

yanCoverage = science-implementation-coverage "Yan Hong"
  "YanHongHypersonicFlowControlBidiExact + finite/source-replay owners"
  finiteWitness
  "Mach-5 thermal-excitation flow-control finite/source replay"
  "source geometry/heat-model/mesh/shock-response replay"
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

finiteOrStrongerCoverageCount : Nat
finiteOrStrongerCoverageCount = 18

allTwentyHaveDomainOwner : Bool
allTwentyHaveDomainOwner = true

typedMechanismDoesNotEqualExecutableWitness : Bool
typedMechanismDoesNotEqualExecutableWitness = true

sourceAttributionDoesNotEqualMechanismProof : Bool
sourceAttributionDoesNotEqualMechanismProof = true

identityGatedScienceCannotBeInheritedBeforeWeld : Bool
identityGatedScienceCannotBeInheritedBeforeWeld = true
