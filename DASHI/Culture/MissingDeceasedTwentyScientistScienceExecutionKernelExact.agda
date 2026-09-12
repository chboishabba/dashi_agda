module DASHI.Culture.MissingDeceasedTwentyScientistScienceExecutionKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SCIENCE-ONLY EXECUTION KERNEL
--
-- This is deliberately independent of event, custody and historical-programme
-- inference.  Each row states the scientific input, transform and output that
-- the in-repo owner currently formalises, together with the next science-only
-- implementation leaf.
------------------------------------------------------------------------

record ScienceExecutionKernel : Set where
  constructor science-execution-kernel
  field
    person : String
    formalOwner : String
    scienceInput : String
    scienceTransform : String
    scienceOutput : String
    referenceRunnable : Bool
    sourceReplayReady : Bool
    nextScienceImplementationLeaf : String

open ScienceExecutionKernel public

nunoKernel = science-execution-kernel "Nuno F. G. Loureiro"
  "LoureiroViriatoPlasmoidBidiExact / KREHM-Hermite depth owners"
  "reduced kinetic plasma state and Fourier-Hermite moments"
  "KREHM/KRMHD evolution, reconnection/plasmoid and Hermite-space propagation"
  "finite reduced-plasma state / instability and benchmark observables"
  true false
  "bind one published Viriato initial condition, closure, discretisation and output to an executable replay"

leblancKernel = science-execution-kernel "Joshua Kyle LeBlanc"
  "LeBlancFissionSurfacePowerICBidiExact / LeBlancFSPICFiniteWitnessExact"
  "fission-surface-power environment, sensor/function and control requirements"
  "instrumentation-and-control maturation, sensing, qualification and fault-response mapping"
  "finite I&C requirement/qualification-gap carrier"
  true false
  "instantiate one named sensor/device qualification, calibration and failure-response matrix"

maiwaldKernel = science-execution-kernel "Frank W. Maiwald"
  "MaiwaldActionSpectroscopyBidiExact / SourceReplayDepthExact"
  "messenger-tagged ValH+ ion population and IR wavenumber scan"
  "cryogenic trapping, irradiation, photodissociation and fragment/action-spectrum measurement"
  "source-replay spectral coordinates and molecular-structure discrimination"
  true true
  "replace source coordinates with raw experimental intensity array, absolute calibration and dissociation-time replay"

rezaKernel = science-execution-kernel "Monica Jacinto / Monica Reza"
  "RezaBurnResistantAlloyBidiExact / tradeoff-Pareto owners"
  "Ni-Co-Cr-Al-Ti composition, processing state and oxygen-service loading"
  "gamma/gamma-prime strengthening versus ignition/burn resistance tradeoff"
  "finite strength/burn non-dominance frontier"
  true false
  "implement source-exact MONDALOY/enamel descendant composition, process and qualification window"

grillmairKernel = science-execution-kernel "Carl J. Grillmair"
  "GrillmairStellarStreamBidiExact / SourceReplayExact"
  "stellar catalogue, colour-magnitude filter and sky-position/distance coordinates"
  "matched filtering, distance scan and stream-track/orbit inference"
  "source-replay stream-candidate geometry and executable detection carrier"
  true true
  "bind exact catalogue slice, filter weights, distance scan and orbit uncertainty"

hicksKernel = science-execution-kernel "Michael David Hicks"
  "HicksSmallBodyPhotometryBidiExact / SourceReplayExact"
  "time-stamped calibrated small-body photometry plus viewing geometry"
  "phase folding / lightcurve inference and multimodal physical-characterisation closure"
  "source-bound rotation/phase inference carrier"
  true true
  "bind Hicks Table Mountain lightcurve array, photometric calibration and viewing geometry"

mccaslandKernel = science-execution-kernel "William Neil McCasland"
  "McCaslandFaultTolerantFlexibleStructureControlBidiExact / finite Gramian engine"
  "plant matrices, candidate sensor/actuator sites and failure family"
  "controllability/observability Gramian scoring under failures"
  "executable robust placement ranking"
  true false
  "source-weld historical beam matrices, candidate locations and failure family"

chavezKernel = science-execution-kernel "Anthony Chavez"
  "AnthonyChavezScorpiusBidiExact"
  "LANL DARHT/Scorpius accelerator-engineering carrier"
  "technical subsystem design/diagnostic workflow"
  "identity-gated engineering science carrier"
  false false
  "pay same-person identity first, then recover exact subsystem geometry/calibration/design responsibility"

thomasKernel = science-execution-kernel "Jason R. Thomas"
  "JasonThomasSignallingBidiExact / JasonThomasSignallingFiniteWitnessExact"
  "chemical perturbation, assay readout and candidate target state"
  "screening, target deconvolution and signalling/ferritinophagy validation"
  "finite assay-to-mechanism validation carrier"
  true false
  "instantiate one Thomas-authored assay with source perturbation/readout counts and direct-target validation"

amyKernel = science-execution-kernel "Amy Eskridge"
  "AmyEskridgeGravityMechanismCrossPollinationExact"
  "claimed engineered-gravity mechanism family"
  "mechanism discrimination and comparator/null-test decomposition"
  "programme-level mechanism map only"
  false false
  "recover an Amy-authored/recorded equation, apparatus, deck or reviewed technical manuscript before execution"

ningKernel = science-execution-kernel "Ning Li"
  "LiTorr theory owners / NingLiYBCO apparatus comparison"
  "superconducting state, static/AC/rotating field geometry and precision gravity measurement"
  "theory-to-apparatus comparison, controls/confounders and null-result discrimination"
  "source-exact static-versus-rotating finite comparison"
  true false
  "implement later AC Gravity/NASA/Army apparatus geometry, drive, calibration and controls on the same comparator"

chenKernel = science-execution-kernel "Chen Shuming"
  "ChenShumingGraphHardwareVerificationBidiExact / FiniteWitnessExact"
  "graph specification, hardware stimulus and observed simulation trace"
  "simulation-based graph-conformance and coverage/mismatch checking"
  "finite hardware-verification carrier"
  true false
  "replace synthetic graph/stimulus counts with the source graph semantics, coverage metric and mismatch example"

fengKernel = science-execution-kernel "Feng Yanghe"
  "FengYangheMilitaryAIGameStatisticsBidiExact / ClassificationFiniteWitnessExact"
  "labelled/noisy-labelled samples and Bayesian/classification assumptions"
  "noise-aware Bayesian classification / attribute filtering"
  "finite classifier mechanism carrier"
  true false
  "replay one source example with exact equations, noise parameters, sample data and outputs"

zhouKernel = science-execution-kernel "Zhou Guangyuan"
  "ZhouGuangyuanPolyimideAerogelBidiExact / ProcessPropertySourceReplayExact"
  "monomer/synthesis/process coordinates and aerogel microstructure"
  "network formation, shrinkage/porosity evolution and thermal characterisation"
  "source-replay structure-property portfolio including SI thermal datum"
  true true
  "implement multi-sample synthesis-to-property table with batch uncertainty and process-window relation"

liuKernel = science-execution-kernel "Liu Donghao"
  "LiuDonghaoDSMMBidiExact / DSMMFiniteWitnessExact"
  "data lifecycle, controls, evidence and maturity criteria"
  "lifecycle-wide maturity assessment and evidence scoring"
  "finite DSMM assessment mechanism carrier"
  true false
  "replace synthetic scores with authored levels/clauses/scoring semantics and one source assessed example"

zhangXiaoxinKernel = science-execution-kernel "Zhang Xiaoxin"
  "ZhangXiaoxinGeomagneticForecastBidiExact / SourceReplayDepthExact"
  "cosmic-ray/time-series event carrier and geomagnetic-storm labels"
  "spectral whitening, CEEMDAN decomposition, IMF selection and CWT precursor extraction"
  "source-replay 229-event forecasting carrier with 129/166 finite recall witness"
  true true
  "implement exact whitening/CEEMDAN/CWT parameters, precursor quantisation and runnable source dataset"

zhangDaibingKernel = science-execution-kernel "Zhang Daibing"
  "ZhangDaibingUAVControlBidiExact / UAVControlFiniteWitnessExact"
  "vehicle state, sensors, localisation and trajectory/reference state"
  "state estimation, guidance, feedback control and landing/path/formation logic"
  "finite autonomy/control mechanism carrier"
  true false
  "source-replay one DOI with exact dynamics, control law, gains, sensor model, geometry and error series"

liMinyongKernel = science-execution-kernel "Li Minyong"
  "LiMinyongPhotopharmacologyBidiExact / PhotopharmacologyFiniteWitnessExact"
  "molecular photoswitch/probe, incident wavelength and target state"
  "photoisomerisation/probe activation, target binding and optical/physiological readout"
  "finite reversible light-to-target/readout carrier"
  true false
  "bind one exact compound/probe wavelength, photostationary state, affinity, dose and readout kinetics"

fangKernel = science-execution-kernel "Fang Daining"
  "FangDainingActiveMechanicalMetamaterialBidiExact / InverseDesignSourceReplayExact"
  "unit-cell/material design variables and target eigenmode/dispersion objective"
  "force-field-induced energy inverse design and band/eigenmode computation"
  "source-replay inverse-design objective and negative-group-velocity witness"
  true true
  "implement full energy functional, unit-cell geometry/constants and computed/experimental band arrays"

yanKernel = science-execution-kernel "Yan Hong"
  "YanHongHypersonicFlowControlBidiExact / ThermalExcitationSourceReplayExact"
  "supersonic/hypersonic inlet flow plus thermal-actuator geometry/power state"
  "thermal/plasma excitation coupled to shock/boundary-layer interaction"
  "source-replay Mach-5 actuator-case response carrier"
  true true
  "implement source geometry, heat-source model, mesh/boundaries and shock/separation response curves"

scienceExecutionKernels : List ScienceExecutionKernel
scienceExecutionKernels =
  nunoKernel ∷ leblancKernel ∷ maiwaldKernel ∷ rezaKernel ∷ grillmairKernel ∷
  hicksKernel ∷ mccaslandKernel ∷ chavezKernel ∷ thomasKernel ∷ amyKernel ∷
  ningKernel ∷ chenKernel ∷ fengKernel ∷ zhouKernel ∷ liuKernel ∷
  zhangXiaoxinKernel ∷ zhangDaibingKernel ∷ liMinyongKernel ∷ fangKernel ∷ yanKernel ∷ []

scienceExecutionKernelsCount : Nat
scienceExecutionKernelsCount = 20

scienceRunnableCount : Nat
scienceRunnableCount = 18

scienceSourceReplayReadyCount : Nat
scienceSourceReplayReadyCount = 7

scienceGatedCount : Nat
scienceGatedCount = 2

scienceExecutionDoesNotPayHistoricalUse : Bool
scienceExecutionDoesNotPayHistoricalUse = false

scienceExecutionDoesNotPayCustody : Bool
scienceExecutionDoesNotPayCustody = false

scienceExecutionCanDriveImplementationPareto : Bool
scienceExecutionCanDriveImplementationPareto = true
