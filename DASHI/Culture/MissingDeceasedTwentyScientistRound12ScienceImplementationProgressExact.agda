module DASHI.Culture.MissingDeceasedTwentyScientistRound12ScienceImplementationProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceExecutionKernelExact as Kernel

record Round12ScienceProgress : Set where
  constructor round12-science-progress
  field
    person : String
    currentScienceObject : String
    round12Delta : String
    nextScienceLeaf : String

open Round12ScienceProgress public

nuno = round12-science-progress "Nuno F. G. Loureiro" "KREHM/KRMHD Fourier-Hermite and plasmoid machinery" "science-only kernel now exposes reduced-state -> evolution -> finite observable transducer" "source-exact Viriato benchmark with initial condition, closure, discretisation and output"
leblanc = round12-science-progress "Joshua Kyle LeBlanc" "FSP instrumentation/control finite carrier" "science-only kernel exposes environment/sensor/function -> qualification-gap transform" "named sensor/device qualification, calibration, failure and autonomous-response matrix"
maiwald = round12-science-progress "Frank W. Maiwald" "messenger-tag action spectroscopy source replay" "science-only kernel exposes ion/tag/IR input -> photodissociation -> spectrum/structure output" "raw experimental spectrum intensities, absolute calibration and dissociation-time replay"
reza = round12-science-progress "Monica Jacinto / Monica Reza" "oxygen-service alloy burn/strength Pareto" "science-only kernel exposes composition/process -> gamma-prime/burn tradeoff -> finite frontier" "MONDALOY/enamel descendant composition, process and qualification window"
grillmair = round12-science-progress "Carl J. Grillmair" "matched-filter stellar-stream source replay" "science-only kernel exposes catalogue/filter -> distance scan -> stream/orbit inference" "exact catalogue slice, filter weights and orbit-fit uncertainty"
hicks = round12-science-progress "Michael David Hicks" "small-body photometry source replay" "science-only kernel exposes calibrated photometry/geometry -> phase fold -> rotation/physical inference" "Table Mountain lightcurve array, calibration and viewing geometry"
mccasland = round12-science-progress "William Neil McCasland" "fault-tolerant Gramian placement engine" "science-only kernel exposes plant/failure family -> Gramian scoring -> robust placement ranking" "historical beam matrices, candidate locations and failure-family replay"
chavez = round12-science-progress "Anthony Chavez" "LANL DARHT/Scorpius engineering carrier" "science execution remains identity-gated rather than inheriting an uncertain person identity" "after same-person weld, exact Scorpius subsystem geometry/calibration/design responsibility"
thomas = round12-science-progress "Jason R. Thomas" "chemical-biology assay/target-deconvolution finite carrier" "science-only kernel exposes perturbation/readout -> deconvolution -> signalling validation" "one Thomas-authored assay dataset plus direct-target/ferritinophagy validation"
amy = round12-science-progress "Amy Eskridge" "programme-level engineered-gravity mechanism discrimination" "science execution remains authorship-gated; no technical payload manufactured" "Amy-authored/recorded equations, apparatus, deck or reviewed technical manuscript"
ning = round12-science-progress "Ning Li" "Li/Torr theory plus static/rotating YBCO apparatus comparison" "science-only kernel exposes superconducting/regime state -> apparatus/control comparison -> null discriminator" "later AC Gravity/NASA/Army apparatus geometry, drive, calibration and controls"
chen = round12-science-progress "Chen Shuming" "graph-specification hardware verification finite carrier" "science-only kernel exposes graph+stimulus+trace -> conformance/coverage transform" "source graph semantics, stimulus corpus, coverage metric and mismatch example"
feng = round12-science-progress "Feng Yanghe" "Bayesian/noisy-label finite classification carrier" "science-only kernel exposes noisy samples -> classifier -> robust decision output" "one source classifier example with exact equations, noise parameters and outputs"
zhou = round12-science-progress "Zhou Guangyuan" "polyimide-aerogel structure/property source replay" "science-only kernel exposes synthesis/process -> porosity/shrinkage -> thermal response" "multi-sample synthesis-to-property table with uncertainty/process window"
liu = round12-science-progress "Liu Donghao" "DSMM lifecycle/evidence finite assessment carrier" "science-only kernel exposes lifecycle controls/evidence -> maturity scoring" "authored maturity rubric, scoring semantics and source assessed example"
zhangXiaoxin = round12-science-progress "Zhang Xiaoxin" "229-event CEEMDAN-CWT geomagnetic forecast replay" "science-only kernel exposes event time series -> whitening/decomposition/CWT -> forecast output" "exact whitening/CEEMDAN/CWT parameters, precursor rule and runnable data"
zhangDaibing = round12-science-progress "Zhang Daibing" "UAV localisation/guidance/control finite carrier" "science-only kernel exposes sensed vehicle state -> estimation/guidance/control -> tracking/landing output" "one DOI source replay with dynamics, control law, gains, geometry and error series"
liMinyong = round12-science-progress "Li Minyong" "photopharmacology/probe finite carrier" "science-only kernel exposes wavelength+molecule -> photoswitch/binding -> readout/reversibility" "one exact compound/probe wavelength, state fractions, affinity, dose and kinetics"
fang = round12-science-progress "Fang Daining" "inverse-design metamaterial source replay" "science-only kernel exposes design variables+target mode -> energy optimisation -> band/eigenmode output" "full energy functional, unit-cell geometry/constants and band arrays"
yan = round12-science-progress "Yan Hong" "Mach-5 thermal-excitation flow-control replay" "science-only kernel exposes inlet/actuator state -> shock-boundary-layer response transform" "source geometry, heat-source model, mesh/boundaries and response curves"

round12TwentyScientistScienceProgress : List Round12ScienceProgress
round12TwentyScientistScienceProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round12ScientificCohortCount : Nat
round12ScientificCohortCount = 20

round12EveryScientistTouched : Bool
round12EveryScientistTouched = true

round12ScienceOnlyFocus : Bool
round12ScienceOnlyFocus = true

round12ScienceRunnableCount : Nat
round12ScienceRunnableCount = Kernel.scienceRunnableCount

round12ScienceDoesNotPayHistoricalUse : Bool
round12ScienceDoesNotPayHistoricalUse = false

round12ScienceDoesNotPayCustody : Bool
round12ScienceDoesNotPayCustody = false
