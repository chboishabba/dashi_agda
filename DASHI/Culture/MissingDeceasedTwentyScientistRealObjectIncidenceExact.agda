module DASHI.Culture.MissingDeceasedTwentyScientistRealObjectIncidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.RealObjectApplicationBidiExact as R

------------------------------------------------------------------------
-- ALL-20 SCIENTIST × REAL-OBJECT INCIDENCE MATRIX
--
-- The matrix asks which already-source-backed science fibres can fit four
-- independently meaningful engineering/research objects.  It is intentionally
-- sparse: noFit and analogyOnly are evidence against forcing one machine to
-- consume all twenty fibres.
------------------------------------------------------------------------

record RealObjectIncidenceRow : Set where
  constructor real-object-incidence-row
  field
    person : String
    combinedRocketScramjet : R.FitStrength
    spaceFissionPlatform : R.FitStrength
    highEnergyFacility : R.FitStrength
    molecularBiologyPlatform : R.FitStrength
    strongestObjectInterpretation : String
    nextQualificationLeaf : String

open RealObjectIncidenceRow public

nuno : RealObjectIncidenceRow
nuno = real-object-incidence-row "Nuno F. G. Loureiro"
  R.analogyOnly R.methodTransfer R.methodTransfer R.noFit
  "plasma/reconnection modelling fits plasma-rich space or high-energy research environments as a method, not as a specific vehicle component"
  "bind KREHM/Viriato variables to one sourced application geometry and validation dataset"

leblanc : RealObjectIncidenceRow
leblanc = real-object-incidence-row "Joshua Kyle LeBlanc"
  R.methodTransfer R.directSourceFit R.methodTransfer R.noFit
  "Fission Surface Power I&C is a direct space/fission platform fit; other control uses require transfer"
  "recover exact I&C gap/qualification matrix and post-loss TechMat handoff"

maiwald : RealObjectIncidenceRow
maiwald = real-object-incidence-row "Frank W. Maiwald"
  R.noFit R.analogyOnly R.methodTransfer R.directSourceFit
  "tagged-ion action spectroscopy is directly a molecular-diagnostics platform technology"
  "recover raw spectrum, calibration, dissociation-time arrays and sample-interface constraints"

reza : RealObjectIncidenceRow
reza = real-object-incidence-row "Monica Jacinto / Monica Reza"
  R.directSourceFit R.engineeringTransfer R.engineeringTransfer R.noFit
  "oxygen-service alloy/process lineage fits rocket-side severe oxidizer service directly and transfers to other extreme environments only after qualification"
  "recover component-specific process window, fatigue/oxidation lifecycle and pre-2013 programme identifiers"

grillmair : RealObjectIncidenceRow
grillmair = real-object-incidence-row "Carl J. Grillmair"
  R.noFit R.analogyOnly R.noFit R.noFit
  "stellar-stream inference is mission/payload science rather than a required subsystem of the current four objects"
  "add a separately sourced astronomical-survey/space-observatory object before promoting fit"

hicks : RealObjectIncidenceRow
hicks = real-object-incidence-row "Michael David Hicks"
  R.noFit R.analogyOnly R.noFit R.noFit
  "small-body photometry is mission/payload science rather than a propulsion/power/laboratory subsystem"
  "add a planetary-survey/observatory object with calibrated lightcurve geometry"

mccasland : RealObjectIncidenceRow
mccasland = real-object-incidence-row "William Neil McCasland"
  R.methodTransfer R.methodTransfer R.methodTransfer R.noFit
  "fault-tolerant controllability/observability placement is a reusable system-control method"
  "instantiate one source-exact plant, candidate placement set and failure family per object"

chavez : RealObjectIncidenceRow
chavez = real-object-incidence-row "Anthony Chavez"
  R.noFit R.noFit R.directSourceFit R.noFit
  "DARHT/Scorpius engineering fits the high-energy experimental-facility class once identity is welded"
  "first pay missing-person/LANL same-person identity, then exact subsystem task identifiers"

thomas : RealObjectIncidenceRow
thomas = real-object-incidence-row "Jason R. Thomas"
  R.noFit R.noFit R.noFit R.directSourceFit
  "cell-signalling and ferritinophagy assay science directly fits a molecular/chemical-biology research platform"
  "recover supporting-information matrices, dose response and target-validation chain"

amy : RealObjectIncidenceRow
amy = real-object-incidence-row "Amy Eskridge"
  R.analogyOnly R.noFit R.analogyOnly R.noFit
  "mechanism-discrimination programme material can motivate precision null-test requirements but technical authorship remains gated"
  "recover an Amy-authored/recorded technical object and exact apparatus/review identifier"

ning : RealObjectIncidenceRow
ning = real-object-incidence-row "Ning Li"
  R.analogyOnly R.noFit R.directSourceFit R.noFit
  "published YBCO gravity experiments directly fit a precision anomalous-force test facility, with negative/null constraints retained"
  "recover later apparatus/calibration plus Army DAAH01-01-9-R001 SOW/closeout"

chen : RealObjectIncidenceRow
chen = real-object-incidence-row "Chen Shuming"
  R.methodTransfer R.methodTransfer R.methodTransfer R.noFit
  "graph-based hardware verification transfers to complex digital control/instrumentation systems"
  "instantiate one exact hardware graph/specification/stimulus/coverage corpus"

feng : RealObjectIncidenceRow
feng = real-object-incidence-row "Feng Yanghe"
  R.analogyOnly R.analogyOnly R.analogyOnly R.noFit
  "Bayesian/noisy-label decision methods are broadly relevant but no low-invention subsystem interface is yet sourced"
  "recover one exact algorithm/equation/dataset and a sourced object requirement before promotion"

zhou : RealObjectIncidenceRow
zhou = real-object-incidence-row "Zhou Guangyuan"
  R.engineeringTransfer R.engineeringTransfer R.engineeringTransfer R.noFit
  "high-temperature lightweight polyimide-aerogel science transfers to thermal-management/insulation roles after environment-specific qualification"
  "recover complete process/property table and object-specific cycling/erosion/vacuum qualification"

liu : RealObjectIncidenceRow
liu = real-object-incidence-row "Liu Donghao"
  R.analogyOnly R.methodTransfer R.methodTransfer R.methodTransfer
  "DSMM/data-governance methods fit research and critical-system data lifecycles but are not physical subsystem mechanisms"
  "recover exact assessment rubric and instantiate one object-specific lifecycle/control/evidence map"

zhangXiaoxin : RealObjectIncidenceRow
zhangXiaoxin = real-object-incidence-row "Zhang Xiaoxin"
  R.analogyOnly R.directSourceFit R.noFit R.noFit
  "geomagnetic forecasting and Fengyun science directly fit a space-environment observation/prediction role"
  "recover event-level data, full hyperparameters and payload/calibration interface"

zhangDaibing : RealObjectIncidenceRow
zhangDaibing = real-object-incidence-row "Zhang Daibing"
  R.methodTransfer R.methodTransfer R.analogyOnly R.noFit
  "guidance/localisation/control methods transfer to autonomous aerospace/space vehicles with new dynamics and qualification"
  "recover one exact vehicle model, gains, disturbances and test time series"

liMinyong : RealObjectIncidenceRow
liMinyong = real-object-incidence-row "Li Minyong"
  R.noFit R.noFit R.noFit R.directSourceFit
  "photopharmacology/probe science directly fits a controlled molecular-biology research platform"
  "recover one exact molecule wavelength-state-binding-readout-kinetics replay"

fang : RealObjectIncidenceRow
fang = real-object-incidence-row "Fang Daining"
  R.engineeringTransfer R.engineeringTransfer R.engineeringTransfer R.noFit
  "extreme-environment mechanics/metamaterial inverse-design transfers to qualified structures and test infrastructure"
  "recover energy functional, unit-cell geometry, band data and object-specific load/temperature qualification"

yan : RealObjectIncidenceRow
yan = real-object-incidence-row "Yan Hong"
  R.directSourceFit R.analogyOnly R.analogyOnly R.noFit
  "Mach-5 inlet thermal-excitation/SBLI control directly fits the airbreathing hypersonic object"
  "recover exact mesh, heat-source model, response curves and integrated inlet qualification"

twentyScientistRealObjectIncidence : List RealObjectIncidenceRow
twentyScientistRealObjectIncidence =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

realObjectIncidenceScientistCount : Nat
realObjectIncidenceScientistCount = 20

incidenceFitPaysHistoricalParticipation : Bool
incidenceFitPaysHistoricalParticipation = false

incidenceFitPaysH2 : Bool
incidenceFitPaysH2 = false

incidenceFitPaysH3 : Bool
incidenceFitPaysH3 = false

noFitIsValidIncidenceEvidence : Bool
noFitIsValidIncidenceEvidence = true

singleMachineMustConsumeAllTwenty : Bool
singleMachineMustConsumeAllTwenty = false
