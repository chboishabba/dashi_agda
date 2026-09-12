module DASHI.Culture.MissingDeceasedTwentyScientistRound9ReferenceRuntimeProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact as Runtime

------------------------------------------------------------------------
-- ROUND 9: REFERENCE-RUNTIME PROGRESS
-- Every scientist remains live.  Runtime readiness is separated from source
-- replay, qualification, custody, historical deployment and event causation.
------------------------------------------------------------------------

record Round9ScientistProgress : Set where
  constructor round9-scientist-progress
  field
    person : String
    runtimeState : String
    round9Delta : String
    referenceRunnable : Bool
    nextScienceReplayLeaf : String
    nextCustodyLeaf : String

open Round9ScientistProgress public

nuno = round9-scientist-progress "Nuno F. G. Loureiro"
  "finite/executable KREHM-Hermite-plasmoid machinery is reference-runnable"
  "bound into plasma-model runtime slot and composite application planner"
  true
  "source-exact Viriato benchmark initial condition, closure, discretisation and output"
  "repository maintainer, grant reassignment and simulation-state custodian"

leblanc = round9-scientist-progress "Joshua Kyle LeBlanc"
  "source-exact notional FSP environment plus finite sensor/function carrier is reference-runnable"
  "bound into harsh-environment power/control runtime slot"
  true
  "named sensor/device qualification, calibration, failure and response evidence"
  "first dated post-loss SNP I&C TechMat roster and handover"

maiwald = round9-scientist-progress "Frank W. Maiwald"
  "source-replay spectroscopy coordinates are reference-runnable"
  "runtime now distinguishes source replay from missing intensity/calibration arrays"
  true
  "raw/supporting action-spectrum intensity array and dissociation-time/calibration table"
  "raw/reduced spectra, calibration files, notebooks and SURP handover"

reza = round9-scientist-progress "Monica Jacinto / Monica Reza"
  "finite burn-strength/material tradeoff machinery is reference-runnable"
  "bound into oxygen-service materials runtime slot"
  true
  "source-exact MONDALOY/enamel process, composition and qualification window"
  "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custody"

grillmair = round9-scientist-progress "Carl J. Grillmair"
  "executable matched-filter distance-scan machinery is reference-runnable"
  "bound into astronomical-inference runtime slot"
  true
  "source stream catalogue slice, matched-filter weights and orbit-fit uncertainty"
  "stream map/catalogue/orbit-fit or unfinished-manuscript custodian"

hicks = round9-scientist-progress "Michael David Hicks"
  "finite photometry/phase mechanism is reference-runnable"
  "bound into planetary-characterisation runtime slot"
  true
  "source lightcurve timestamps, magnitudes/errors, viewing geometry and period inference"
  "2022 JPL separation and unfinished observing/reduction/data handover"

mccasland = round9-scientist-progress "William Neil McCasland"
  "finite/executable Gramian placement/failure-family engine is reference-runnable"
  "bound into resilient-structure-control runtime slot"
  true
  "source plant matrices, candidate locations and historical failure family"
  "dated DBE status and 2025-2026 client/programme carrier"

chavez = round9-scientist-progress "Anthony Chavez"
  "reference execution remains identity-gated"
  "runtime refuses to inherit LANL/Scorpius technical state across unpaid same-person seam"
  false
  "after identity weld, source-exact Scorpius subsystem geometry/calibration/design responsibility"
  "primary same-person weld between missing-person and LANL engineering identities"

thomas = round9-scientist-progress "Jason R. Thomas"
  "finite signalling/target-deconvolution mechanism is reference-runnable"
  "bound into chemical-biology assay runtime slot"
  true
  "Thomas-authored perturbation/readout counts plus direct-target and ferritinophagy validation"
  "lab/project/data successor plus final event medical-examiner carrier"

amy = round9-scientist-progress "Amy Eskridge"
  "reference execution remains technical-authorship gated"
  "runtime refuses to manufacture a finite Amy science payload from programme adjacency"
  false
  "Amy-authored/recorded equations, apparatus, deck or reviewed technical manuscript"
  "Amy-linked NF-1676/EDAA/STRIVES object and Institute derivative/handover identity"

ning = round9-scientist-progress "Ning Li"
  "source-exact static-versus-rotating apparatus comparison is reference-runnable"
  "bound into precision-force/null-test metrology runtime slot"
  true
  "later AC Gravity/NASA/Army apparatus geometry, controls and calibration comparison"
  "original FY2001 DoD row, Army SOW, closeout/result and apparatus custody"

chen = round9-scientist-progress "Chen Shuming"
  "finite graph-specification verification mechanism is reference-runnable"
  "bound into hardware-verification runtime slot"
  true
  "source graph semantics, stimulus corpus, coverage metric and mismatch example"
  "processor-specific responsibility and post-loss technical custodian"

feng = round9-scientist-progress "Feng Yanghe"
  "finite Bayesian/noisy-label classifier mechanism is reference-runnable"
  "bound into robust-decision-support runtime slot while War Skull seam remains separate"
  true
  "source model equations, sample/noise parameters and one classifier replay"
  "post-2023 War Skull code/project lead and primary event carrier"

zhou = round9-scientist-progress "Zhou Guangyuan"
  "source-exact SI thermal datum plus finite aerogel witness is reference-runnable"
  "bound into thermal-protection runtime slot"
  true
  "multi-sample synthesis/shrinkage/porosity/temperature/conductivity source table"
  "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"

liu = round9-scientist-progress "Liu Donghao"
  "finite DSMM lifecycle/evidence mechanism is reference-runnable"
  "bound into data-security-governance runtime slot"
  true
  "authored maturity levels, clauses, scoring semantics and one assessed example"
  "dated Liu-to-Liao governance transition and DSMM project custody"

zhangXiaoxin = round9-scientist-progress "Zhang Xiaoxin"
  "source-replay forecast coordinates are reference-runnable"
  "runtime preserves 229-event/split/accuracy replay while hyperparameters remain residual"
  true
  "exact whitening, CEEMDAN, CWT, precursor quantisation and runnable code/data"
  "dated NSMC/Fengyun successor and payload/ground-system custody"

zhangDaibing = round9-scientist-progress "Zhang Daibing"
  "finite UAV guidance/localisation/control mechanism is reference-runnable"
  "bound into autonomous-mobility runtime slot"
  true
  "one DOI's dynamics, state, control law, gains, sensor model, geometry and error series"
  "Yunzhihang/NUDT project and code custodian"

liMinyong = round9-scientist-progress "Li Minyong"
  "finite photoswitch/probe mechanism is reference-runnable"
  "bound into photochemical-control runtime slot"
  true
  "one exact molecule/probe wavelength, photostationary state, affinity, dose and readout kinetics"
  "post-loss lab/project/patent/student custodian"

fang = round9-scientist-progress "Fang Daining"
  "source-replay inverse-design coordinates are reference-runnable"
  "runtime preserves source design objective/negative-group-velocity claim while arrays remain residual"
  true
  "full energy functional, unit-cell geometry/material constants and computed/experimental bands"
  "post-loss BIT project/code/IP handover"

yan = round9-scientist-progress "Yan Hong"
  "source-replay Mach-5 thermal-actuator cases are reference-runnable"
  "runtime preserves source case topology/ordering while response curves remain residual"
  true
  "geometry, mesh/boundaries, heat-source model and shock-angle/separation curves"
  "named NPU flow-control project/code/data successor"

round9TwentyScientistProgress : List Round9ScientistProgress
round9TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round9ScientificCohortCount : Nat
round9ScientificCohortCount = 20

round9ReferenceRunnableCount : Nat
round9ReferenceRunnableCount = 18

round9GatedCount : Nat
round9GatedCount = 2

round9EveryScientistTouched : Bool
round9EveryScientistTouched = true

runtimeExecutionDoesNotPaySourceReplay : Bool
runtimeExecutionDoesNotPaySourceReplay = false

runtimeExecutionDoesNotPayHistoricalUse : Bool
runtimeExecutionDoesNotPayHistoricalUse = false

runtimeExecutionDoesNotPayPersonPossession : Bool
runtimeExecutionDoesNotPayPersonPossession = false

runtimeExecutionCanRefineReverseAcquisition : Bool
runtimeExecutionCanRefineReverseAcquisition = true
