module DASHI.Culture.MissingDeceasedTwentyScientistRound10CompositeTraceProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistCompositeReferenceTraceExact as Trace

------------------------------------------------------------------------
-- ROUND 10: COMPOSITE TRACE / ALL-TWENTY PROGRESS
--
-- The two ungated composite applications receive executable reference-trace
-- consumers, while every scientist retains one current science replay leaf and
-- one separate custody/succession leaf.  Trace participation is not historical
-- programme membership.
------------------------------------------------------------------------

record Round10ScientistProgress : Set where
  constructor round10-scientist-progress
  field
    person : String
    currentScienceDepth : String
    round10Delta : String
    participatesInUngatedTrace : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round10ScientistProgress public

nuno = round10-scientist-progress "Nuno F. G. Loureiro"
  "finite/executable KREHM-Hermite-plasmoid machinery"
  "long-duration trace ranks Viriato custody below source replay/qualification because public science can execute independently"
  true
  "source-exact Viriato benchmark initial condition, closure, discretisation and numerical output"
  "repository maintainer, grant reassignment and simulation-state custodian"

leblanc = round10-scientist-progress "Joshua Kyle LeBlanc"
  "source-exact finite FSP environment/sensor carrier"
  "long-duration trace promotes named device qualification/failure evidence to top-tier soft debt"
  true
  "named sensor/device qualification, calibration, failure envelope and autonomous-response evidence"
  "first dated post-loss SNP I&C TechMat roster and handover"

maiwald = round10-scientist-progress "Frank W. Maiwald"
  "source-coordinate action-spectroscopy replay"
  "long-duration trace ranks raw action-spectrum intensities/calibration as the first replay target"
  true
  "raw/supporting ValH+ spectrum intensities, calibration and dissociation-time table"
  "raw/reduced spectra, calibration files, notebooks and SURP handover"

reza = round10-scientist-progress "Monica Jacinto / Monica Reza"
  "finite alloy burn/strength tradeoff plus descendant application lineage"
  "long-duration trace carries the descendant oxygen-service process window as an operating-window debt"
  true
  "source-exact MONDALOY/enamel composition, process and oxygen-service qualification window"
  "Boeing/UTC/Rocketdyne/Aerojet assignment and process-window custodian"

grillmair = round10-scientist-progress "Carl J. Grillmair"
  "executable matched-filter/distance-scan machinery"
  "autonomous-survey trace promotes one real survey slice/filter/orbit uncertainty replay"
  true
  "source catalogue slice, matched-filter weights and orbit-fit uncertainty"
  "stream maps/catalogues/orbit-fit or unfinished-manuscript custodian"

hicks = round10-scientist-progress "Michael David Hicks"
  "finite small-body photometry/phase inference"
  "autonomous-survey trace promotes a calibrated source lightcurve replay"
  true
  "source lightcurve timestamps, magnitudes/errors, viewing geometry and period/phase inference"
  "2022 JPL separation and unfinished observing/reduction/data handover"

mccasland = round10-scientist-progress "William Neil McCasland"
  "executable Gramian placement/failure-family engine"
  "participates in both ungated composite design logic through resilient-structure control; source plant weld remains next"
  true
  "published plant matrices, candidate locations and failure-family objective bound to the executable engine"
  "dated DBE status and 2025-2026 client/programme carrier"

chavez = round10-scientist-progress "Anthony Chavez"
  "science remains identity-gated at LANL DARHT/Scorpius carrier"
  "kept outside ungated trace execution; hard gate remains explicit rather than bypassed"
  false
  "after identity weld, source-exact Scorpius subsystem geometry/calibration/design responsibility"
  "primary same-person weld between missing-person and LANL engineering identities"

thomas = round10-scientist-progress "Jason R. Thomas"
  "finite signalling/target-deconvolution mechanism"
  "retained for the separately gated multi-domain-lab route; science replay still advances independently"
  false
  "Thomas-authored perturbation/readout counts plus direct-target and ferritinophagy validation chain"
  "lab/project/data successor plus final event medical-examiner carrier"

amy = round10-scientist-progress "Amy Eskridge"
  "programme/mechanism-only; technical authorship unresolved"
  "kept outside ungated trace execution; no finite payload manufactured to satisfy the lab composite"
  false
  "Amy-authored/recorded equations, apparatus, deck or reviewed technical manuscript"
  "Amy-linked NF-1676/EDAA/STRIVES object and Institute derivative/handover identity"

ning = round10-scientist-progress "Ning Li"
  "source-exact static-versus-rotating YBCO apparatus comparison"
  "retained for extreme-environment and laboratory routes; later-apparatus continuity remains science replay debt"
  false
  "later AC Gravity/NASA/Army apparatus geometry, controls and calibration comparison"
  "original FY2001 DoD row, Army SOW, closeout/result and apparatus custody"

chen = round10-scientist-progress "Chen Shuming"
  "finite graph-specification hardware-verification mechanism"
  "autonomous-survey trace ranks one source verification example as validation debt"
  true
  "source graph semantics, stimulus corpus, coverage metric and mismatch example"
  "processor-specific responsibility and post-loss technical custodian"

feng = round10-scientist-progress "Feng Yanghe"
  "finite Bayesian/noisy-label classification mechanism"
  "autonomous-survey trace promotes a source classifier replay while keeping War Skull same-object unpaid"
  true
  "source model equations, example data, label-noise parameters and outputs"
  "post-2023 War Skull code/project lead and primary event carrier"

zhou = round10-scientist-progress "Zhou Guangyuan"
  "source-exact SI thermal datum plus finite aerogel process/property witness"
  "long-duration trace ranks a multi-sample source table as the second source-replay target"
  true
  "multi-sample synthesis, shrinkage, porosity, temperature and conductivity table"
  "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"

liu = round10-scientist-progress "Liu Donghao"
  "finite DSMM lifecycle/evidence mechanism"
  "autonomous-survey trace carries authored scoring/assessment semantics as qualification debt"
  true
  "authored maturity levels, clauses, scoring semantics and one assessed example"
  "dated Liu-to-Liao governance transition and DSMM project custody"

zhangXiaoxin = round10-scientist-progress "Zhang Xiaoxin"
  "source replay with 229-event Oulu carrier and source accuracy coordinates"
  "autonomous-survey trace ranks exact CEEMDAN/CWT parameters/code/data as its highest-alpha replay"
  true
  "whitening, CEEMDAN, CWT and precursor parameters plus runnable source code/data"
  "dated NSMC/Fengyun successor and payload/ground-system custody"

zhangDaibing = round10-scientist-progress "Zhang Daibing"
  "finite UAV localisation/guidance/control mechanism"
  "appears in both ungated traces; one source-exact dynamics/control/test replay is now shared high-value validation debt"
  true
  "one DOI's state equations, control law, gains, sensor model, geometry and error series"
  "Yunzhihang/NUDT project and code custodian"

liMinyong = round10-scientist-progress "Li Minyong"
  "finite photoswitch/probe mechanism"
  "retained for laboratory route while exact compound/probe replay remains independently valuable"
  false
  "one exact molecule/probe wavelength, photostationary state, affinity, dose and readout kinetics"
  "post-loss lab/project/patent/student custodian"

fang = round10-scientist-progress "Fang Daining"
  "source replay of inverse-design objective and negative-group-velocity claim"
  "long-duration role is active; full energy/geometry/band arrays remain the executable replacement leaf"
  true
  "full energy functional, unit-cell geometry/material constants and computed/experimental bands"
  "post-loss BIT project/code/IP handover"

yan = round10-scientist-progress "Yan Hong"
  "source replay of Mach-5 thermal-actuator case topology"
  "retained for extreme-environment route; exact response curves remain science replay debt"
  false
  "geometry, mesh/boundaries, heat-source model and shock-angle/separation curves"
  "named NPU flow-control project/code/data successor"

round10TwentyScientistProgress : List Round10ScientistProgress
round10TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round10ScientificCohortCount : Nat
round10ScientificCohortCount = 20

round10UngatedCompositeCount : Nat
round10UngatedCompositeCount = 2

round10HardGatedCompositeCount : Nat
round10HardGatedCompositeCount = 2

round10EveryScientistTouched : Bool
round10EveryScientistTouched = true

round10TraceOwnerPresent : Trace.ungatedCompositeTraceCount ≡ 2
round10TraceOwnerPresent = refl

round10TraceDoesNotPaySourceReplication : Bool
round10TraceDoesNotPaySourceReplication = false

round10TraceDoesNotPayHistoricalUse : Bool
round10TraceDoesNotPayHistoricalUse = false

round10TraceDoesNotPayPersonPossession : Bool
round10TraceDoesNotPayPersonPossession = false

round10TraceCanRefineScienceAndCustodyPareto : Bool
round10TraceCanRefineScienceAndCustodyPareto = true
