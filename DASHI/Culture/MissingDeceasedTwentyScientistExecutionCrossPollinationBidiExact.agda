module DASHI.Culture.MissingDeceasedTwentyScientistExecutionCrossPollinationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B

------------------------------------------------------------------------
-- EXECUTION CROSS-POLLINATION BIDI
--
-- This layer does not claim that the scientists collaborated, shared a
-- programme, or used each other's methods.  It reuses DASHI implementation
-- patterns across already-attributed science fibres.  Each binding records
-- the reusable in-repo machinery and the source-specific debt that prevents
-- that reuse from being promoted into a source reproduction.
------------------------------------------------------------------------

data CrossPollinationKind : Set where
  manifestMaterialization : CrossPollinationKind
  finiteDataReplay : CrossPollinationKind
  nullComparison : CrossPollinationKind
  frozenInferenceReplay : CrossPollinationKind
  finiteFailureReplay : CrossPollinationKind
  processPropertyReplay : CrossPollinationKind

record CrossPollinationBinding : Set where
  constructor cross-pollination-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    kind : CrossPollinationKind
    sourceOwnedScience : String
    reusedInRepoMachinery : String
    newlyEnabled : String
    reverseSourceDebt : String

open CrossPollinationBinding public

zhangBinding : CrossPollinationBinding
zhangBinding = cross-pollination-binding
  "Zhang Xiaoxin" B.zhangXiaoxinFibre manifestMaterialization
  "public CEEMDAN-CWT forecast data/code deposits"
  "public-producer -> materialization -> integrity -> parse -> execution ladder"
  "source producer can now be routed through a typed execution-state machine"
  "local bytes, MD5 verification, MAT schemas, code dependencies, event-output comparison"

maiwaldBinding : CrossPollinationBinding
maiwaldBinding = cross-pollination-binding
  "Frank W. Maiwald" B.frankMaiwaldFibre finiteDataReplay
  "ValH+ action spectroscopy plus located ACS Supporting Information manifest"
  "same manifest/integrity/parse separation used by Zhang public-producer lane"
  "SI tables can be treated as finite data products rather than narrative metadata"
  "materialized SI bytes, table parse, measured intensity/calibration arrays and dissociation-time replay"

ningBinding : CrossPollinationBinding
ningBinding = cross-pollination-binding
  "Ning Li" B.ningLiFibre nullComparison
  "source-exact static and rotating YBCO negative-result apparatus coordinates"
  "query-indexed comparison and null-result witness discipline from existing DASHI inference machinery"
  "apparatus variants can be compared without promoting absence-of-effect into universal impossibility"
  "later AC Gravity/Army same-object apparatus, calibration, controls, raw measurements and closeout"

zhouBinding : CrossPollinationBinding
zhouBinding = cross-pollination-binding
  "Zhou Guangyuan" B.zhouGuangyuanFibre processPropertyReplay
  "source-exact PI-D1/PI-A4 aerogel process/property coordinates"
  "finite SI measurement witnesses plus source-data replay/materialization ladder"
  "named samples can become a typed process -> structure -> property table rather than isolated constants"
  "complete multi-sample recipe, uncertainty, thermal curve and scale-up process window"

grillmairBinding : CrossPollinationBinding
grillmairBinding = cross-pollination-binding
  "Carl J. Grillmair" B.carlGrillmairFibre frozenInferenceReplay
  "matched-filter stellar-stream distance-scan/orbit inference"
  "Fly-style select/freeze/held-out discipline plus existing matched-filter executable machinery"
  "catalogue/filter/orbit replay can keep filter selection separate from evaluation and uncertainty"
  "exact catalogue slice, colour-magnitude filter weights, distance grid, orbit inputs and uncertainty output"

mccaslandBinding : CrossPollinationBinding
mccaslandBinding = cross-pollination-binding
  "William Neil McCasland" B.williamNeilMcCaslandFibre finiteFailureReplay
  "fault-tolerant Gramian sensor/actuator placement over failure families"
  "requirement-closed finite-family enumeration from NDim/RSA plus existing McCasland finite engine"
  "historical plant parameters can feed the existing exhaustive failure-family compiler without a new planner"
  "published plant matrices, candidate sensor/actuator sites, failure family and benchmark placements"

crossPollinationBindings : List CrossPollinationBinding
crossPollinationBindings =
  zhangBinding ∷ maiwaldBinding ∷ ningBinding ∷ zhouBinding ∷ grillmairBinding ∷ mccaslandBinding ∷ []

crossPollinationBindingsCount : Nat
crossPollinationBindingsCount = 6

crossPollinationReusesExistingMachinery : Bool
crossPollinationReusesExistingMachinery = true

crossPollinationDoesNotPayHistoricalDeployment : Bool
crossPollinationDoesNotPayHistoricalDeployment = false

crossPollinationDoesNotPayCommonProgramme : Bool
crossPollinationDoesNotPayCommonProgramme = false

crossPollinationDoesNotPayCustody : Bool
crossPollinationDoesNotPayCustody = false

crossPollinationDoesNotPaySourceReproduction : Bool
crossPollinationDoesNotPaySourceReproduction = false
