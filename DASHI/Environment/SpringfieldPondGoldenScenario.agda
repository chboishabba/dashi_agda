module DASHI.Environment.SpringfieldPondGoldenScenario where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using ([]; _∷_)

import DASHI.Environment.FunctionalEcology as Eco
import DASHI.Environment.InversePlanning as Planning
import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Environment.QuantitiesConservation as Q
import DASHI.Environment.SpatialTransport as Spatial
import DASHI.Environment.SurrogateCalibration as Surrogate
import DASHI.Foundations.SSPTritCarrier as SSP

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

------------------------------------------------------------------------
-- Spatial skeleton.

upperCatchment : Spatial.SpatialNode
upperCatchment =
  Spatial.mkSpatialNode
    "springfield-upper-catchment"
    Spatial.catchment
    "scenario CRS"
    "gis://catchment/upper"
    "golden-scenario fixture"

stormwaterReach : Spatial.SpatialNode
stormwaterReach =
  Spatial.mkSpatialNode
    "springfield-stormwater-reach"
    Spatial.streamReach
    "scenario CRS"
    "gis://drainage/reach-1"
    "golden-scenario fixture"

pond : Spatial.SpatialNode
pond =
  Spatial.mkSpatialNode
    "springfield-pond"
    Spatial.waterbody
    "scenario CRS"
    "gis://waterbody/pond"
    "golden-scenario fixture"

window : Spatial.TimeWindow
window = Spatial.mkTimeWindow zero three Data.Nat.z≤n

catchmentToDrain : Spatial.TransportEdge upperCatchment stormwaterReach
catchmentToDrain =
  Spatial.mkTransportEdge
    Spatial.dissolvedPhosphorus
    window
    true
    true
    "fixture flow-direction evidence"
    "fixture uncertainty"

drainToPond : Spatial.TransportEdge stormwaterReach pond
drainToPond =
  Spatial.mkTransportEdge
    Spatial.dissolvedPhosphorus
    window
    true
    true
    "fixture inlet evidence"
    "fixture uncertainty"

phosphorusPath : Spatial.Path upperCatchment pond
phosphorusPath = Spatial.step catchmentToDrain (Spatial.step drainToPond Spatial.here)

sourceSupport : Spatial.SpatialSupport upperCatchment pond
sourceSupport =
  Spatial.mkSpatialSupport
    phosphorusPath
    "upper catchment land-use footprint"
    "pond observation footprint"
    true

sourceToPond : Spatial.SourceToObservationWitness upperCatchment pond
sourceToPond =
  Spatial.mkSourceToObservationWitness
    sourceSupport
    Spatial.dissolvedPhosphorus
    "rainfall event precedes observed load"
    true
    true
    ("golden scenario transport witness" ∷ [])

------------------------------------------------------------------------
-- Functional groups and candidate interventions.

pondweedGroup : Eco.FunctionalGroup
pondweedGroup =
  Eco.mkFunctionalGroup
    "submerged nuisance macrophyte"
    (Eco.producer ∷ Eco.habitatProvider ∷ [])

floatingWetlandGroup : Eco.FunctionalGroup
floatingWetlandGroup =
  Eco.mkFunctionalGroup
    "floating planted wetland guild"
    (Eco.aquaticFilter ∷ Eco.nutrientScavenger ∷ Eco.habitatProvider ∷ [])

riparianGroup : Eco.FunctionalGroup
riparianGroup =
  Eco.mkFunctionalGroup
    "riparian nutrient interception guild"
    (Eco.riparianStabiliser ∷ Eco.nutrientScavenger ∷ Eco.habitatProvider ∷ [])

openContext : Eco.ContextGate
openContext = Eco.mkContextGate true true true true true true

floatingReducesAvailableNutrients : Eco.Interaction
floatingReducesAvailableNutrients =
  Eco.mkInteraction
    floatingWetlandGroup
    pondweedGroup
    SSP.sspNegOne
    openContext
    two
    "candidate nutrient-competition effect"

bufferReducesCatchmentLoad : Eco.Interaction
bufferReducesCatchmentLoad =
  Eco.mkInteraction
    riparianGroup
    pondweedGroup
    SSP.sspNegOne
    openContext
    two
    "candidate upstream nutrient-interception effect"

floatingPlanter : Eco.Intervention
floatingPlanter =
  Eco.mkIntervention
    "floating planted wetland trial"
    Eco.floatingPlanter
    (floatingWetlandGroup ∷ pondweedGroup ∷ [])
    (floatingReducesAvailableNutrients ∷ [])
    two
    Latent.pathB-latent
    true

upstreamBuffer : Eco.Intervention
upstreamBuffer =
  Eco.mkIntervention
    "upstream vegetated buffer"
    Eco.riparianBuffer
    (riparianGroup ∷ pondweedGroup ∷ [])
    (bufferReducesCatchmentLoad ∷ [])
    two
    Latent.pathB-latent
    true

mechanicalRemoval : Eco.Intervention
mechanicalRemoval =
  Eco.mkIntervention
    "mechanical pondweed removal"
    Eco.mechanicalRemoval
    (pondweedGroup ∷ [])
    []
    one
    Latent.pathA-screening
    true

------------------------------------------------------------------------
-- Source hypothesis and planning candidates.

nutrientObservation : Planning.Observation
nutrientObservation =
  Planning.mkObservation
    "elevated pond nutrient availability"
    "springfield-pond"
    "fixture wet season"
    SSP.sspPosOne
    two
    one

catchmentNutrientGroup : Eco.FunctionalGroup
catchmentNutrientGroup =
  Eco.mkFunctionalGroup
    "catchment nutrient export"
    (Eco.producer ∷ [])

upstreamLossHypothesis : Planning.SourceHypothesis
upstreamLossHypothesis =
  Planning.mkSourceHypothesis
    "upstream nutrient loss"
    "springfield-upper-catchment"
    catchmentNutrientGroup
    true
    true
    true
    one

upstreamExplanation : Planning.Explanation
upstreamExplanation =
  Planning.mkExplanation
    upstreamLossHypothesis
    nutrientObservation
    SSP.sspPosOne
    one
    one
    one
    Latent.pathB-latent
    ("typed source-to-observation path" ∷ [])

waterObjective : Planning.Objective
waterObjective =
  Planning.mkObjective
    "reduce nutrient availability and recurrent pondweed pressure"
    Planning.nutrientRetention
    SSP.sspPosOne
    three
    true

humanReview : Planning.Constraint
humanReview =
  Planning.mkConstraint
    "engineering ecological and community review"
    true
    true
    "golden scenario remains non-deployment fixture"

combinedPlan : Planning.Plan
combinedPlan =
  Planning.mkPlan
    "upstream buffer plus floating wetland trial"
    (upstreamBuffer ∷ floatingPlanter ∷ [])
    (waterObjective ∷ [])
    (humanReview ∷ [])
    Latent.pathB-latent
    one
    two
    two
    one

mechanicalOnlyPlan : Planning.Plan
mechanicalOnlyPlan =
  Planning.mkPlan
    "mechanical removal only"
    (mechanicalRemoval ∷ [])
    (waterObjective ∷ [])
    (humanReview ∷ [])
    Latent.pathA-screening
    three
    one
    one
    two

------------------------------------------------------------------------
-- Conservation and escalation fixtures.

zeroConservation : Q.ConservationBundle
zeroConservation =
  Q.mkConservationBundle
    (Q.exactZeroBalance "pond water fixture")
    (Q.exactZeroBalance "pond nitrogen fixture")
    (Q.exactZeroBalance "pond phosphorus fixture")
    (Q.exactZeroBalance "pond carbon fixture")
    (Q.exactZeroBalance "pond sediment fixture")
    true
    true

policyAssessment : Surrogate.SurrogateAssessment
policyAssessment =
  Surrogate.mkSurrogateAssessment
    true
    one
    two
    (Data.Nat.s≤s Data.Nat.z≤n)
    one
    two
    (Data.Nat.s≤s Data.Nat.z≤n)
    true
    true

policyEscalates :
  Latent.chooseLane
    Latent.pathB-latent
    (Surrogate.assessmentEscalation policyAssessment)
  ≡ Latent.pathC-authoritative
policyEscalates = refl

------------------------------------------------------------------------
-- Golden-scenario output contract.

record SpringfieldPondGoldenScenario : Set where
  constructor mkSpringfieldPondGoldenScenario
  field
    transportWitness : Spatial.SourceToObservationWitness upperCatchment pond
    rankedSourceCandidate : Planning.Explanation
    candidatePlans : Data.List.Base.List Planning.Plan
    conservationBundle : Q.ConservationBundle
    selectedPlanReceipt : Planning.PlanningReceipt
    policyCriticalEscalationChecked :
      Latent.chooseLane
        Latent.pathB-latent
        (Surrogate.assessmentEscalation policyAssessment)
      ≡ Latent.pathC-authoritative
    gisOutputContract : Data.List.Base.List Agda.Builtin.String.String
    provenance : Data.List.Base.List Agda.Builtin.String.String
open SpringfieldPondGoldenScenario public

canonicalSpringfieldPondGoldenScenario : SpringfieldPondGoldenScenario
canonicalSpringfieldPondGoldenScenario =
  mkSpringfieldPondGoldenScenario
    sourceToPond
    upstreamExplanation
    (combinedPlan ∷ mechanicalOnlyPlan ∷ [])
    zeroConservation
    (Planning.canonicalScreeningReceipt combinedPlan)
    policyEscalates
    ("source hypotheses layer" ∷ "candidate interventions layer" ∷ "uncertainty layer" ∷ [])
    ("synthetic fixture only; replace with audited Springfield datasets" ∷ [])
