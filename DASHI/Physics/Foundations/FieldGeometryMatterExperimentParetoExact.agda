module DASHI.Physics.Foundations.FieldGeometryMatterExperimentParetoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Foundations.GRQFTSequentialExperimentPlannerExact as Sequential

------------------------------------------------------------------------
-- CROSS-DOMAIN EXPERIMENT / ACQUISITION PORTFOLIO
--
-- This is a non-scalar portfolio surface.  Scores are routing coordinates,
-- never truth, authority or physical payment.  The portfolio deliberately
-- points at the strongest remaining SAME-OBJECT experiments instead of adding
-- another ontology layer.
------------------------------------------------------------------------

data ExperimentDomain : Set where
  matbgSameSampleSpectralEntropy : ExperimentDomain
  generalizedCaloricUsefulCycle : ExperimentDomain
  fusionNozzleSameRunMomentumClosure : ExperimentDomain
  precisionThrustIndependentReplication : ExperimentDomain
  quantumStressGravityBackreaction : ExperimentDomain

record ExperimentCandidate : Set where
  constructor experiment-candidate
  field
    domain : ExperimentDomain
    discriminatorReference : String
    sameObjectRequirement : String
    calibrationRequirement : String
    informationGain : Nat
    dependencyClosure : Nat
    residualCoverage : Nat
    provenanceNovelty : Nat
    resourceCost : Nat
    riskOrDifficulty : Nat
    externalProducerRequired : Bool

open ExperimentCandidate public

matbgCandidate : ExperimentCandidate
matbgCandidate =
  experiment-candidate
    matbgSameSampleSpectralEntropy
    "same device: momentum-resolved spectral function plus temperature-dependent chemical potential/entropy under registered local twist and strain"
    "same MATBG region, same valley/layer/sublattice convention, same twist/strain/filling calibration"
    "QTM/PTS energy, momentum, density, temperature and strain calibration"
    5 5 4 5 4 4 true

generalizedCaloricCandidate : ExperimentCandidate
generalizedCaloricCandidate =
  experiment-candidate
    generalizedCaloricUsefulCycle
    "closed control path with directly measured cold-side heat, hot-side heat, work and hysteretic loss"
    "same material/device across every leg of the control cycle"
    "control coordinate, temperature, heat-flow and work calibration"
    5 4 5 4 4 4 true

fusionMomentumCandidate : ExperimentCandidate
fusionMomentumCandidate =
  experiment-candidate
    fusionNozzleSameRunMomentumClosure
    "same-shot plasma state, field solution, boundary momentum flux, coil reaction force, exhaust distribution and thrust"
    "same discharge/run and same engine geometry"
    "density/velocity/distribution, B/E, circuit, force and thrust calibration"
    5 5 5 4 5 5 true

precisionReplicationCandidate : ExperimentCandidate
precisionReplicationCandidate =
  experiment-candidate
    precisionThrustIndependentReplication
    "independent apparatus reproduces calibrated residual after declared nuisance closure and apparatus-change tests"
    "same claimed scaling law and calibrated observable, independent hardware/site"
    "force/displacement, thermal, pressure, outgassing, vibration, EM, facility and sensor calibration"
    5 5 5 5 5 5 true

quantumGravityCandidate : ExperimentCandidate
quantumGravityCandidate =
  experiment-candidate
    quantumStressGravityBackreaction
    "same-object renormalized quantum-stress configuration with an independently measured metric/gravity response"
    "same boundary-conditioned quantum state/stress object and gravity observable"
    "geometry, boundary condition, stress model, force/stress proxy and gravity/metric sensor calibration"
    5 5 5 5 5 5 true

record ExperimentPortfolio : Set where
  constructor experiment-portfolio
  field
    candidates : List ExperimentCandidate
    scoringReference : String
    nonScalarAxesRetained : Bool
    stoppingRuleReference : String

open ExperimentPortfolio public

canonicalExperimentPortfolio : ExperimentPortfolio
canonicalExperimentPortfolio =
  experiment-portfolio
    (matbgCandidate ∷
     generalizedCaloricCandidate ∷
     fusionMomentumCandidate ∷
     precisionReplicationCandidate ∷
     quantumGravityCandidate ∷ [])
    "maximize information gain, dependency closure, residual coverage and provenance novelty while minimizing cost/risk; no scalar collapse is asserted"
    true
    "stop formal abstraction when only external same-object acquisition, calibration, execution or replication can pay the live leaf"

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

candidateCount : ExperimentPortfolio → Nat
candidateCount portfolio = listCount (candidates portfolio)

reusedSequentialPlannerBoundary : Sequential.GRQFTSequentialPlannerBoundary
reusedSequentialPlannerBoundary = Sequential.canonicalGRQFTSequentialPlannerBoundary

record ExperimentParetoBoundary : Set where
  constructor experiment-pareto-boundary
  field
    priorityDoesNotCreateTruth : Bool
    priorityDoesNotCreateAuthority : Bool
    highInformationGainDoesNotCreateSameObjectIdentity : Bool
    lowerCostDoesNotCreateScientificSufficiency : Bool
    sequentialClosureRemainsConsumerRelative : Bool
    externalPaymentCannotBeReplacedByMoreFormalism : Bool
    candidateScoresAreRoutingCoordinatesNotEmpiricalResults : Bool

open ExperimentParetoBoundary public

canonicalExperimentParetoBoundary : ExperimentParetoBoundary
canonicalExperimentParetoBoundary =
  experiment-pareto-boundary true true true true true true true
