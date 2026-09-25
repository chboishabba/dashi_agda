module DASHI.Cognition.PNF.IntegrativeComplexityDifferentiationIntegrationExact where

------------------------------------------------------------------------
-- INTEGRATIVE COMPLEXITY AS OBSERVER, NOT FINE ONTOLOGY
--
-- DASHI CONTRIBUTION
--
-- The psychological literature motivates differentiation and integration as
-- distinct dimensions and commonly scores discourse on a 1..7 scale.  This
-- module uses a finite 1..7 observation interface while retaining relational
-- context/order/residual beneath it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

data ICScore : Set where
  ic1 ic2 ic3 ic4 ic5 ic6 ic7 : ICScore

data Differentiation : Set where
  undifferentiated : Differentiation
  differentiated : Differentiation

data Integration : Set where
  unintegrated : Integration
  integrated : Integration

record RelationalIntegrationState : Set where
  constructor relational-integration-state
  field
    differentiation : Differentiation
    integration : Integration
    relationContext : String
    orderResidual : String
    selfPositionRetained : Bool
    otherIrreducibilityRetained : Bool
    newAffordanceReceipt : String

open RelationalIntegrationState public

data ICObservationEpisode : Set where
  sameScoreDifferentResidualA : ICObservationEpisode
  sameScoreDifferentResidualB : ICObservationEpisode
  lowDifferentiationEpisode : ICObservationEpisode
  highDifferentiationEpisode : ICObservationEpisode

icObserved : ICObservationEpisode → ICScore
icObserved sameScoreDifferentResidualA = ic5
icObserved sameScoreDifferentResidualB = ic5
icObserved lowDifferentiationEpisode = ic2
icObserved highDifferentiationEpisode = ic5

fineResidual : ICObservationEpisode → Bool
fineResidual sameScoreDifferentResidualA = false
fineResidual sameScoreDifferentResidualB = true
fineResidual lowDifferentiationEpisode = false
fineResidual highDifferentiationEpisode = true

sameICScore :
  icObserved sameScoreDifferentResidualA
  ≡ icObserved sameScoreDifferentResidualB
sameICScore = refl

differentFineResidual :
  fineResidual sameScoreDifferentResidualA
  ≡ fineResidual sameScoreDifferentResidualB →
  ⊥
differentFineResidual ()

icScoreFineStateWitness :
  Descent.ConsumerNonDescentWitness icObserved fineResidual
icScoreFineStateWitness =
  Descent.consumerNonDescentWitness
    sameScoreDifferentResidualA
    sameScoreDifferentResidualB
    sameICScore
    differentFineResidual

fineResidualDoesNotFactorThroughICScore :
  Descent.FactorsThrough icObserved fineResidual → ⊥
fineResidualDoesNotFactorThroughICScore =
  Descent.nonDescentWitnessBlocksFactorization icScoreFineStateWitness

record DifferentiationIntegrationIndependence : Set where
  constructor differentiation-integration-independence
  field
    lowLow : Differentiation × Integration
    highLow : Differentiation × Integration
    lowHigh : Differentiation × Integration
    highHigh : Differentiation × Integration

canonicalDifferentiationIntegrationIndependence :
  DifferentiationIntegrationIndependence
canonicalDifferentiationIntegrationIndependence =
  differentiation-integration-independence
    (undifferentiated , unintegrated)
    (differentiated , unintegrated)
    (undifferentiated , integrated)
    (differentiated , integrated)

record IntegrativeComplexityBoundary : Set where
  constructor integrative-complexity-boundary
  field
    differentiationEqualsIntegration : Bool
    scoreIsFineOntology : Bool
    scoreRecoversHistoricalResidual : Bool
    scoreMayServeAsDeclaredObserver : Bool

canonicalIntegrativeComplexityBoundary : IntegrativeComplexityBoundary
canonicalIntegrativeComplexityBoundary =
  integrative-complexity-boundary false false false true
