module DASHI.Chemistry.MechanismDiscriminationCoreBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.MechanismModelDiscriminationExact as Core
import DASHI.Chemistry.MechanismDiscriminationExact as Chemistry

------------------------------------------------------------------------
-- CHEMISTRY -> DOMAIN-NEUTRAL MODEL-DISCRIMINATION BRIDGE
------------------------------------------------------------------------

toCoreDirection : Chemistry.PredictionDirection → Core.QualitativeDirection
toCoreDirection Chemistry.stronglyDown = Core.stronglyDown
toCoreDirection Chemistry.down = Core.down
toCoreDirection Chemistry.unchanged = Core.unchanged
toCoreDirection Chemistry.up = Core.up
toCoreDirection Chemistry.stronglyUp = Core.stronglyUp
toCoreDirection Chemistry.unresolved = Core.unresolvedDirection

toCoreResidualClass : Chemistry.ResidualStatus → Core.ResidualClass
toCoreResidualClass Chemistry.consistent = Core.consistent
toCoreResidualClass Chemistry.tension = Core.tension
toCoreResidualClass Chemistry.discriminating = Core.discriminating
toCoreResidualClass Chemistry.falsified = Core.falsified
toCoreResidualClass Chemistry.unresolvedResidual = Core.unresolvedResidual

toCoreHypothesis : Chemistry.MechanismHypothesis → Core.ModelHypothesis
toCoreHypothesis hypothesis =
  Core.modelHypothesis
    (Chemistry.hypothesisId hypothesis)
    (Chemistry.mechanismFamily hypothesis)
    (Chemistry.requiredCarrier hypothesis)
    (Chemistry.excludedShortcut hypothesis)

toCoreObservable : Chemistry.ObservableCoordinate → Core.ObservableCoordinate
toCoreObservable observable =
  Core.observableCoordinate
    (Chemistry.observableId observable)
    (Chemistry.measurementReference observable)
    (Chemistry.assayContext observable)

toCorePrediction : Chemistry.PredictedCoordinate → Core.PredictedObservation
toCorePrediction prediction =
  Core.predictedObservation
    (toCoreHypothesis (Chemistry.hypothesis prediction))
    (toCoreObservable (Chemistry.observable prediction))
    (toCoreDirection (Chemistry.predictedDirection prediction))
    (Chemistry.predictionBasis prediction)
    (Chemistry.targetSystemValidated prediction)

toCoreObservation : Chemistry.ObservedCoordinate → Core.ObservedEvidence
toCoreObservation observation =
  Core.observedEvidence
    (toCoreObservable (Chemistry.observable observation))
    (toCoreDirection (Chemistry.observedDirection observation))
    (Chemistry.measurementSource observation)
    (Chemistry.protocolValidated observation)

toCoreResidual : Chemistry.ModelResidual → Core.ModelResidual
toCoreResidual residual =
  Core.modelResidual
    (toCorePrediction (Chemistry.prediction residual))
    (toCoreObservation (Chemistry.observation residual))
    (toCoreResidualClass (Chemistry.status residual))
    (Chemistry.residualInterpretation residual)

toCoreReopenDirective : Chemistry.ReopenTarget → Core.ReopenDirective
toCoreReopenDirective target =
  Core.reopenDirective
    (toCoreHypothesis (Chemistry.hypothesis target))
    (Chemistry.reopenedCarrier target)
    (Chemistry.reopenedCarrier target)
    (Chemistry.reopenedObligation target)
    (Chemistry.reason target)

record ChemistryCoreDiscriminationBridgeBoundary : Set where
  constructor chemistryCoreDiscriminationBridgeBoundary
  field
    chemistryResidualsCanEnterGenericCore : Bool
    chemistryResidualsCanEnterGenericCoreIsTrue :
      chemistryResidualsCanEnterGenericCore ≡ true

    genericCoreReplacesChemistryEvidenceSemantics : Bool
    genericCoreReplacesChemistryEvidenceSemanticsIsFalse :
      genericCoreReplacesChemistryEvidenceSemantics ≡ false

    domainSpecificPredictionBasisRemainsExplicit : Bool
    domainSpecificPredictionBasisRemainsExplicitIsTrue :
      domainSpecificPredictionBasisRemainsExplicit ≡ true

canonicalChemistryCoreDiscriminationBridgeBoundary :
  ChemistryCoreDiscriminationBridgeBoundary
canonicalChemistryCoreDiscriminationBridgeBoundary =
  chemistryCoreDiscriminationBridgeBoundary true refl false refl true refl
