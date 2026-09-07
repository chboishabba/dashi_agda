module DASHI.Chemistry.MechanismDiscriminationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Core
import DASHI.Chemistry.TransitionKernel as TK

------------------------------------------------------------------------
-- CHEMISTRY-SPECIALISED MECHANISM DISCRIMINATION
--
-- This owner keeps chemistry's TransitionKernel experiment-selection carrier
-- and domain terminology while explicitly consuming the domain-neutral Core
-- model-discrimination boundary.  The reciprocal adapter back into Core lives
-- in MechanismDiscriminationCoreBridgeExact.
------------------------------------------------------------------------

data PredictionDirection : Set where
  stronglyDown : PredictionDirection
  down : PredictionDirection
  unchanged : PredictionDirection
  up : PredictionDirection
  stronglyUp : PredictionDirection
  unresolved : PredictionDirection

data ResidualStatus : Set where
  consistent : ResidualStatus
  tension : ResidualStatus
  discriminating : ResidualStatus
  falsified : ResidualStatus
  unresolvedResidual : ResidualStatus

record ObservableCoordinate : Set where
  constructor observableCoordinate
  field
    observableId : String
    measurementReference : String
    assayContext : String

open ObservableCoordinate public

record MechanismHypothesis : Set where
  constructor mechanismHypothesis
  field
    hypothesisId : String
    mechanismFamily : String
    requiredCarrier : String
    excludedShortcut : String

open MechanismHypothesis public

record PredictedCoordinate : Set where
  constructor predictedCoordinate
  field
    hypothesis : MechanismHypothesis
    observable : ObservableCoordinate
    predictedDirection : PredictionDirection
    predictionBasis : String
    targetSystemValidated : Bool

open PredictedCoordinate public

record ObservedCoordinate : Set where
  constructor observedCoordinate
  field
    observable : ObservableCoordinate
    observedDirection : PredictionDirection
    measurementSource : String
    protocolValidated : Bool

open ObservedCoordinate public

record ModelResidual : Set where
  constructor modelResidual
  field
    prediction : PredictedCoordinate
    observation : ObservedCoordinate
    status : ResidualStatus
    residualInterpretation : String

open ModelResidual public

record DiscriminationPanel : Set where
  constructor discriminationPanel
  field
    hypotheses : List MechanismHypothesis
    observables : List ObservableCoordinate
    predictions : List PredictedCoordinate
    experimentSelection : TK.ExperimentSelection
    sameExposurePanel : Bool
    sameExposurePanelValidated : Bool

open DiscriminationPanel public

record ReopenTarget : Set where
  constructor reopenTarget
  field
    hypothesis : MechanismHypothesis
    reopenedCarrier : String
    reopenedObligation : String
    reason : String

open ReopenTarget public

record DiscriminationBoundary : Set where
  constructor discriminationBoundary
  field
    oneMatchingObservableProvesMechanism : Bool
    oneMatchingObservableProvesMechanismIsFalse :
      oneMatchingObservableProvesMechanism ≡ false

    oneContradictoryObservableAlwaysFalsifiesMechanism : Bool
    oneContradictoryObservableAlwaysFalsifiesMechanismIsFalse :
      oneContradictoryObservableAlwaysFalsifiesMechanism ≡ false

    samePhenotypeImpliesSameMechanism : Bool
    samePhenotypeImpliesSameMechanismIsFalse :
      samePhenotypeImpliesSameMechanism ≡ false

    discriminatingResidualMayReopenSpecificMechanismCarrier : Bool
    discriminatingResidualMayReopenSpecificMechanismCarrierIsTrue :
      discriminatingResidualMayReopenSpecificMechanismCarrier ≡ true

    matchedMultiCoordinatePanelCanSeparateMechanismFamilies : Bool
    matchedMultiCoordinatePanelCanSeparateMechanismFamiliesIsTrue :
      matchedMultiCoordinatePanelCanSeparateMechanismFamilies ≡ true

canonicalDiscriminationBoundary : DiscriminationBoundary
canonicalDiscriminationBoundary = discriminationBoundary
  false refl false refl false refl true refl true refl

-- Core -> Chemistry direction of the BIDI seam.
existingGenericModelDiscriminationBoundary : Core.ModelDiscriminationBoundary
existingGenericModelDiscriminationBoundary = Core.canonicalModelDiscriminationBoundary
