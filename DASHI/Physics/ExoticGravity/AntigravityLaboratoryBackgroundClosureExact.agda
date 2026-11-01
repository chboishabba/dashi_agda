module DASHI.Physics.ExoticGravity.AntigravityLaboratoryBackgroundClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as Typed
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorStateBridgeExact as State
import DASHI.Physics.ExoticGravity.AntigravityConstraintInformedBundleDesignExact as Design
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as Legacy

------------------------------------------------------------------------
-- SAME-APPARATUS ORDINARY BACKGROUND CLOSURE
--
-- The existing comparator's final open leaf after a numerical weak-field GR
-- prediction is backgroundClosureLeaf.  Legacy NASA/Hathaway/Tajmar constraints
-- refine what an adequate closure must control, but do not pay it.  This owner
-- supplies only the missing receipt carrier; it does not assert any experiment
-- has produced one.
------------------------------------------------------------------------

record SameApparatusBackgroundClosureReceipt
    (prediction : Typed.OrdinaryGRPredictionReceipt) : Set₂ where
  constructor same-apparatus-background-closure-receipt
  field
    apparatusIdentity : String

    ElectromagneticBackgroundReceipt : Set
    electromagneticBackgroundReceipt : ElectromagneticBackgroundReceipt

    MechanicalVibrationBackgroundReceipt : Set
    mechanicalVibrationBackgroundReceipt : MechanicalVibrationBackgroundReceipt

    ThermalBackgroundReceipt : Set
    thermalBackgroundReceipt : ThermalBackgroundReceipt

    RFInstrumentationBackgroundReceipt : Set
    rfInstrumentationBackgroundReceipt : RFInstrumentationBackgroundReceipt

    SameApparatusPredictionBackgroundReceipt : Set
    sameApparatusPredictionBackgroundReceipt :
      SameApparatusPredictionBackgroundReceipt

    SameObservableChannelReceipt : Set
    sameObservableChannelReceipt : SameObservableChannelReceipt

    PredictionIdentityReceipt : Set
    predictionIdentityReceipt : PredictionIdentityReceipt

    designDemand : Design.ConstraintInformedDesignDemand
    designDemandIsNASARefinedBackground :
      designDemand ≡ Design.nasaRFBackgroundDemand

open SameApparatusBackgroundClosureReceipt public

------------------------------------------------------------------------
-- Existing state-machine payment.
------------------------------------------------------------------------

closedComparatorState : Legacy.GRComparatorState
closedComparatorState =
  Legacy.gr-comparator-state true true true true true true

closedComparatorStateIsClosed :
  Legacy.firstOpenGRComparatorLeaf closedComparatorState
    ≡ Legacy.comparatorClosed
closedComparatorStateIsClosed = refl

record ClosedComparatorStateWeld
    (prediction : Typed.OrdinaryGRPredictionReceipt) : Set₂ where
  constructor closed-comparator-state-weld
  field
    predictionState : State.TypedPredictionStateWeld prediction
    backgroundClosure : SameApparatusBackgroundClosureReceipt prediction
    closedState : Legacy.GRComparatorState
    closedStateMatches : closedState ≡ closedComparatorState

open ClosedComparatorStateWeld public

compileClosedComparatorStateWeld :
  (prediction : Typed.OrdinaryGRPredictionReceipt) →
  SameApparatusBackgroundClosureReceipt prediction →
  ClosedComparatorStateWeld prediction
compileClosedComparatorStateWeld prediction backgrounds =
  closed-comparator-state-weld
    (State.compilePredictionStateWeld prediction)
    backgrounds
    closedComparatorState refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record LaboratoryBackgroundClosureBoundary : Set where
  constructor laboratory-background-closure-boundary
  field
    ordinaryGRPredictionAlonePaysBackgroundClosure : Bool
    rfInstrumentationControlAlonePaysAllBackgrounds : Bool
    legacyArtifactConstraintAutomaticallyPaysNewBackgroundReceipt : Bool
    electromagneticMechanicalThermalClosureAllRequired : Bool
    sameApparatusIdentityRequired : Bool
    sameObservableChannelRequired : Bool
    backgroundClosureMayCloseExistingComparatorState : Bool
    closedComparatorAutomaticallyProvesResidualAnomaly : Bool
    closedComparatorAutomaticallyProvesMaterialEffectiveNegativeG : Bool

canonicalLaboratoryBackgroundClosureBoundary :
  LaboratoryBackgroundClosureBoundary
canonicalLaboratoryBackgroundClosureBoundary =
  laboratory-background-closure-boundary
    false false false true true true true false false
