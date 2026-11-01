module DASHI.Physics.ExoticGravity.LiTorrSourceAttributedObservationResidualBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.LiTorrSourceAttributedOrdinaryGREvaluationExact as Attributed

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED OBSERVATION <-> ORDINARY-GR RESIDUAL
--
-- A residual is only meaningful when prediction and observation are the same
-- observable, same apparatus, same calibration/geometry revision, and retain
-- their distinct source roles.  A nonzero residual is not by itself evidence
-- for negative effective G.
------------------------------------------------------------------------

data ResidualStatus : Set where
  residualNotEvaluated : ResidualStatus
  residualConsistentWithinUncertainty : ResidualStatus
  residualOutsideDeclaredUncertainty : ResidualStatus

record SourceAttributedObservation (d : SI.Dimension) : Set where
  constructor source-attributed-observation
  field
    observableName : String
    measurement : SI.Measurement d SI.unitScale
    source : Attributed.RoleBoundSource
    sourceRoleIsExperimental :
      Attributed.role source ≡ Attributed.experimentalMeasurement
    sourceIsSameApparatusMeasurement :
      Attributed.entitlement source ≡ Attributed.sameApparatusMeasurement
    apparatusIdentity : String
    calibrationRevision : String
    geometryRevision : String

open SourceAttributedObservation public

record SourceAttributedPrediction (d : SI.Dimension) : Set₂ where
  constructor source-attributed-prediction
  field
    prediction : Attributed.SourceAttributedNumericalPrediction
    observableName : String
    predictedValue : SI.Measurement d SI.unitScale
    apparatusIdentity : String
    calibrationRevision : String
    geometryRevision : String

open SourceAttributedPrediction public

record SameObservableResidualInput (d : SI.Dimension) : Set₂ where
  constructor same-observable-residual-input
  field
    observation : SourceAttributedObservation d
    prediction : SourceAttributedPrediction d
    sameObservableName :
      SourceAttributedObservation.observableName observation ≡
      SourceAttributedPrediction.observableName prediction
    sameApparatusIdentity :
      SourceAttributedObservation.apparatusIdentity observation ≡
      SourceAttributedPrediction.apparatusIdentity prediction
    sameCalibrationRevision :
      SourceAttributedObservation.calibrationRevision observation ≡
      SourceAttributedPrediction.calibrationRevision prediction
    sameGeometryRevision :
      SourceAttributedObservation.geometryRevision observation ≡
      SourceAttributedPrediction.geometryRevision prediction

open SameObservableResidualInput public

record SourceAttributedResidualReceipt (d : SI.Dimension) : Set₂ where
  constructor source-attributed-residual-receipt
  field
    input : SameObservableResidualInput d
    residualCarrier : String
    residualStatus : ResidualStatus
    uncertaintyModelRevision : String
    ResidualEvaluationReceipt : Set
    residualEvaluationReceipt : ResidualEvaluationReceipt
    sourceRolesRetained : Bool
    noHistoricalAuthorPromotion : Bool

open SourceAttributedResidualReceipt public

record ResidualInterpretationBoundary : Set where
  constructor residual-interpretation-boundary
  field
    nonzeroResidualProvesNegativeEffectiveG : Bool
    outsideUncertaintyResidualProvesNewPhysics : Bool
    observationMayBorrowTheoryPaperAuthority : Bool
    predictionMayBorrowExperimentalAuthority : Bool
    residualMayBeAttributedToAmy : Bool
    residualRequiresSameObservable : Bool
    residualRequiresSameApparatus : Bool
    residualRequiresSameCalibrationAndGeometry : Bool
    ordinaryConfounderAnalysisStillRequired : Bool

canonicalResidualInterpretationBoundary : ResidualInterpretationBoundary
canonicalResidualInterpretationBoundary =
  residual-interpretation-boundary
    false false false false false true true true true
