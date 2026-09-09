module DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact as Stress
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.LiTorrStandardGRRotatingSourceKernelExact as GR
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

record SameApparatusGRComparatorInput : Set₂ where
  constructor same-apparatus-gr-comparator-input
  field
    apparatusIdentity : String
    laboratoryStressEnergy : Stress.LaboratoryStressEnergyReceipt
    geometryState : Geometry.GeometryClosureState
    geometryIsClosed : Geometry.firstOpenGeometryLeaf geometryState ≡ Geometry.closedGeometry
    rotatingGeometry : GR.RotatingSourceGeometry
    weakFieldKernel : GR.WeakFieldGRKernel rotatingGeometry
    SameApparatusStressGeometryReceipt : Set
    sameApparatusStressGeometryReceipt : SameApparatusStressGeometryReceipt
    ExactGeometryInstantiationReceipt : Set
    exactGeometryInstantiationReceipt : ExactGeometryInstantiationReceipt
    WeakFieldValidityReceipt : Set
    weakFieldValidityReceipt : WeakFieldValidityReceipt
    ConventionNormalizationReceipt : Set
    conventionNormalizationReceipt : ConventionNormalizationReceipt

open SameApparatusGRComparatorInput public

record OrdinaryGREvaluationRequest : Set₂ where
  constructor ordinary-gr-evaluation-request
  field
    apparatusIdentity : String
    source : Stress.LaboratoryStressEnergyReceipt
    geometry : GR.RotatingSourceGeometry
    kernel : GR.WeakFieldGRKernel geometry
    ExactGeometryInstantiationReceipt : Set
    exactGeometryInstantiationReceipt : ExactGeometryInstantiationReceipt
    WeakFieldValidityReceipt : Set
    weakFieldValidityReceipt : WeakFieldValidityReceipt
    ConventionNormalizationReceipt : Set
    conventionNormalizationReceipt : ConventionNormalizationReceipt

open OrdinaryGREvaluationRequest public

compileOrdinaryGREvaluationRequest :
  SameApparatusGRComparatorInput → OrdinaryGREvaluationRequest
compileOrdinaryGREvaluationRequest input =
  ordinary-gr-evaluation-request
    (SameApparatusGRComparatorInput.apparatusIdentity input)
    (SameApparatusGRComparatorInput.laboratoryStressEnergy input)
    (SameApparatusGRComparatorInput.rotatingGeometry input)
    (SameApparatusGRComparatorInput.weakFieldKernel input)
    (SameApparatusGRComparatorInput.ExactGeometryInstantiationReceipt input)
    (SameApparatusGRComparatorInput.exactGeometryInstantiationReceipt input)
    (SameApparatusGRComparatorInput.WeakFieldValidityReceipt input)
    (SameApparatusGRComparatorInput.weakFieldValidityReceipt input)
    (SameApparatusGRComparatorInput.ConventionNormalizationReceipt input)
    (SameApparatusGRComparatorInput.conventionNormalizationReceipt input)

record OrdinaryGRPredictionReceipt : Set₂ where
  constructor ordinary-gr-prediction-receipt
  field
    request : OrdinaryGREvaluationRequest
    predictionCarrier : String
    evaluatorIdentity : String
    evaluatorRevision : String
    NumericalEvaluationReceipt : Set
    numericalEvaluationReceipt : NumericalEvaluationReceipt
    SameInputPredictionReceipt : Set
    sameInputPredictionReceipt : SameInputPredictionReceipt

open OrdinaryGRPredictionReceipt public

data ComparatorResidual : Set where
  missingExactGeometryInstantiation : ComparatorResidual
  missingWeakFieldValidity : ComparatorResidual
  missingConventionNormalization : ComparatorResidual
  missingNumericalEvaluation : ComparatorResidual
  missingSameInputPredictionIdentity : ComparatorResidual

producerForComparatorResidual : ComparatorResidual → Search.ProducerClass
producerForComparatorResidual missingExactGeometryInstantiation = Search.identityProducer
producerForComparatorResidual missingWeakFieldValidity = Search.discriminatorProducer
producerForComparatorResidual missingConventionNormalization = Search.identityProducer
producerForComparatorResidual missingNumericalEvaluation = Search.empiricalEvidenceProducer
producerForComparatorResidual missingSameInputPredictionIdentity = Search.identityProducer

record LaboratoryGRComparatorBoundary : Set where
  constructor laboratory-gr-comparator-boundary
  field
    genericWeakFieldKernelEqualsSameApparatusPrediction : Bool
    closedGeometryAloneEqualsNumericalPrediction : Bool
    labStressEnergyAloneEqualsNumericalPrediction : Bool
    evaluationRequestEqualsCompletedPrediction : Bool
    exactGeometryInstantiationRequired : Bool
    weakFieldValidityRequired : Bool
    conventionNormalizationRequired : Bool
    numericalEvaluationStillRequired : Bool
    sameInputPredictionIdentityStillRequired : Bool
    comparatorRequestAutomaticallyProvesResidualAnomaly : Bool
    predictionReceiptAutomaticallyProvesNegativeEffectiveG : Bool

canonicalLaboratoryGRComparatorBoundary : LaboratoryGRComparatorBoundary
canonicalLaboratoryGRComparatorBoundary =
  laboratory-gr-comparator-boundary false false false false true true true true true false false
