module DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact as Stress
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.LiTorrStandardGRRotatingSourceKernelExact as GR
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- LABORATORY SOURCE + CLOSED GEOMETRY -> ORDINARY-GR COMPARATOR REQUEST
--
-- This compiler closes an architectural seam only.  It does not manufacture a
-- numerical field prediction: exact geometry instantiation, convention, weak-
-- field validity and evaluation remain explicit receipts.
------------------------------------------------------------------------

record SameApparatusGRComparatorInput : Set₂ where
  constructor same-apparatus-gr-comparator-input
  field
    apparatusIdentity : String
    laboratoryStressEnergy : Stress.LaboratoryStressEnergyReceipt

    geometryState : Geometry.GeometryClosureState
    geometryIsClosed :
      Geometry.firstOpenGeometryLeaf geometryState ≡ Geometry.closedGeometry

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

record OrdinaryGRComparatorRequest : Set₂ where
  constructor ordinary-gr-comparator-request
  field
    apparatusIdentity : String
    source : Stress.LaboratoryStressEnergyReceipt
    geometry : GR.RotatingSourceGeometry
    kernel : GR.WeakFieldGRKernel geometry

    NumericalEvaluationReceipt : Set
    numericalEvaluationReceipt : NumericalEvaluationReceipt

    SameInputPredictionReceipt : Set
    sameInputPredictionReceipt : SameInputPredictionReceipt

open OrdinaryGRComparatorRequest public

------------------------------------------------------------------------
-- The input is enough to authorize numerical evaluation; it is not itself the
-- evaluation.  This avoids pretending a symbolic weak-field scaling kernel is
-- already a literal same-apparatus prediction.
------------------------------------------------------------------------

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
    exactGeometryInstantiationRequired : Bool
    weakFieldValidityRequired : Bool
    conventionNormalizationRequired : Bool
    numericalEvaluationStillRequired : Bool
    comparatorRequestAutomaticallyProvesResidualAnomaly : Bool
    comparatorRequestAutomaticallyProvesNegativeEffectiveG : Bool

canonicalLaboratoryGRComparatorBoundary : LaboratoryGRComparatorBoundary
canonicalLaboratoryGRComparatorBoundary =
  laboratory-gr-comparator-boundary
    false false false true true true true false false
