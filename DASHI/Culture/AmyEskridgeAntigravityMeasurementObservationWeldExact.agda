module DASHI.Culture.AmyEskridgeAntigravityMeasurementObservationWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.AmyEskridgeAntigravityObservationBidiCrossPollinationExact as AmyBidi
import DASHI.Culture.AmyEskridgeAntigravityExperimentBindingExact as Experiment
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact as SC
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CONSUMER-BOUND EXPERIMENT RESULT -> GRAVITATIONAL OBSERVATION RECEIPT
--
-- An experiment design or discriminator does not itself create an observation.
-- To enter the #828 GR comparison lane, the actual measurement must carry the
-- calibrated observation receipt and a laboratory-result attributed source.
------------------------------------------------------------------------

record AmyConsumerMeasurementObservation
    {projection : AmyBidi.AmyGravityReverseSearchProjection}
    (demand : Experiment.AmyConsumerBoundExperimentDemand projection) : Set where
  constructor amy-consumer-measurement-observation
  field
    outcome : SC.JointObservation
    observation : Obs.GravitationalObservationReceipt

    observationChannelMatchesDemand :
      Obs.channel observation ≡ Experiment.observationChannel demand

    sourceIsLaboratoryResult :
      Sources.sourceKind (Obs.attributedObservationSource observation)
        ≡ Sources.laboratoryGravityExperimentResult

    sourceInspectedForExactUse :
      Sources.inspectedForExactUse (Obs.attributedObservationSource observation)
        ≡ true

    sourceIsEmpiricalResultCarrier :
      Sources.empiricalResultCarrier (Obs.attributedObservationSource observation)
        ≡ true

open AmyConsumerMeasurementObservation public

------------------------------------------------------------------------
-- Reverse residuals.  These are the first missing coordinates when a designed
-- experiment has not yet produced an admissible GR observation receipt.
------------------------------------------------------------------------

data AmyMeasurementObservationResidual : Set where
  missingLaboratoryAttributedSource : AmyMeasurementObservationResidual
  missingExactChannelBinding : AmyMeasurementObservationResidual
  missingCalibrationReceipt : AmyMeasurementObservationResidual
  missingNoiseOrEnvironmentalModel : AmyMeasurementObservationResidual
  missingExactDataRevision : AmyMeasurementObservationResidual
  missingAnalysisPipeline : AmyMeasurementObservationResidual
  missingExactResultLocator : AmyMeasurementObservationResidual
  sourceNotInspectedForExactUse : AmyMeasurementObservationResidual
  sourceNotEmpiricalResultCarrier : AmyMeasurementObservationResidual

producerForAmyMeasurementResidual :
  AmyMeasurementObservationResidual → Search.ProducerClass
producerForAmyMeasurementResidual missingLaboratoryAttributedSource =
  Search.attributionProducer
producerForAmyMeasurementResidual missingExactChannelBinding =
  Search.identityProducer
producerForAmyMeasurementResidual missingCalibrationReceipt =
  Search.empiricalEvidenceProducer
producerForAmyMeasurementResidual missingNoiseOrEnvironmentalModel =
  Search.empiricalEvidenceProducer
producerForAmyMeasurementResidual missingExactDataRevision =
  Search.attributionProducer
producerForAmyMeasurementResidual missingAnalysisPipeline =
  Search.empiricalEvidenceProducer
producerForAmyMeasurementResidual missingExactResultLocator =
  Search.discriminatorProducer
producerForAmyMeasurementResidual sourceNotInspectedForExactUse =
  Search.propositionSourceProducer
producerForAmyMeasurementResidual sourceNotEmpiricalResultCarrier =
  Search.attributionProducer

------------------------------------------------------------------------
-- Firewalls.  No canonical positive result is constructed here: the module
-- specifies what a real result must contain.
------------------------------------------------------------------------

record AmyMeasurementObservationBoundary : Set where
  constructor amy-measurement-observation-boundary
  field
    experimentDesignEqualsMeasurementResult : Bool
    discriminatorSeparationEqualsPhysicalDetection : Bool
    measurementRequiresExactConsumerChannel : Bool
    measurementRequiresLaboratoryAttributedSource : Bool
    measurementRequiresInspectedEmpiricalCarrier : Bool
    observationReceiptAutomaticallyProvesAntigravity : Bool
    observationReceiptRetroactivelyProvesAmyMechanismAssociation : Bool
    admissibleObservationMayEnterTheoryComparison : Bool

canonicalAmyMeasurementObservationBoundary : AmyMeasurementObservationBoundary
canonicalAmyMeasurementObservationBoundary =
  amy-measurement-observation-boundary
    false false true true true false false true
