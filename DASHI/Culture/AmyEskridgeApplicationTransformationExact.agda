module DASHI.Culture.AmyEskridgeApplicationTransformationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationTransformationCapabilityBidiExact as A

------------------------------------------------------------------------
-- AMY ESKRIDGE APPLICATION TRANSFORMATION
--
-- The relevant investigative object is not simply anomalous-force physics.
-- It is the transformation from a proposed/public scientific foundation into a
-- concrete experimental/application capability: apparatus geometry,
-- calibration, data reduction, operating conditions, validation history, and
-- the Institute's privately matured derivative work.
------------------------------------------------------------------------

amyPOAMSApplicationTransformation : A.ApplicationTransformation
amyPOAMSApplicationTransformation = A.application-transformation
  "Amy Eskridge / POAMS-adjacent anomalous-force experimental application"
  (A.governingPhysics ∷ [])
  (A.applicationGeometry ∷
   A.constitutiveConfiguration ∷
   A.calibrationState ∷
   A.operatingWindow ∷
   A.failureHistory ∷
   A.validationCorpus ∷
   A.uncertaintyModel ∷
   A.integrationWorkflow ∷
   A.tacitExecutionKnowledge ∷ [])
  "NASA/TM-20205010911; Amy Eskridge captured September 2020 release-review statement; Institute for Exotic Science public materials"
  "The public/report-level theory and preliminary experiment do not determine the Institute's later apparatus configuration, calibration, analysis workflow, validation corpus, or privately matured derivative results."

record AmyApplicationTransformationFrontier : Set where
  constructor amy-application-transformation-frontier
  field
    publicFoundationLocated : Bool
    publicFoundationLocatedIsTrue : publicFoundationLocated ≡ true
    privateMaturationSelfReported : Bool
    privateMaturationSelfReportedIsTrue : privateMaturationSelfReported ≡ true
    exactPrivateDerivativeObjectIdentified : Bool
    exactPrivateDerivativeObjectIdentifiedIsFalse : exactPrivateDerivativeObjectIdentified ≡ false
    apparatusConfigurationRecovered : Bool
    apparatusConfigurationRecoveredIsFalse : apparatusConfigurationRecovered ≡ false
    calibrationAndDataReductionRecovered : Bool
    calibrationAndDataReductionRecoveredIsFalse : calibrationAndDataReductionRecovered ≡ false
    validationCorpusRecovered : Bool
    validationCorpusRecoveredIsFalse : validationCorpusRecovered ≡ false
    sameObjectPOAMSWeldClosed : Bool
    sameObjectPOAMSWeldClosedIsFalse : sameObjectPOAMSWeldClosed ≡ false
    successorOrHandoverRecovered : Bool
    successorOrHandoverRecoveredIsFalse : successorOrHandoverRecovered ≡ false
    eventCausalLinkOwned : Bool
    eventCausalLinkOwnedIsFalse : eventCausalLinkOwned ≡ false

canonicalAmyApplicationTransformationFrontier : AmyApplicationTransformationFrontier
canonicalAmyApplicationTransformationFrontier = amy-application-transformation-frontier
  true refl true refl false refl false refl false refl false refl false refl false refl false refl

data AmyApplicationReverseTarget : Set where
  acquireInstituteDerivedObjectIdentity
  acquireApparatusGeometry
  acquireCalibrationProcedure
  acquireRawAndReducedData
  acquireNullAndFailureHistory
  acquireValidationProtocol
  acquireUncertaintyModel
  acquireLabNotebookOrVersionedWorkflow
  acquireSuccessorOrHandover
  acquireIndependentEventLink
  : AmyApplicationReverseTarget
