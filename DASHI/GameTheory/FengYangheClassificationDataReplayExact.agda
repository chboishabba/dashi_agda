module DASHI.GameTheory.FengYangheClassificationDataReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.GameTheory.FengYangheMilitaryAIGameStatisticsBidiExact as Base

------------------------------------------------------------------------
-- FENG YANGHE / CLASSIFICATION SOURCE-DATA REPLAY SURFACE
-- NUDT Press ISBN 978-7-5673-0533-5 and 978-7-5673-0611-0.
--
-- Publisher metadata exposes model assumptions and workflow, but not the full
-- example datasets/equations in a machine-readable public carrier inspected
-- here.  This owner therefore pays method coordinates and leaves numeric replay
-- explicitly blocked.
------------------------------------------------------------------------

record FengClassificationDataReplay : Set where
  constructor feng-classification-data-replay
  field
    bayesianSource : String
    noisyLabelSource : String
    framework : String
    baseDistributions : String
    preprocessingRequirement : String
    automaticFilteringClaim : String
    taskFamily : String
    samplingStepReported : Bool
    simulationExamplesReported : Bool
    realDataExamplesReported : Bool
    exactModelEquationsPaid : Bool
    exactExampleDatasetPaid : Bool
    exactNoiseParametersPaid : Bool
    warSkullSameObjectPaid : Bool

open FengClassificationDataReplay public

fengClassificationDataReplay : FengClassificationDataReplay
fengClassificationDataReplay = feng-classification-data-replay
  "NUDT Press ISBN 978-7-5673-0533-5, 2019"
  "NUDT Press ISBN 978-7-5673-0611-0, 2023"
  "multi-group graph Bayesian classification framework; separate noisy-label classification work"
  "multinomial and Dirichlet distribution assumptions in the group-graph Bayesian model"
  "publisher description says no data preprocessing is required by the framework"
  "automatic filtering of noisy and redundant attributes"
  "regression or classification prediction"
  true
  true
  true
  false
  false
  false
  false

existingBayesianReceipt : Base.FengWorkReceipt
existingBayesianReceipt = Base.bayesianClassificationReceipt

existingNoisyLabelReceipt : Base.FengWorkReceipt
existingNoisyLabelReceipt = Base.noisyLabelClassificationReceipt

sourceDataReplayPaysPublisherMethodCoordinates : Bool
sourceDataReplayPaysPublisherMethodCoordinates = true

sourceDataReplayPaysExactClassifierReplay : Bool
sourceDataReplayPaysExactClassifierReplay = false

classificationMethodPaysWarSkullImplementation : Bool
classificationMethodPaysWarSkullImplementation = false
