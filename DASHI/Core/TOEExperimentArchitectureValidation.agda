module DASHI.Core.TOEExperimentArchitectureValidation where

open import DASHI.Core.Prelude

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.CalibratedExperimentInferenceExact as Calibrated
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- Focused compile root.  These witnesses pin the intended theorem boundaries
-- without manufacturing physical or probabilistic claims.
------------------------------------------------------------------------

predictionBoundary : Envelope.PredictionEnvelopeBoundary
predictionBoundary = Envelope.canonicalPredictionEnvelopeBoundary

calibrationBoundary : Calibrated.CalibratedExperimentBoundary
calibrationBoundary = Calibrated.canonicalCalibratedExperimentBoundary

robustnessBoundary : Robust.RobustExperimentFrontierBoundary
robustnessBoundary = Robust.canonicalRobustExperimentFrontierBoundary

physicalBoundary : Physical.PhysicalTheoryExperimentBoundary
physicalBoundary = Physical.canonicalPhysicalTheoryExperimentBoundary

fitDoesNotDetermineAdequacy :
  (Robust.fit Robust.adequateModel ≡ Robust.fit Robust.inadequateModel) ×
  ¬ (Robust.adequate Robust.adequateModel ≡
     Robust.adequate Robust.inadequateModel)
fitDoesNotDetermineAdequacy = Robust.sameFitDifferentAdequacy
