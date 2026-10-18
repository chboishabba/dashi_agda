module DASHI.Biology.ThreatCalibratedSocialPerceptionBoundaryExact where

------------------------------------------------------------------------
-- COMPATIBILITY OWNER
--
-- The later implementation splits threat sensitivity, mentalizing, relational
-- monitoring and response policy rather than defining one scalar social-
-- perception capacity.
------------------------------------------------------------------------

import DASHI.Biology.ThreatMentalizingRelationalMonitoringSeparationExact as MTR
import DASHI.Cognition.PNF.TrialecticMentalizingCalibrationExact as Calibration

canonicalThreatCalibratedSocialPerceptionBoundary =
  MTR.canonicalThreatMentalizingMonitoringBoundary
