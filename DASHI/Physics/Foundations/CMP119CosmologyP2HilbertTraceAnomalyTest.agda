{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyTest where

import DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact as P2

r136IsHilbertTraceRegression =
  P2.embeddedR136IsPinnedLocalCHilbertTrace

sourceAnomalyBuildsOldReadoutRegression =
  P2.asSameFamilyLocalCTraceAnomalyReadout

freeTraceFrameCalibrationRetiredRegression =
  P2.freeTraceFrameCalibrationNoLongerRequired
