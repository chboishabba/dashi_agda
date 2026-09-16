module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationProvenanceGraphValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationProvenanceGraphExact as P

provenanceRegression :
  P.AdKCalibrationProvenanceGraphBoundary.articleSourceRetained
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ true
  × P.AdKCalibrationProvenanceGraphBoundary.structuralSourcesRetained
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ true
  × P.AdKCalibrationProvenanceGraphBoundary.externalIdentityNodesRetained
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ true
  × P.AdKCalibrationProvenanceGraphBoundary.acquisitionGuardRetained
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ true
provenanceRegression = refl , refl , refl , refl

promotionRegression :
  P.AdKCalibrationProvenanceGraphBoundary.numericPromotionRequiresRuntimeAcquisition
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ true
  × P.AdKCalibrationProvenanceGraphBoundary.identityNodeAlonePaysNumericCell
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ false
  × P.AdKCalibrationProvenanceGraphBoundary.sourceCountCreatesTruthWeight
    P.canonicalAdKCalibrationProvenanceGraphBoundary
  ≡ false
promotionRegression = refl , refl , refl
