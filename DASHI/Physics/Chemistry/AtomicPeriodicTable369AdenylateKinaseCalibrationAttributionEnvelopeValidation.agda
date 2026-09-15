module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as P

identityRegression :
  P.AdKCalibrationAttributionBoundary.doiRetained
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.pmidRetained
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.pmcidRetained
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.articleQidExplicitlyUnresolved
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.adkQidRetained
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
identityRegression = refl , refl , refl , refl , refl

provenanceRegression :
  P.AdKCalibrationAttributionBoundary.numericAtomCarriesSource
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.numericAtomCarriesLocator
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.numericAtomCarriesMethodRole
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
  × P.AdKCalibrationAttributionBoundary.unpaidAtomRemainsAttributable
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ true
provenanceRegression = refl , refl , refl , refl

firewallRegression :
  P.AdKCalibrationAttributionBoundary.qidCreatesScientificAuthority
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ false
  × P.AdKCalibrationAttributionBoundary.doiCreatesScientificAuthority
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ false
  × P.AdKCalibrationAttributionBoundary.identityEqualityCreatesNumericPayment
    P.canonicalAdKCalibrationAttributionBoundary
  ≡ false
firewallRegression = refl , refl , refl
