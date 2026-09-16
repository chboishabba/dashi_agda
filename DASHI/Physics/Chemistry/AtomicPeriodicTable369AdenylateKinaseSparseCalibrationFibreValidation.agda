module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as P

paidSparseCoordinatesRegression :
  P.AdKSparseCalibrationBoundary.alphaThetaOnePaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
  × P.AdKSparseCalibrationBoundary.alphaThetaTwoPaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
  × P.AdKSparseCalibrationBoundary.zetaThetaOnePaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
  × P.AdKSparseCalibrationBoundary.zetaThetaTwoPaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
  × P.AdKSparseCalibrationBoundary.gammaReferenceFreeEnergyPaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
paidSparseCoordinatesRegression = refl , refl , refl , refl , refl

missingnessAndRateKindRegression :
  P.AdKSparseCalibrationBoundary.namedStateDLnTablePaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ false
  × P.AdKSparseCalibrationBoundary.perEdgeKramersNumericTablePaid
    P.canonicalAdKSparseCalibrationBoundary
  ≡ false
  × P.AdKSparseCalibrationBoundary.kramersRateEqualsExperimentalRate
    P.canonicalAdKSparseCalibrationBoundary
  ≡ false
  × P.AdKSparseCalibrationBoundary.missingCoordinateMayBeInferredFromNeighbour
    P.canonicalAdKSparseCalibrationBoundary
  ≡ false
missingnessAndRateKindRegression = refl , refl , refl , refl

attributionRegression :
  P.AdKSparseCalibrationBoundary.reusesAttributedSourceCore
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
  × P.AdKSparseCalibrationBoundary.reusesExternalIdentityAvailability
    P.canonicalAdKSparseCalibrationBoundary
  ≡ true
  × P.AdKSparseCalibrationBoundary.unresolvedArticleQidBlocksCalibration
    P.canonicalAdKSparseCalibrationBoundary
  ≡ false
  × P.AdKSparseCalibrationBoundary.citationCreatesScientificAuthority
    P.canonicalAdKSparseCalibrationBoundary
  ≡ false
attributionRegression = refl , refl , refl , refl
