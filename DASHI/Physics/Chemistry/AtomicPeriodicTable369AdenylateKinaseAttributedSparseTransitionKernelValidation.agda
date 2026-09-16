module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAttributedSparseTransitionKernelValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAttributedSparseTransitionKernelExact as P

kernelRegression :
  P.AdKAttributedSparseKernelBoundary.sixRouteEdgesRetained
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
  × P.AdKAttributedSparseKernelBoundary.everyEdgeCarriesAttributionEnvelope
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
  × P.AdKAttributedSparseKernelBoundary.kramersRateRoleRetained
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
  × P.AdKAttributedSparseKernelBoundary.missingNumericRateRetained
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
kernelRegression = refl , refl , refl , refl

stateRegression :
  P.AdKAttributedSparseKernelBoundary.stateCalibrationFibreRetained
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
  × P.AdKAttributedSparseKernelBoundary.relativeEnergyReferenceRetained
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
  × P.AdKAttributedSparseKernelBoundary.endpointAnglesRetained
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ true
stateRegression = refl , refl , refl

firewallRegression :
  P.AdKAttributedSparseKernelBoundary.kernelIsFullyNumericallyCalibrated
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ false
  × P.AdKAttributedSparseKernelBoundary.kramersKernelEqualsExperimentalKernel
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ false
  × P.AdKAttributedSparseKernelBoundary.identityMetadataCreatesMissingNumbers
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ false
  × P.AdKAttributedSparseKernelBoundary.pathFluxEqualsEdgeKernel
    P.canonicalAdKAttributedSparseKernelBoundary
  ≡ false
firewallRegression = refl , refl , refl , refl
