module DASHI.Physics.Chemistry.Atomic369Kernel6HeisenbergBridgeValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.Atomic369Kernel6HeisenbergBridgeExact as B

kernelRoundTrip :
  (k : B.Kernel6) → B.x6ToKernel6 (B.kernel6ToX6 k) ≡ k
kernelRoundTrip = B.kernel6RoundTrip

x6RoundTrip :
  (x : B.HeisenbergX6) → B.kernel6ToX6 (B.x6ToKernel6 x) ≡ x
x6RoundTrip = B.x6RoundTrip

carrierBridgePaid :
  B.Kernel6HeisenbergBoundary.kernel6HeisenbergCarrierIsomorphismPaid
    B.canonicalKernel6HeisenbergBoundary ≡ true
carrierBridgePaid = refl

physicalAssignmentNotInvented :
  B.Kernel6HeisenbergBoundary.physicalNH3StateToKernel6AssignmentPaid
    B.canonicalKernel6HeisenbergBoundary ≡ false
physicalAssignmentNotInvented = refl
