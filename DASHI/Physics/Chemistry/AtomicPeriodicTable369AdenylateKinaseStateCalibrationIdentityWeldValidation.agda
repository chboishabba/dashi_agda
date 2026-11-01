module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStateCalibrationIdentityWeldValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStateCalibrationIdentityWeldExact as P

endpointIdentityRegression :
  P.AdKStateCalibrationIdentityWeldBoundary.alphaCarriesOpenStructuralReference
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ true
  × P.AdKStateCalibrationIdentityWeldBoundary.zetaCarriesClosedStructuralReference
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ true
  × P.AdKStateCalibrationIdentityWeldBoundary.gammaCarriesNoManufacturedPdbIdentity
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ true
endpointIdentityRegression = refl , refl , refl

firewallRegression :
  P.AdKStateCalibrationIdentityWeldBoundary.alphaDefinitionallyEquals4AKE
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ false
  × P.AdKStateCalibrationIdentityWeldBoundary.zetaDefinitionallyEquals1AKE
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ false
  × P.AdKStateCalibrationIdentityWeldBoundary.pdbReferenceCreatesTransitionRate
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ false
  × P.AdKStateCalibrationIdentityWeldBoundary.qidCreatesStateCoordinate
    P.canonicalAdKStateCalibrationIdentityWeldBoundary
  ≡ false
firewallRegression = refl , refl , refl , refl
