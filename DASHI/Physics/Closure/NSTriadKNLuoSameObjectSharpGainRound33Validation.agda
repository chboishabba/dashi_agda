module DASHI.Physics.Closure.NSTriadKNLuoSameObjectSharpGainRound33Validation where

------------------------------------------------------------------------
-- Round Thirty-Three validation root.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoIndexedGluingResourceLatticeRound32Validation
import DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact as Lookup
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Gain
import DASHI.Physics.Closure.NSTriadKNNineOwnerResourceReserveRound33Exact as Reserve

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

sameObjectCompatibilityRegression :
  Lookup.sameObjectCompatibilityNecessityClosed ≡ true
sameObjectCompatibilityRegression =
  Lookup.sameObjectCompatibilityNecessityClosedIsTrue

canonicalVelocityLookupRegression :
  Lookup.canonicalRetainedVelocityLookupClosed ≡ true
canonicalVelocityLookupRegression =
  Lookup.canonicalRetainedVelocityLookupClosedIsTrue

fullFiniteSystemStillOpenRegression :
  Lookup.canonicalFiniteGalerkinSystemBuilderConstructed ≡ false
fullFiniteSystemStillOpenRegression =
  Lookup.canonicalFiniteGalerkinSystemBuilderConstructedIsFalse

sharpDyadicGainRegression :
  Gain.sharpDyadicGainCalibrationClosed ≡ true
sharpDyadicGainRegression =
  Gain.sharpDyadicGainCalibrationClosedIsTrue

physicalDyadicGainStillOpenRegression :
  Gain.physicalHHBadDyadicGainConstructed ≡ false
physicalDyadicGainStillOpenRegression =
  Gain.physicalHHBadDyadicGainConstructedIsFalse

nineOwnerResourceRegression :
  Reserve.nineOwnerResourceValuationClosed ≡ true
nineOwnerResourceRegression =
  Reserve.nineOwnerResourceValuationClosedIsTrue

explicitReserveRegression :
  Reserve.explicitViscosityReserveAlgebraClosed ≡ true
explicitReserveRegression =
  Reserve.explicitViscosityReserveAlgebraClosedIsTrue

physicalNineOwnerCertificateStillOpenRegression :
  Reserve.physicalNineOwnerResourceCertificateConstructed ≡ false
physicalNineOwnerCertificateStillOpenRegression =
  Reserve.physicalNineOwnerResourceCertificateConstructedIsFalse
