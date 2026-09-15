module DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as Carrier

literalModeListConstancySeparatedFromViscosity :
  Carrier.literalModeListConstancyWithoutViscosity ≡ true
literalModeListConstancySeparatedFromViscosity =
  Carrier.literalModeListConstancyWithoutViscosityIsTrue

literalModeListStillPaysNonzeroSupport :
  Carrier.literalModeListPaysRetainedNonzeroSupport ≡ true
literalModeListStillPaysNonzeroSupport =
  Carrier.literalModeListPaysRetainedNonzeroSupportIsTrue

positiveViscosityNotRequired :
  Carrier.positiveViscosityRequiredForModeListCarrier ≡ false
positiveViscosityNotRequired =
  Carrier.positiveViscosityRequiredForModeListCarrierIsFalse
