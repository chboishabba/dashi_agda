module DASHI.Applications.CounterUASOpenWorldBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASOpenWorldBridgeExact as Bridge

record CounterUASOpenWorldBridgeRegression : Set where
  constructor counterUASOpenWorldBridgeRegression
  field
    unknownSurfacingIsOpenSetLikeNotOpenWorldProof :
      Bridge.unknownSurfacingProvesFullOpenWorldLearning ≡ false
    signatureAccumulationIsNotIncrementalClassLearning :
      Bridge.signatureReferenceAccumulationEqualsIncrementalClassLearning ≡ false
    vendorClaimDoesNotInheritAcademicAlgorithm :
      Bridge.vendorClaimInheritsAcademicAlgorithmIdentity ≡ false
    generalPaperDoesNotValidateVendorImplementation :
      Bridge.generalOpenWorldPaperValidatesVendorImplementation ≡ false
    laterSignatureDoesNotRewriteEarlierUnknownObservation :
      Bridge.laterSignatureRetroactivelyRewritesEarlierObservation ≡ false

canonicalCounterUASOpenWorldBridgeRegression :
  CounterUASOpenWorldBridgeRegression
canonicalCounterUASOpenWorldBridgeRegression =
  counterUASOpenWorldBridgeRegression refl refl refl refl refl
