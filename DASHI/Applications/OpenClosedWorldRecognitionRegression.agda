module DASHI.Applications.OpenClosedWorldRecognitionRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.OpenClosedWorldRecognitionExact as OpenClosed
import DASHI.Applications.OpenClosedWorldRecognitionSourceAtlasExact as Sources

record OpenClosedWorldRecognitionRegression : Set where
  constructor openClosedWorldRecognitionRegression
  field
    closedSetRequiresAllTestClassesKnown :
      OpenClosed.closedSetAssumesKnownTestClasses ≡ true
    openSetAllowsUnknownTestClasses :
      OpenClosed.openSetAllowsUnknownTestClasses ≡ true
    openSetDoesNotRequireIncrementalIncorporation :
      OpenClosed.openSetRequiresIncrementalIncorporation ≡ false
    openWorldRequiresUnknownHandlingAndIncrementalLearning :
      OpenClosed.openWorldRequiresUnknownHandlingAndIncrementalLearning ≡ true
    oodDetectionIsNotOpenSetRecognition :
      OpenClosed.oodDetectionEqualsOpenSetRecognition ≡ false
    openSetRecognitionIsNotOpenWorldRecognition :
      OpenClosed.openSetEqualsOpenWorld ≡ false
    openWorldDetectionAddsLocalization :
      OpenClosed.openWorldObjectDetectionRequiresLocalization ≡ true
    unknownRecognitionDoesNotCreateKnownIdentity :
      OpenClosed.unknownRecognitionCreatesKnownIdentity ≡ false
    incrementalAdditionDoesNotRetroactivelyValidatePriorIdentity :
      OpenClosed.incrementalAdditionRetroactivelyValidatesPriorIdentity ≡ false
    sourceAtlasNonPromoting :
      Sources.openClosedWorldSourceAtlasCreatesAuthority ≡ false

canonicalOpenClosedWorldRecognitionRegression :
  OpenClosedWorldRecognitionRegression
canonicalOpenClosedWorldRecognitionRegression =
  openClosedWorldRecognitionRegression
    refl refl refl refl refl refl refl refl refl
    Sources.openClosedWorldSourceAtlasCreatesAuthorityIsFalse
