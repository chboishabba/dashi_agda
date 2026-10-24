module DASHI.Cognition.Teleodynamics.TeleodynamicSemanticActionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicSemanticActionBridgeExact as Bridge

pairAccuracyIsNotRepresentationLaw :
  Bridge.pairAccuracyCreatesLatentAction Bridge.canonicalSemanticActionBoundary ≡ false
pairAccuracyIsNotRepresentationLaw = refl

compositionIsIndependentDiagnostic :
  Bridge.heldOutCompositionRequired Bridge.canonicalSemanticActionBoundary ≡ true
compositionIsIndependentDiagnostic = refl

futureLanguageIsSeparateEndpoint :
  Bridge.futureLanguageOutcomeSeparate Bridge.canonicalSemanticActionBoundary ≡ true
futureLanguageIsSeparateEndpoint = refl

fitStillDoesNotCreateMechanism :
  Bridge.successfulActionFitCreatesMechanism Bridge.canonicalSemanticActionBoundary ≡ false
fitStillDoesNotCreateMechanism = refl

e8RecognitionStillNeedsIntertwining :
  Bridge.e8CarrierCountCreatesRecognition Bridge.canonicalSemanticActionBoundary ≡ false
e8RecognitionStillNeedsIntertwining = refl
