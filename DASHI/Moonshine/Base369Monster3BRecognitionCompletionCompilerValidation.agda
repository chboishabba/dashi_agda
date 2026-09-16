module DASHI.Moonshine.Base369Monster3BRecognitionCompletionCompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Base369Monster3BRecognitionCompletionCompilerExact as P

compilerRegression :
  P.Base369RecognitionCompletionBoundary.exactBase369ModelChartReused
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ true
  × P.Base369RecognitionCompletionBoundary.reverseRecognitionCompilerConstructed
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ true
  × P.Base369RecognitionCompletionBoundary.translationIntertwinerCompiled
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ true
  × P.Base369RecognitionCompletionBoundary.modulationIntertwinerCompiled
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ true
compilerRegression = refl , refl , refl , refl

frontierRegression :
  P.Base369RecognitionCompletionBoundary.actualBase369RecognitionCandidateInhabitedHere
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ false
  × P.Base369RecognitionCompletionBoundary.dimensionCreatesCandidate
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ false
  × P.Base369RecognitionCompletionBoundary.characterCreatesCandidate
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ false
  × P.Base369RecognitionCompletionBoundary.oeisCreatesCandidate
    P.canonicalBase369RecognitionCompletionBoundary
  ≡ false
frontierRegression = refl , refl , refl , refl
