module DASHI.Physics.Closure.NSAlternativeApproachSurveyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSWaveletRouteClosedReceipt as Closed

data NSAlternativeApproach : Set where
  littlewoodPaleyPrimeBands :
    NSAlternativeApproach

  besovPrimeLaneApproach :
    NSAlternativeApproach

  parabolicHeatKernelSmoothing :
    NSAlternativeApproach

canonicalNSAlternativeApproaches : List NSAlternativeApproach
canonicalNSAlternativeApproaches =
  littlewoodPaleyPrimeBands
  ∷ besovPrimeLaneApproach
  ∷ parabolicHeatKernelSmoothing
  ∷ []

nsAlternativeSurveyStatement : String
nsAlternativeSurveyStatement =
  "After closing the pure wavelet-frame route, the admissible NS direction is prime-band Littlewood-Paley/Besov/parabolic smoothing rather than frame lower bounds."

record NSAlternativeApproachSurveyReceipt : Setω where
  field
    closedReceipt :
      Closed.NSWaveletRouteClosedReceipt

    waveletRouteClosed :
      Closed.nsWaveletRouteFullyClosed closedReceipt ≡ true

    approaches :
      List NSAlternativeApproach

    approachesAreCanonical :
      approaches ≡ canonicalNSAlternativeApproaches

    littlewoodPaleyAnalogueCandidate :
      Bool

    littlewoodPaleyAnalogueCandidateIsTrue :
      littlewoodPaleyAnalogueCandidate ≡ true

    besovSpaceFromPrimeLanes :
      Bool

    besovSpaceFromPrimeLanesIsTrue :
      besovSpaceFromPrimeLanes ≡ true

    parabolicSmoothingStandardApproach :
      Bool

    parabolicSmoothingStandardApproachIsTrue :
      parabolicSmoothingStandardApproach ≡ true

    continuumRegularityProved :
      Bool

    continuumRegularityProvedIsFalse :
      continuumRegularityProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsAlternativeSurveyStatement

open NSAlternativeApproachSurveyReceipt public

canonicalNSAlternativeApproachSurveyReceipt :
  NSAlternativeApproachSurveyReceipt
canonicalNSAlternativeApproachSurveyReceipt =
  record
    { closedReceipt =
        Closed.canonicalNSWaveletRouteClosedReceipt
    ; waveletRouteClosed =
        refl
    ; approaches =
        canonicalNSAlternativeApproaches
    ; approachesAreCanonical =
        refl
    ; littlewoodPaleyAnalogueCandidate =
        true
    ; littlewoodPaleyAnalogueCandidateIsTrue =
        refl
    ; besovSpaceFromPrimeLanes =
        true
    ; besovSpaceFromPrimeLanesIsTrue =
        refl
    ; parabolicSmoothingStandardApproach =
        true
    ; parabolicSmoothingStandardApproachIsTrue =
        refl
    ; continuumRegularityProved =
        false
    ; continuumRegularityProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsAlternativeSurveyStatement
    ; statementIsCanonical =
        refl
    }
