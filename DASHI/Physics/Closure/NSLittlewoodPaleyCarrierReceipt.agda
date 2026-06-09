module DASHI.Physics.Closure.NSLittlewoodPaleyCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSAlternativeApproachSurveyReceipt as Survey

data PrimeLPBand : Set where
  p2Band :
    PrimeLPBand

  p3Band :
    PrimeLPBand

  p5Band :
    PrimeLPBand

canonicalPrimeLPBands : List PrimeLPBand
canonicalPrimeLPBands =
  p2Band
  ∷ p3Band
  ∷ p5Band
  ∷ []

nsLittlewoodPaleyStatement : String
nsLittlewoodPaleyStatement =
  "Carrier NS should move from a failed 2/3/5 Haar-frame bridge to prime-band Littlewood-Paley paraproduct estimates."

record NSLittlewoodPaleyCarrierReceipt : Setω where
  field
    surveyReceipt :
      Survey.NSAlternativeApproachSurveyReceipt

    lpCandidateRecorded :
      Survey.littlewoodPaleyAnalogueCandidate surveyReceipt ≡ true

    bandCount :
      Nat

    bandCountIsThree :
      bandCount ≡ 3

    primeBands :
      List PrimeLPBand

    primeBandsAreCanonical :
      primeBands ≡ canonicalPrimeLPBands

    carrierLPDecompositionDefined :
      Bool

    carrierLPDecompositionDefinedIsTrue :
      carrierLPDecompositionDefined ≡ true

    paraproductFromPrimeBands :
      Bool

    paraproductFromPrimeBandsIsTrue :
      paraproductFromPrimeBands ≡ true

    paraproductBoundProved :
      Bool

    paraproductBoundProvedIsFalse :
      paraproductBoundProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsLittlewoodPaleyStatement

open NSLittlewoodPaleyCarrierReceipt public

canonicalNSLittlewoodPaleyCarrierReceipt :
  NSLittlewoodPaleyCarrierReceipt
canonicalNSLittlewoodPaleyCarrierReceipt =
  record
    { surveyReceipt =
        Survey.canonicalNSAlternativeApproachSurveyReceipt
    ; lpCandidateRecorded =
        refl
    ; bandCount =
        3
    ; bandCountIsThree =
        refl
    ; primeBands =
        canonicalPrimeLPBands
    ; primeBandsAreCanonical =
        refl
    ; carrierLPDecompositionDefined =
        true
    ; carrierLPDecompositionDefinedIsTrue =
        refl
    ; paraproductFromPrimeBands =
        true
    ; paraproductFromPrimeBandsIsTrue =
        refl
    ; paraproductBoundProved =
        false
    ; paraproductBoundProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsLittlewoodPaleyStatement
    ; statementIsCanonical =
        refl
    }
