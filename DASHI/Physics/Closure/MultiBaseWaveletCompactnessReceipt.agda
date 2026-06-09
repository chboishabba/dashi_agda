module DASHI.Physics.Closure.MultiBaseWaveletCompactnessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HaarWaveletEmbeddingReceipt as Haar
import DASHI.Physics.Closure.UltrametricAubinLionsCompactness as Compact

data MultiBaseCompactnessInput : Set where
  dyadicTriadicPentadicEmbedding : MultiBaseCompactnessInput
  ultrametricCoefficientCompactness : MultiBaseCompactnessInput
  frameBoundRieszBasisTarget : MultiBaseCompactnessInput

canonicalMultiBaseCompactnessInputs : List MultiBaseCompactnessInput
canonicalMultiBaseCompactnessInputs =
  dyadicTriadicPentadicEmbedding
  ∷ ultrametricCoefficientCompactness
  ∷ frameBoundRieszBasisTarget
  ∷ []

data MultiBaseCompactnessBlocker : Set where
  missingRieszFrameBounds : MultiBaseCompactnessBlocker
  missingCoefficientToL2ContinuityProof : MultiBaseCompactnessBlocker
  missingArchimedeanNonlinearPassage : MultiBaseCompactnessBlocker

canonicalMultiBaseCompactnessBlockers : List MultiBaseCompactnessBlocker
canonicalMultiBaseCompactnessBlockers =
  missingRieszFrameBounds
  ∷ missingCoefficientToL2ContinuityProof
  ∷ missingArchimedeanNonlinearPassage
  ∷ []

multiBaseCompactnessStatement : String
multiBaseCompactnessStatement =
  "The p-adic-to-Archimedean bridge is sharpened to a multi-base wavelet/Riesz-basis route: coefficient compactness implies L2(R3) compactness only after frame bounds are proved."

record MultiBaseWaveletCompactnessReceipt : Setω where
  field
    haarEmbeddingReceipt :
      Haar.HaarWaveletEmbeddingReceipt

    carrierToL2EmbeddingAvailable :
      Haar.carrierToL2EmbeddingInhabited haarEmbeddingReceipt ≡ true

    ultrametricCompactnessReceipt :
      Compact.UltrametricAubinLionsCompactnessReceipt

    ultrametricCompactnessStillOpen :
      Compact.carrierSpecializedCompactnessConstructed ultrametricCompactnessReceipt
      ≡
      false

    inputs :
      List MultiBaseCompactnessInput

    inputsAreCanonical :
      inputs ≡ canonicalMultiBaseCompactnessInputs

    rieszBasisForMultiBaseWavelet :
      Bool

    rieszBasisForMultiBaseWaveletIsCandidate :
      rieszBasisForMultiBaseWavelet ≡ true

    frameBoundsProved :
      Bool

    frameBoundsProvedIsFalse :
      frameBoundsProved ≡ false

    aubinLionsViaRiesz :
      Bool

    aubinLionsViaRieszIsConditional :
      aubinLionsViaRiesz ≡ true

    padicToArchimedeanBridgeCandidate :
      Bool

    padicToArchimedeanBridgeCandidateIsTrue :
      padicToArchimedeanBridgeCandidate ≡ true

    archimedeanCompactnessPromoted :
      Bool

    archimedeanCompactnessPromotedIsFalse :
      archimedeanCompactnessPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List MultiBaseCompactnessBlocker

    blockersAreCanonical :
      blockers ≡ canonicalMultiBaseCompactnessBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ multiBaseCompactnessStatement

    receiptBoundary :
      List String

open MultiBaseWaveletCompactnessReceipt public

canonicalMultiBaseWaveletCompactnessReceipt :
  MultiBaseWaveletCompactnessReceipt
canonicalMultiBaseWaveletCompactnessReceipt =
  record
    { haarEmbeddingReceipt =
        Haar.canonicalHaarWaveletEmbeddingReceipt
    ; carrierToL2EmbeddingAvailable =
        refl
    ; ultrametricCompactnessReceipt =
        Compact.canonicalUltrametricAubinLionsCompactnessReceipt
    ; ultrametricCompactnessStillOpen =
        refl
    ; inputs =
        canonicalMultiBaseCompactnessInputs
    ; inputsAreCanonical =
        refl
    ; rieszBasisForMultiBaseWavelet =
        true
    ; rieszBasisForMultiBaseWaveletIsCandidate =
        refl
    ; frameBoundsProved =
        false
    ; frameBoundsProvedIsFalse =
        refl
    ; aubinLionsViaRiesz =
        true
    ; aubinLionsViaRieszIsConditional =
        refl
    ; padicToArchimedeanBridgeCandidate =
        true
    ; padicToArchimedeanBridgeCandidateIsTrue =
        refl
    ; archimedeanCompactnessPromoted =
        false
    ; archimedeanCompactnessPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalMultiBaseCompactnessBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        multiBaseCompactnessStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The Riesz/frame-bound route is recorded as the concrete p-adic-to-Archimedean bridge candidate"
        ∷ "Frame bounds and coefficient-to-L2 continuity are not proved here"
        ∷ "Clay Navier-Stokes promotion remains false"
        ∷ []
    }

multiBaseWaveletCompactnessDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalMultiBaseWaveletCompactnessReceipt ≡ false
multiBaseWaveletCompactnessDoesNotPromoteClay =
  refl

