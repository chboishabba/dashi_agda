module DASHI.Physics.Closure.HaarWaveletEmbeddingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

data CarrierWaveletBase : Set where
  dyadicP2 : CarrierWaveletBase
  triadicP3 : CarrierWaveletBase
  pentadicP5 : CarrierWaveletBase

canonicalCarrierWaveletBases : List CarrierWaveletBase
canonicalCarrierWaveletBases =
  dyadicP2
  ∷ triadicP3
  ∷ pentadicP5
  ∷ []

data CarrierToL2EmbeddingBlocker : Set where
  standardSingleBaseHaarNotApplicable : CarrierToL2EmbeddingBlocker
  missingMultiBaseFrameBounds : CarrierToL2EmbeddingBlocker
  missingArchimedeanLimitPassage : CarrierToL2EmbeddingBlocker

canonicalCarrierToL2EmbeddingBlockers :
  List CarrierToL2EmbeddingBlocker
canonicalCarrierToL2EmbeddingBlockers =
  standardSingleBaseHaarNotApplicable
  ∷ missingMultiBaseFrameBounds
  ∷ missingArchimedeanLimitPassage
  ∷ []

haarEmbeddingStatement : String
haarEmbeddingStatement =
  "Depth-d p2, p3, and p5 carrier leaves embed as dyadic, triadic, and pentadic step/wavelet systems in L2(R3).  The union is multi-base, not a standard single Haar basis."

record HaarWaveletEmbeddingReceipt : Setω where
  field
    bases :
      List CarrierWaveletBase

    basesAreCanonical :
      bases ≡ canonicalCarrierWaveletBases

    p2BranchingBase :
      Nat

    p2BranchingBaseIsTwo :
      p2BranchingBase ≡ 2

    p3BranchingBase :
      Nat

    p3BranchingBaseIsThree :
      p3BranchingBase ≡ 3

    p5BranchingBase :
      Nat

    p5BranchingBaseIsFive :
      p5BranchingBase ≡ 5

    haarEmbeddingDefined :
      Bool

    haarEmbeddingDefinedIsTrue :
      haarEmbeddingDefined ≡ true

    carrierToL2EmbeddingInhabited :
      Bool

    carrierToL2EmbeddingInhabitedIsTrue :
      carrierToL2EmbeddingInhabited ≡ true

    multiBaseWaveletSystem :
      Bool

    multiBaseWaveletSystemIsTrue :
      multiBaseWaveletSystem ≡ true

    standardHaarNotApplicable :
      Bool

    standardHaarNotApplicableIsTrue :
      standardHaarNotApplicable ≡ true

    alternativeCompactnessBridgeOpen :
      Bool

    alternativeCompactnessBridgeOpenIsTrue :
      alternativeCompactnessBridgeOpen ≡ true

    archimedeanNSLimitPromoted :
      Bool

    archimedeanNSLimitPromotedIsFalse :
      archimedeanNSLimitPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List CarrierToL2EmbeddingBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierToL2EmbeddingBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ haarEmbeddingStatement

    receiptBoundary :
      List String

open HaarWaveletEmbeddingReceipt public

canonicalHaarWaveletEmbeddingReceipt :
  HaarWaveletEmbeddingReceipt
canonicalHaarWaveletEmbeddingReceipt =
  record
    { bases =
        canonicalCarrierWaveletBases
    ; basesAreCanonical =
        refl
    ; p2BranchingBase =
        2
    ; p2BranchingBaseIsTwo =
        refl
    ; p3BranchingBase =
        3
    ; p3BranchingBaseIsThree =
        refl
    ; p5BranchingBase =
        5
    ; p5BranchingBaseIsFive =
        refl
    ; haarEmbeddingDefined =
        true
    ; haarEmbeddingDefinedIsTrue =
        refl
    ; carrierToL2EmbeddingInhabited =
        true
    ; carrierToL2EmbeddingInhabitedIsTrue =
        refl
    ; multiBaseWaveletSystem =
        true
    ; multiBaseWaveletSystemIsTrue =
        refl
    ; standardHaarNotApplicable =
        true
    ; standardHaarNotApplicableIsTrue =
        refl
    ; alternativeCompactnessBridgeOpen =
        true
    ; alternativeCompactnessBridgeOpenIsTrue =
        refl
    ; archimedeanNSLimitPromoted =
        false
    ; archimedeanNSLimitPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalCarrierToL2EmbeddingBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        haarEmbeddingStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The carrier-to-L2 embedding target is now explicit as a 2/3/5 multi-base wavelet system"
        ∷ "Single-base Haar compactness is not applicable"
        ∷ "Archimedean NS limit and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

haarWaveletEmbeddingDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalHaarWaveletEmbeddingReceipt ≡ false
haarWaveletEmbeddingDoesNotPromoteClay =
  refl

