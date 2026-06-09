module DASHI.Physics.Closure.MutualOrthogonalityGeneralProofReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DyadicTriadicScale1InnerProduct as Scale1
import DASHI.Physics.Closure.WaveletOrthogonalityProofReceipt as Prior

------------------------------------------------------------------------
-- General all-scale mutual-orthogonality proof attempt.

data OrthogonalityPair : Set where
  dyadicTriadic :
    OrthogonalityPair

  dyadicPentadic :
    OrthogonalityPair

  triadicPentadic :
    OrthogonalityPair

canonicalOrthogonalityPairs : List OrthogonalityPair
canonicalOrthogonalityPairs =
  dyadicTriadic
  ∷ dyadicPentadic
  ∷ triadicPentadic
  ∷ []

data ProofStatus : Set where
  finiteChecksPass :
    ProofStatus

  incompatiblePartitionLemmaNeeded :
    ProofStatus

  allScaleProofOpen :
    ProofStatus

canonicalProofStatus : List ProofStatus
canonicalProofStatus =
  finiteChecksPass
  ∷ incompatiblePartitionLemmaNeeded
  ∷ allScaleProofOpen
  ∷ []

proofAttemptStatement : String
proofAttemptStatement =
  "Scale-zero and scale-one cancellations do not prove that every dyadic half-interval sees equal signed triadic or pentadic mass; the all-scale partition lemma remains open."

record MutualOrthogonalityGeneralProofReceipt : Setω where
  field
    scaleOneReceipt :
      Scale1.DyadicTriadicScale1InnerProductReceipt

    scaleOneCancels :
      Scale1.scaleOneDyadicTriadicInnerProductZero scaleOneReceipt
      ≡
      true

    priorReceipt :
      Prior.WaveletOrthogonalityProofReceipt

    priorAllScaleProofStillOpen :
      Prior.literalMutualOrthogonalityProved priorReceipt ≡ false

    pairs :
      List OrthogonalityPair

    pairsAreCanonical :
      pairs ≡ canonicalOrthogonalityPairs

    proofStatus :
      List ProofStatus

    proofStatusIsCanonical :
      proofStatus ≡ canonicalProofStatus

    mutualOrthogonalityProofAttempted :
      Bool

    mutualOrthogonalityProofAttemptedIsTrue :
      mutualOrthogonalityProofAttempted ≡ true

    dyadicTriadicAllScaleProved :
      Bool

    dyadicTriadicAllScaleProvedIsFalse :
      dyadicTriadicAllScaleProved ≡ false

    dyadicPentadicAllScaleProved :
      Bool

    dyadicPentadicAllScaleProvedIsFalse :
      dyadicPentadicAllScaleProved ≡ false

    triadicPentadicAllScaleProved :
      Bool

    triadicPentadicAllScaleProvedIsFalse :
      triadicPentadicAllScaleProved ≡ false

    proofStatusOpen :
      Bool

    proofStatusOpenIsTrue :
      proofStatusOpen ≡ true

    allScaleMutualOrthogonalityProved :
      Bool

    allScaleMutualOrthogonalityProvedIsFalse :
      allScaleMutualOrthogonalityProved ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ proofAttemptStatement

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    receiptBoundary :
      List String

open MutualOrthogonalityGeneralProofReceipt public

canonicalMutualOrthogonalityGeneralProofReceipt :
  MutualOrthogonalityGeneralProofReceipt
canonicalMutualOrthogonalityGeneralProofReceipt =
  record
    { scaleOneReceipt =
        Scale1.canonicalDyadicTriadicScale1InnerProductReceipt
    ; scaleOneCancels =
        refl
    ; priorReceipt =
        Prior.canonicalWaveletOrthogonalityProofReceipt
    ; priorAllScaleProofStillOpen =
        refl
    ; pairs =
        canonicalOrthogonalityPairs
    ; pairsAreCanonical =
        refl
    ; proofStatus =
        canonicalProofStatus
    ; proofStatusIsCanonical =
        refl
    ; mutualOrthogonalityProofAttempted =
        true
    ; mutualOrthogonalityProofAttemptedIsTrue =
        refl
    ; dyadicTriadicAllScaleProved =
        false
    ; dyadicTriadicAllScaleProvedIsFalse =
        refl
    ; dyadicPentadicAllScaleProved =
        false
    ; dyadicPentadicAllScaleProvedIsFalse =
        refl
    ; triadicPentadicAllScaleProved =
        false
    ; triadicPentadicAllScaleProvedIsFalse =
        refl
    ; proofStatusOpen =
        true
    ; proofStatusOpenIsTrue =
        refl
    ; allScaleMutualOrthogonalityProved =
        false
    ; allScaleMutualOrthogonalityProvedIsFalse =
        refl
    ; statement =
        proofAttemptStatement
    ; statementIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite dyadic/triadic checks support the route but do not prove all-scale orthogonality"
        ∷ "Dyadic/pentadic and triadic/pentadic estimates remain unproved"
        ∷ "A partition lemma or Gram-spectrum bound is still required"
        ∷ []
    }

mutualOrthogonalityGeneralProofKeepsNSFalse :
  clayNavierStokesPromoted
    canonicalMutualOrthogonalityGeneralProofReceipt
  ≡
  false
mutualOrthogonalityGeneralProofKeepsNSFalse =
  refl

