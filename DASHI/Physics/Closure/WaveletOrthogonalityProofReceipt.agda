module DASHI.Physics.Closure.WaveletOrthogonalityProofReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HaarMutualCoherenceReceipt as Coherence

------------------------------------------------------------------------
-- All-scale orthogonality proof attempt.

data WaveletPair : Set where
  dyadicTriadic :
    WaveletPair

  dyadicPentadic :
    WaveletPair

  triadicPentadic :
    WaveletPair

canonicalWaveletPairs : List WaveletPair
canonicalWaveletPairs =
  dyadicTriadic
  ∷ dyadicPentadic
  ∷ triadicPentadic
  ∷ []

data WaveletOrthogonalityStatus : Set where
  scaleZeroCancellation :
    WaveletOrthogonalityStatus

  scaleOneCounterexample :
    WaveletOrthogonalityStatus

  uniformCoherenceStillNeeded :
    WaveletOrthogonalityStatus

canonicalWaveletOrthogonalityStatus :
  List WaveletOrthogonalityStatus
canonicalWaveletOrthogonalityStatus =
  scaleZeroCancellation
  ∷ scaleOneCounterexample
  ∷ uniformCoherenceStillNeeded
  ∷ []

counterexampleStatement : String
counterexampleStatement =
  "The dyadic/triadic standard Haar pair at scale one has inner product sqrt(6)/6, so pairwise all-scale orthogonality is false."

record WaveletOrthogonalityProofReceipt : Setω where
  field
    coherenceReceipt :
      Coherence.HaarMutualCoherenceReceipt

    scaleOneCounterexampleAvailable :
      Coherence.scaleOneInnerProductZero coherenceReceipt ≡ false

    pairs :
      List WaveletPair

    pairsAreCanonical :
      pairs ≡ canonicalWaveletPairs

    status :
      List WaveletOrthogonalityStatus

    statusIsCanonical :
      status ≡ canonicalWaveletOrthogonalityStatus

    literalMutualOrthogonalityProved :
      Bool

    literalMutualOrthogonalityProvedIsFalse :
      literalMutualOrthogonalityProved ≡ false

    literalMutualOrthogonalityDisproved :
      Bool

    literalMutualOrthogonalityDisprovedIsTrue :
      literalMutualOrthogonalityDisproved ≡ true

    counterexample :
      String

    counterexampleIsCanonical :
      counterexample ≡ counterexampleStatement

    frameBoundRouteStillOpen :
      Bool

    frameBoundRouteStillOpenIsTrue :
      frameBoundRouteStillOpen ≡ true

    rieszBasisProved :
      Bool

    rieszBasisProvedIsFalse :
      rieszBasisProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    receiptBoundary :
      List String

open WaveletOrthogonalityProofReceipt public

canonicalWaveletOrthogonalityProofReceipt :
  WaveletOrthogonalityProofReceipt
canonicalWaveletOrthogonalityProofReceipt =
  record
    { coherenceReceipt =
        Coherence.canonicalHaarMutualCoherenceReceipt
    ; scaleOneCounterexampleAvailable =
        refl
    ; pairs =
        canonicalWaveletPairs
    ; pairsAreCanonical =
        refl
    ; status =
        canonicalWaveletOrthogonalityStatus
    ; statusIsCanonical =
        refl
    ; literalMutualOrthogonalityProved =
        false
    ; literalMutualOrthogonalityProvedIsFalse =
        refl
    ; literalMutualOrthogonalityDisproved =
        true
    ; literalMutualOrthogonalityDisprovedIsTrue =
        refl
    ; counterexample =
        counterexampleStatement
    ; counterexampleIsCanonical =
        refl
    ; frameBoundRouteStillOpen =
        true
    ; frameBoundRouteStillOpenIsTrue =
        refl
    ; rieszBasisProved =
        false
    ; rieszBasisProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The simple orthogonality route is closed negatively"
        ∷ "A bounded Gram operator or frame-bound argument is still required"
        ∷ "The 2/3/5 wavelet bridge remains a candidate, not an inhabited Archimedean compactness proof"
        ∷ []
    }

waveletOrthogonalityProofDoesNotPromoteNS :
  clayNavierStokesPromoted canonicalWaveletOrthogonalityProofReceipt
  ≡
  false
waveletOrthogonalityProofDoesNotPromoteNS =
  refl

