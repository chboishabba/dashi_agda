module DASHI.Physics.Closure.HaarMutualCoherenceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HaarFrameBoundsReceipt as Frame

------------------------------------------------------------------------
-- Dyadic/triadic/pentadic Haar mutual-coherence diagnostics.

data HaarCoherenceComputation : Set where
  dyadicTriadicScaleZero :
    HaarCoherenceComputation

  dyadicTriadicScaleOne :
    HaarCoherenceComputation

  dyadicPentadicStillTarget :
    HaarCoherenceComputation

  triadicPentadicStillTarget :
    HaarCoherenceComputation

canonicalHaarCoherenceComputations :
  List HaarCoherenceComputation
canonicalHaarCoherenceComputations =
  dyadicTriadicScaleZero
  ∷ dyadicTriadicScaleOne
  ∷ dyadicPentadicStillTarget
  ∷ triadicPentadicStillTarget
  ∷ []

data HaarCoherenceBlocker : Set where
  missingAllScaleGramSpectrumBound :
    HaarCoherenceBlocker

  missingDyadicPentadicUniformEstimate :
    HaarCoherenceBlocker

  missingTriadicPentadicUniformEstimate :
    HaarCoherenceBlocker

canonicalHaarCoherenceBlockers :
  List HaarCoherenceBlocker
canonicalHaarCoherenceBlockers =
  missingAllScaleGramSpectrumBound
  ∷ missingDyadicPentadicUniformEstimate
  ∷ missingTriadicPentadicUniformEstimate
  ∷ []

scaleZeroStatement : String
scaleZeroStatement =
  "<psi_2,psi_3> at scale zero is 0 for the symmetric mother-wavelet convention."

scaleOneStatement : String
scaleOneStatement =
  "<psi_2,1,0,psi_3,1,0> cancels to 0 under the supported Haar convention: sqrt(6) * (1/9 - 1/9)."

record HaarMutualCoherenceReceipt : Setω where
  field
    frameReceipt :
      Frame.HaarFrameBoundsReceipt

    frameBoundsStillOpen :
      Frame.rieszLowerBoundProved frameReceipt ≡ false

    computations :
      List HaarCoherenceComputation

    computationsAreCanonical :
      computations ≡ canonicalHaarCoherenceComputations

    scaleZeroInnerProductZero :
      Bool

    scaleZeroInnerProductZeroIsTrue :
      scaleZeroInnerProductZero ≡ true

    scaleZeroComputation :
      String

    scaleZeroComputationIsCanonical :
      scaleZeroComputation ≡ scaleZeroStatement

    scaleOneInnerProductZero :
      Bool

    scaleOneInnerProductZeroIsTrue :
      scaleOneInnerProductZero ≡ true

    scaleOneComputation :
      String

    scaleOneComputationIsCanonical :
      scaleOneComputation ≡ scaleOneStatement

    dyadicTriadicMutualOrthogonalityConjecture :
      Bool

    dyadicTriadicMutualOrthogonalityConjectureIsOpen :
      dyadicTriadicMutualOrthogonalityConjecture ≡ false

    mutualCoherenceDiagnosticRecorded :
      Bool

    mutualCoherenceDiagnosticRecordedIsTrue :
      mutualCoherenceDiagnosticRecorded ≡ true

    rieszFrameBoundProved :
      Bool

    rieszFrameBoundProvedIsFalse :
      rieszFrameBoundProved ≡ false

    blockers :
      List HaarCoherenceBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHaarCoherenceBlockers

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    receiptBoundary :
      List String

open HaarMutualCoherenceReceipt public

canonicalHaarMutualCoherenceReceipt :
  HaarMutualCoherenceReceipt
canonicalHaarMutualCoherenceReceipt =
  record
    { frameReceipt =
        Frame.canonicalHaarFrameBoundsReceipt
    ; frameBoundsStillOpen =
        refl
    ; computations =
        canonicalHaarCoherenceComputations
    ; computationsAreCanonical =
        refl
    ; scaleZeroInnerProductZero =
        true
    ; scaleZeroInnerProductZeroIsTrue =
        refl
    ; scaleZeroComputation =
        scaleZeroStatement
    ; scaleZeroComputationIsCanonical =
        refl
    ; scaleOneInnerProductZero =
        true
    ; scaleOneInnerProductZeroIsTrue =
        refl
    ; scaleOneComputation =
        scaleOneStatement
    ; scaleOneComputationIsCanonical =
        refl
    ; dyadicTriadicMutualOrthogonalityConjecture =
        false
    ; dyadicTriadicMutualOrthogonalityConjectureIsOpen =
        refl
    ; mutualCoherenceDiagnosticRecorded =
        true
    ; mutualCoherenceDiagnosticRecordedIsTrue =
        refl
    ; rieszFrameBoundProved =
        false
    ; rieszFrameBoundProvedIsFalse =
        refl
    ; blockers =
        canonicalHaarCoherenceBlockers
    ; blockersAreCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Scale-zero dyadic/triadic cancellation is recorded"
        ∷ "Scale-one dyadic/triadic cancellation is recorded under the supported Haar convention"
        ∷ "The all-scale orthogonality shortcut remains open; frame bounds still require a Gram-spectrum proof"
        ∷ "No Navier-Stokes or Clay promotion follows"
        ∷ []
    }

haarMutualCoherenceDoesNotPromoteNS :
  clayNavierStokesPromoted canonicalHaarMutualCoherenceReceipt ≡ false
haarMutualCoherenceDoesNotPromoteNS =
  refl
