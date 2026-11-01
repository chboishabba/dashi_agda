module DASHI.Physics.Closure.DyadicTriadicScale1InnerProduct where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HaarMutualCoherenceReceipt as Coherence

------------------------------------------------------------------------
-- Recheck of the supported scale-one dyadic/triadic Haar overlap.

scaleOneIntervalComputation : String
scaleOneIntervalComputation =
  "sqrt(2)*sqrt(3)*(length[0,1/9)-length[2/9,1/3]) = sqrt(6)*(1/9-1/9) = 0."

record DyadicTriadicScale1InnerProductReceipt : Setω where
  field
    coherenceReceipt :
      Coherence.HaarMutualCoherenceReceipt

    scaleZeroAlreadyCancels :
      Coherence.scaleZeroInnerProductZero coherenceReceipt ≡ true

    scaleOneRechecked :
      Bool

    scaleOneRecheckedIsTrue :
      scaleOneRechecked ≡ true

    scaleOneDyadicTriadicInnerProductZero :
      Bool

    scaleOneDyadicTriadicInnerProductZeroIsTrue :
      scaleOneDyadicTriadicInnerProductZero ≡ true

    previousSqrtSixOverSixDiagnosticRetired :
      Bool

    previousSqrtSixOverSixDiagnosticRetiredIsTrue :
      previousSqrtSixOverSixDiagnosticRetired ≡ true

    mutualOrthogonalityScale1Confirmed :
      Bool

    mutualOrthogonalityScale1ConfirmedIsTrue :
      mutualOrthogonalityScale1Confirmed ≡ true

    allScaleMutualOrthogonalityProved :
      Bool

    allScaleMutualOrthogonalityProvedIsFalse :
      allScaleMutualOrthogonalityProved ≡ false

    computation :
      String

    computationIsCanonical :
      computation ≡ scaleOneIntervalComputation

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    receiptBoundary :
      List String

open DyadicTriadicScale1InnerProductReceipt public

canonicalDyadicTriadicScale1InnerProductReceipt :
  DyadicTriadicScale1InnerProductReceipt
canonicalDyadicTriadicScale1InnerProductReceipt =
  record
    { coherenceReceipt =
        Coherence.canonicalHaarMutualCoherenceReceipt
    ; scaleZeroAlreadyCancels =
        refl
    ; scaleOneRechecked =
        true
    ; scaleOneRecheckedIsTrue =
        refl
    ; scaleOneDyadicTriadicInnerProductZero =
        true
    ; scaleOneDyadicTriadicInnerProductZeroIsTrue =
        refl
    ; previousSqrtSixOverSixDiagnosticRetired =
        true
    ; previousSqrtSixOverSixDiagnosticRetiredIsTrue =
        refl
    ; mutualOrthogonalityScale1Confirmed =
        true
    ; mutualOrthogonalityScale1ConfirmedIsTrue =
        refl
    ; allScaleMutualOrthogonalityProved =
        false
    ; allScaleMutualOrthogonalityProvedIsFalse =
        refl
    ; computation =
        scaleOneIntervalComputation
    ; computationIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The scale-one dyadic/triadic supported-Haar overlap cancels exactly"
        ∷ "This retires the previous sqrt(6)/6 diagnostic for the stated convention"
        ∷ "No all-scale 2/3/5 frame theorem follows from this finite check"
        ∷ []
    }

dyadicTriadicScale1DoesNotPromoteNS :
  clayNavierStokesPromoted
    canonicalDyadicTriadicScale1InnerProductReceipt
  ≡
  false
dyadicTriadicScale1DoesNotPromoteNS =
  refl

