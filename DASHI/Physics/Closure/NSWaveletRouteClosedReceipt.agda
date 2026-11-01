module DASHI.Physics.Closure.NSWaveletRouteClosedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HilbertSchmidtBoundGramReceipt as HS

------------------------------------------------------------------------
-- Closure of the multibase Haar-frame route for Navier-Stokes.
--
-- This receipt records a negative diagnostic.  The unrestricted 2/3/5 Haar
-- union fails on constants, and the zero-mean restricted off-diagonal Gram
-- route has divergent Hilbert-Schmidt control.  The carrier must therefore
-- use a different analytic interface, such as the prime-band
-- Littlewood-Paley route recorded in the follow-up receipt.

data NSWaveletRouteClosedFact : Set where
  unrestrictedConstantObstruction :
    NSWaveletRouteClosedFact

  zeroMeanDoesNotChangeHaarGramEntries :
    NSWaveletRouteClosedFact

  hilbertSchmidtControlDiverges :
    NSWaveletRouteClosedFact

  frameLowerBoundNotEstablished :
    NSWaveletRouteClosedFact

  littlewoodPaleyReplacementNeeded :
    NSWaveletRouteClosedFact

canonicalNSWaveletRouteClosedFacts :
  List NSWaveletRouteClosedFact
canonicalNSWaveletRouteClosedFacts =
  unrestrictedConstantObstruction
  ∷ zeroMeanDoesNotChangeHaarGramEntries
  ∷ hilbertSchmidtControlDiverges
  ∷ frameLowerBoundNotEstablished
  ∷ littlewoodPaleyReplacementNeeded
  ∷ []

data NSWaveletRouteClosedBlocker : Set where
  missingFrameLowerBound :
    NSWaveletRouteClosedBlocker

  missingPrimeBandParaproductEstimate :
    NSWaveletRouteClosedBlocker

  missingNonlinearTermPassage :
    NSWaveletRouteClosedBlocker

  missingClayRegularityArgument :
    NSWaveletRouteClosedBlocker

canonicalNSWaveletRouteClosedBlockers :
  List NSWaveletRouteClosedBlocker
canonicalNSWaveletRouteClosedBlockers =
  missingFrameLowerBound
  ∷ missingPrimeBandParaproductEstimate
  ∷ missingNonlinearTermPassage
  ∷ missingClayRegularityArgument
  ∷ []

data NSWaveletRoutePromotion : Set where

nsWaveletRoutePromotionImpossibleHere :
  NSWaveletRoutePromotion →
  ⊥
nsWaveletRoutePromotionImpossibleHere ()

nsWaveletRouteClosedStatement : String
nsWaveletRouteClosedStatement =
  "The 2/3/5 Haar-frame route is closed as a Navier-Stokes proof route: constants obstruct the unrestricted system and Hilbert-Schmidt control diverges on the zero-mean Gram route."

record NSWaveletRouteClosedReceipt : Setω where
  field
    hilbertSchmidtReceipt :
      HS.HilbertSchmidtBoundGramReceipt

    hilbertSchmidtDivergenceRecorded :
      HS.hilbertSchmidtNormGram23Diverges hilbertSchmidtReceipt ≡ true

    hilbertSchmidtFrameLowerBoundFailed :
      HS.restrictedFrameLowerBoundProved hilbertSchmidtReceipt ≡ false

    facts :
      List NSWaveletRouteClosedFact

    factsAreCanonical :
      facts ≡ canonicalNSWaveletRouteClosedFacts

    nsWaveletRouteFullyClosed :
      Bool

    nsWaveletRouteFullyClosedIsTrue :
      nsWaveletRouteFullyClosed ≡ true

    unrestrictedHaarFrameFailed :
      Bool

    unrestrictedHaarFrameFailedIsTrue :
      unrestrictedHaarFrameFailed ≡ true

    zeroMeanFrameRouteFailed :
      Bool

    zeroMeanFrameRouteFailedIsTrue :
      zeroMeanFrameRouteFailed ≡ true

    frameLowerBoundMinusInfinityDiagnostic :
      Bool

    frameLowerBoundMinusInfinityDiagnosticIsTrue :
      frameLowerBoundMinusInfinityDiagnostic ≡ true

    alternativeApproachRequired :
      Bool

    alternativeApproachRequiredIsTrue :
      alternativeApproachRequired ≡ true

    nsWeakSolutionPromoted :
      Bool

    nsWeakSolutionPromotedIsFalse :
      nsWeakSolutionPromoted ≡ false

    navierStokesRegularityPromoted :
      Bool

    navierStokesRegularityPromotedIsFalse :
      navierStokesRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List NSWaveletRouteClosedBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSWaveletRouteClosedBlockers

    promotionFlags :
      List NSWaveletRoutePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsWaveletRouteClosedStatement

    receiptBoundary :
      List String

open NSWaveletRouteClosedReceipt public

canonicalNSWaveletRouteClosedReceipt :
  NSWaveletRouteClosedReceipt
canonicalNSWaveletRouteClosedReceipt =
  record
    { hilbertSchmidtReceipt =
        HS.canonicalHilbertSchmidtBoundGramReceipt
    ; hilbertSchmidtDivergenceRecorded =
        refl
    ; hilbertSchmidtFrameLowerBoundFailed =
        refl
    ; facts =
        canonicalNSWaveletRouteClosedFacts
    ; factsAreCanonical =
        refl
    ; nsWaveletRouteFullyClosed =
        true
    ; nsWaveletRouteFullyClosedIsTrue =
        refl
    ; unrestrictedHaarFrameFailed =
        true
    ; unrestrictedHaarFrameFailedIsTrue =
        refl
    ; zeroMeanFrameRouteFailed =
        true
    ; zeroMeanFrameRouteFailedIsTrue =
        refl
    ; frameLowerBoundMinusInfinityDiagnostic =
        true
    ; frameLowerBoundMinusInfinityDiagnosticIsTrue =
        refl
    ; alternativeApproachRequired =
        true
    ; alternativeApproachRequiredIsTrue =
        refl
    ; nsWeakSolutionPromoted =
        false
    ; nsWeakSolutionPromotedIsFalse =
        refl
    ; navierStokesRegularityPromoted =
        false
    ; navierStokesRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalNSWaveletRouteClosedBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsWaveletRouteClosedStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Unrestricted 2/3/5 Haar frame route fails on constant functions"
        ∷ "Zero-mean restriction does not change Haar-Haar Gram entries"
        ∷ "Hilbert-Schmidt off-diagonal control diverges in the recorded route"
        ∷ "No NS weak-solution, regularity, or Clay promotion follows"
        ∷ []
    }

nsWaveletRouteClosedKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSWaveletRouteClosedReceipt ≡ false
nsWaveletRouteClosedKeepsClayFalse =
  refl

nsWaveletRouteNoPromotion :
  NSWaveletRoutePromotion →
  ⊥
nsWaveletRouteNoPromotion =
  nsWaveletRoutePromotionImpossibleHere
