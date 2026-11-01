module DASHI.Physics.Closure.GramMatrixSpectrumBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GramMatrix2x3BoundsReceipt as G23

------------------------------------------------------------------------
-- NS W2 frame analysis: Gram-spectrum lower-bound route.

data GramMatrixSpectrumRoute : Set where
  gershgorinDiscEstimate :
    GramMatrixSpectrumRoute

  mutualCoherenceSummation :
    GramMatrixSpectrumRoute

  finiteTruncationAudit :
    GramMatrixSpectrumRoute

canonicalGramMatrixSpectrumRoutes : List GramMatrixSpectrumRoute
canonicalGramMatrixSpectrumRoutes =
  gershgorinDiscEstimate
  ∷ mutualCoherenceSummation
  ∷ finiteTruncationAudit
  ∷ []

data GramMatrixSpectrumStatus : Set where
  gershgorinLowerBoundNonpositive :
    GramMatrixSpectrumStatus

  spectrumRouteFailsClosed :
    GramMatrixSpectrumStatus

  frameLowerBoundOpen :
    GramMatrixSpectrumStatus

canonicalGramMatrixSpectrumStatus : List GramMatrixSpectrumStatus
canonicalGramMatrixSpectrumStatus =
  gershgorinLowerBoundNonpositive
  ∷ spectrumRouteFailsClosed
  ∷ frameLowerBoundOpen
  ∷ []

data GramMatrixSpectrumBlocker : Set where
  rowSumBoundExceedsDiagonal :
    GramMatrixSpectrumBlocker

  missingPositiveUniformInfimum :
    GramMatrixSpectrumBlocker

  missingInfiniteGramOperatorSpectrum :
    GramMatrixSpectrumBlocker

canonicalGramMatrixSpectrumBlockers : List GramMatrixSpectrumBlocker
canonicalGramMatrixSpectrumBlockers =
  rowSumBoundExceedsDiagonal
  ∷ missingPositiveUniformInfimum
  ∷ missingInfiniteGramOperatorSpectrum
  ∷ []

data GramMatrixSpectrumPromotionReceipt : Set where

gramMatrixSpectrumPromotionImpossibleHere :
  GramMatrixSpectrumPromotionReceipt →
  ⊥
gramMatrixSpectrumPromotionImpossibleHere ()

gershgorinFailureDiagnostic : String
gershgorinFailureDiagnostic =
  "Gershgorin lower bound route fails closed: diagonal minus accumulated coarse cross-term row sum is nonpositive, so no uniform positive Gram-spectrum lower bound is certified"

record GramMatrixSpectrumBoundReceipt : Setω where
  field
    gram2x3Receipt :
      G23.GramMatrix2x3BoundsReceipt

    gram2x3LowerBoundStillOpen :
      G23.uniformGramLowerBoundProved gram2x3Receipt ≡ false

    truncationDepth :
      Nat

    routes :
      List GramMatrixSpectrumRoute

    routesAreCanonical :
      routes ≡ canonicalGramMatrixSpectrumRoutes

    status :
      List GramMatrixSpectrumStatus

    statusIsCanonical :
      status ≡ canonicalGramMatrixSpectrumStatus

    diagnostic :
      String

    diagnosticIsCanonical :
      diagnostic ≡ gershgorinFailureDiagnostic

    gershgorinLowerBoundPositive :
      Bool

    gershgorinLowerBoundPositiveIsFalse :
      gershgorinLowerBoundPositive ≡ false

    uniformSpectrumLowerBoundProved :
      Bool

    uniformSpectrumLowerBoundProvedIsFalse :
      uniformSpectrumLowerBoundProved ≡ false

    lowerFrameBoundPromoted :
      Bool

    lowerFrameBoundPromotedIsFalse :
      lowerFrameBoundPromoted ≡ false

    navierStokesRegularityPromoted :
      Bool

    navierStokesRegularityPromotedIsFalse :
      navierStokesRegularityPromoted ≡ false

    clayRegularityPromoted :
      Bool

    clayRegularityPromotedIsFalse :
      clayRegularityPromoted ≡ false

    blockers :
      List GramMatrixSpectrumBlocker

    blockersAreCanonical :
      blockers ≡ canonicalGramMatrixSpectrumBlockers

    promotionReceipts :
      List GramMatrixSpectrumPromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    receiptBoundary :
      List String

open GramMatrixSpectrumBoundReceipt public

canonicalGramMatrixSpectrumBoundReceipt :
  GramMatrixSpectrumBoundReceipt
canonicalGramMatrixSpectrumBoundReceipt =
  record
    { gram2x3Receipt =
        G23.canonicalGramMatrix2x3BoundsReceipt
    ; gram2x3LowerBoundStillOpen =
        refl
    ; truncationDepth =
        0
    ; routes =
        canonicalGramMatrixSpectrumRoutes
    ; routesAreCanonical =
        refl
    ; status =
        canonicalGramMatrixSpectrumStatus
    ; statusIsCanonical =
        refl
    ; diagnostic =
        gershgorinFailureDiagnostic
    ; diagnosticIsCanonical =
        refl
    ; gershgorinLowerBoundPositive =
        false
    ; gershgorinLowerBoundPositiveIsFalse =
        refl
    ; uniformSpectrumLowerBoundProved =
        false
    ; uniformSpectrumLowerBoundProvedIsFalse =
        refl
    ; lowerFrameBoundPromoted =
        false
    ; lowerFrameBoundPromotedIsFalse =
        refl
    ; navierStokesRegularityPromoted =
        false
    ; navierStokesRegularityPromotedIsFalse =
        refl
    ; clayRegularityPromoted =
        false
    ; clayRegularityPromotedIsFalse =
        refl
    ; blockers =
        canonicalGramMatrixSpectrumBlockers
    ; blockersAreCanonical =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; receiptBoundary =
        "The Gershgorin route is recorded as a negative diagnostic"
        ∷ "The lower bound is fail-closed because the certified coarse row sum can dominate the diagonal"
        ∷ "No lower frame bound, NS regularity theorem, or Clay promotion follows"
        ∷ []
    }

gramMatrixSpectrumBoundDoesNotPromoteNS :
  navierStokesRegularityPromoted canonicalGramMatrixSpectrumBoundReceipt
  ≡
  false
gramMatrixSpectrumBoundDoesNotPromoteNS =
  refl
