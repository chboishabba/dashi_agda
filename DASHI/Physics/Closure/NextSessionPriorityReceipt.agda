module DASHI.Physics.Closure.NextSessionPriorityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ResidualBlockersSummaryReceipt as Blockers

------------------------------------------------------------------------
-- Ordered next-session research priorities.

data NextSessionPriority : Set where
  vubNLOFromCarrierRG :
    NextSessionPriority

  deg23HilbertModularVol :
    NextSessionPriority

  waveletOrthogonalityProof :
    NextSessionPriority

canonicalNextSessionPriorities : List NextSessionPriority
canonicalNextSessionPriorities =
  vubNLOFromCarrierRG
  ∷ deg23HilbertModularVol
  ∷ waveletOrthogonalityProof
  ∷ []

vubPriorityStatement : String
vubPriorityStatement =
  "Confirm whether the alpha_s(m_b)/pi NLO correction in the degree-28 Vub diagnostic is carrier-derived rather than an external PDG insertion."

deg23PriorityStatement : String
deg23PriorityStatement =
  "Compute the Hilbert modular volume for Q(sqrt(21)) or the appropriate Shimura surface to replace the underived deg23 pattern."

waveletPriorityStatement : String
waveletPriorityStatement =
  "Prove or disprove the all-scale 2/3/5 wavelet orthogonality/frame-bound claim."

record NextSessionPriorityReceipt : Setω where
  field
    blockerSummary :
      Blockers.ResidualBlockersSummaryReceipt

    blockersTerminalStillFalse :
      Blockers.terminalClaimPromoted blockerSummary ≡ false

    priorities :
      List NextSessionPriority

    prioritiesAreCanonical :
      priorities ≡ canonicalNextSessionPriorities

    nextSessionPrioritiesRecorded :
      Bool

    nextSessionPrioritiesRecordedIsTrue :
      nextSessionPrioritiesRecorded ≡ true

    vubPriority :
      String

    vubPriorityIsCanonical :
      vubPriority ≡ vubPriorityStatement

    deg23Priority :
      String

    deg23PriorityIsCanonical :
      deg23Priority ≡ deg23PriorityStatement

    waveletPriority :
      String

    waveletPriorityIsCanonical :
      waveletPriority ≡ waveletPriorityStatement

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    receiptBoundary :
      List String

open NextSessionPriorityReceipt public

canonicalNextSessionPriorityReceipt : NextSessionPriorityReceipt
canonicalNextSessionPriorityReceipt =
  record
    { blockerSummary =
        Blockers.canonicalResidualBlockersSummaryReceipt
    ; blockersTerminalStillFalse =
        refl
    ; priorities =
        canonicalNextSessionPriorities
    ; prioritiesAreCanonical =
        refl
    ; nextSessionPrioritiesRecorded =
        true
    ; nextSessionPrioritiesRecordedIsTrue =
        refl
    ; vubPriority =
        vubPriorityStatement
    ; vubPriorityIsCanonical =
        refl
    ; deg23Priority =
        deg23PriorityStatement
    ; deg23PriorityIsCanonical =
        refl
    ; waveletPriority =
        waveletPriorityStatement
    ; waveletPriorityIsCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The list is a next-session queue, not a completed proof"
        ∷ "All Clay and terminal promotion flags remain false"
        ∷ []
    }

nextSessionPriorityKeepsTerminalFalse :
  terminalUnificationPromoted canonicalNextSessionPriorityReceipt
  ≡
  false
nextSessionPriorityKeepsTerminalFalse =
  refl

