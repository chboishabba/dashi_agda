module DASHI.DCHoTT.UnificationCandidate where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.DCHoTT.InterpretationAdapter as DCHoTT
import DASHI.Papers.Unification.TheoremInterface as Unification

------------------------------------------------------------------------
-- DCHoTT-facing Unification candidate adapter.
--
-- This is only an interpretation surface: it presents the checked
-- DCHoTT adapter index beside the paper-facing unification theorem
-- interface, while preserving the explicit terminal-unification false flag.

data DCHoTTUnificationCandidateStatus : Set where
  dchottInterpretationOfUnificationCandidate_terminalFalse :
    DCHoTTUnificationCandidateStatus

canonicalDCHoTTUnificationCandidateSummary : List String
canonicalDCHoTTUnificationCandidateSummary =
  "DCHoTT-facing adapter imports the checked bridge-only DCHoTT interpretation index."
  ∷ "Unification theorem grammar and consumer surfaces come from the paper-facing interface."
  ∷ "UCT.1-UCT.4 remain open; UCT.5-UCT.8 remain fail-closed consumers."
  ∷ "No DCHoTT formal D-space equivalence, Im-reflection theorem, B0 promotion, or terminal unification is claimed."
  ∷ []

record DCHoTTUnificationCandidateAdapter : Setω where
  field
    status :
      DCHoTTUnificationCandidateStatus

    dchottInterpretationIndex :
      DCHoTT.DCHoTTInterpretationAdapterIndex

    unificationTheoremInterface :
      Unification.UnificationPaperTheoremInterface

    dchottAdapterNoPromotion :
      DCHoTT.noPromotionClaimed dchottInterpretationIndex ≡ true

    dchottAdapterNoFullRepoPort :
      DCHoTT.noFullRepoPortClaimed dchottInterpretationIndex ≡ true

    unificationTerminalPromotion :
      Bool

    unificationTerminalPromotionMatchesInterface :
      unificationTerminalPromotion
      ≡
      Unification.terminalUnificationPromoted unificationTheoremInterface

    unificationTerminalPromotionIsFalse :
      unificationTerminalPromotion ≡ false

    summary :
      List String

    summaryIsCanonical :
      summary ≡ canonicalDCHoTTUnificationCandidateSummary

open DCHoTTUnificationCandidateAdapter public

canonicalDCHoTTUnificationCandidateAdapter :
  DCHoTTUnificationCandidateAdapter
canonicalDCHoTTUnificationCandidateAdapter =
  record
    { status =
        dchottInterpretationOfUnificationCandidate_terminalFalse
    ; dchottInterpretationIndex =
        DCHoTT.canonicalDCHoTTInterpretationAdapterIndex
    ; unificationTheoremInterface =
        Unification.canonicalUnificationPaperTheoremInterface
    ; dchottAdapterNoPromotion =
        DCHoTT.noPromotionClaimedIsTrue
          DCHoTT.canonicalDCHoTTInterpretationAdapterIndex
    ; dchottAdapterNoFullRepoPort =
        DCHoTT.noFullRepoPortClaimedIsTrue
          DCHoTT.canonicalDCHoTTInterpretationAdapterIndex
    ; unificationTerminalPromotion =
        Unification.terminalUnificationPromoted
          Unification.canonicalUnificationPaperTheoremInterface
    ; unificationTerminalPromotionMatchesInterface =
        refl
    ; unificationTerminalPromotionIsFalse =
        Unification.unificationPaperInterfaceTerminalFalse
    ; summary =
        canonicalDCHoTTUnificationCandidateSummary
    ; summaryIsCanonical =
        refl
    }

dchottUnificationCandidateTerminalFalse :
  unificationTerminalPromotion canonicalDCHoTTUnificationCandidateAdapter
  ≡ false
dchottUnificationCandidateTerminalFalse =
  Unification.unificationPaperInterfaceTerminalFalse
