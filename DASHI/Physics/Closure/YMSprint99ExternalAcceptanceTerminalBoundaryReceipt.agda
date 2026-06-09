module DASHI.Physics.Closure.YMSprint99ExternalAcceptanceTerminalBoundaryReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSprint98ClayStatementBoundaryCandidateReceipt as Sprint98

------------------------------------------------------------------------
-- Sprint 99 external-acceptance terminal boundary.
--
-- Sprint 98 supplied the internal Clay statement boundary candidate.  This
-- final receipt records that the remaining ExternalAcceptanceToken is not a
-- mathematical theorem object and cannot be self-issued by the repo.
--
-- Therefore:
--   internal candidate chain complete in the receipt layer;
--   external acceptance unavailable inside DASHI;
--   Clay/YM promotion remains false.

internalCandidateChainCompleteInRepo : Bool
internalCandidateChainCompleteInRepo = true

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

externalAcceptanceTokenRepoInternal : Bool
externalAcceptanceTokenRepoInternal = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data ExternalAcceptanceToken : Set where

externalAcceptanceTokenImpossibleHere :
  ExternalAcceptanceToken →
  ⊥
externalAcceptanceTokenImpossibleHere ()

data ClayYangMillsPromotion : Set where

clayYangMillsPromotionImpossibleHere :
  ClayYangMillsPromotion →
  ⊥
clayYangMillsPromotionImpossibleHere ()

record ExternalAcceptanceTerminalBoundary : Set₁ where
  constructor mkExternalAcceptanceTerminalBoundary
  field
    clayStatementBoundaryCandidate :
      Sprint98.ClayStatementBoundaryDischarged
    externalAcceptanceDescription :
      String
    internalCandidateComplete :
      internalCandidateChainCompleteInRepo ≡ true
    externalAcceptanceUnavailable :
      externalAcceptanceTokenAvailable ≡ false
    externalAcceptanceNotRepoInternal :
      externalAcceptanceTokenRepoInternal ≡ false
    noExternalAcceptanceWitness :
      ExternalAcceptanceToken → ⊥
    noClayPromotionWitness :
      ClayYangMillsPromotion → ⊥
    noClayPromotion :
      clayYangMillsPromoted ≡ false

sprint99Route : String
sprint99Route =
  "ClayStatementBoundaryDischarged + no repo-internal ExternalAcceptanceToken -> terminal fail-closed Clay promotion boundary."

sprint99Remaining : String
sprint99Remaining =
  "Remaining after Sprint 99: external peer review/community/Clay acceptance outside the repo."

canonicalExternalAcceptanceTerminalBoundary :
  ExternalAcceptanceTerminalBoundary
canonicalExternalAcceptanceTerminalBoundary =
  mkExternalAcceptanceTerminalBoundary
    Sprint98.canonicalClayStatementBoundaryDischarged
    "External acceptance is a governance/review artifact, not an Agda proof object available inside the repository"
    refl
    refl
    refl
    externalAcceptanceTokenImpossibleHere
    clayYangMillsPromotionImpossibleHere
    refl

record YMSprint99ExternalAcceptanceTerminalBoundaryReceipt : Set₁ where
  field
    sprint98ClayStatementBoundaryCandidateReceipt :
      Sprint98.YMSprint98ClayStatementBoundaryCandidateReceipt
    terminalBoundary :
      ExternalAcceptanceTerminalBoundary
    internalCandidateComplete :
      internalCandidateChainCompleteInRepo ≡ true
    externalAcceptanceUnavailable :
      externalAcceptanceTokenAvailable ≡ false
    externalAcceptanceNotRepoInternal :
      externalAcceptanceTokenRepoInternal ≡ false
    route :
      sprint99Route ≡
      "ClayStatementBoundaryDischarged + no repo-internal ExternalAcceptanceToken -> terminal fail-closed Clay promotion boundary."
    remaining :
      sprint99Remaining ≡
      "Remaining after Sprint 99: external peer review/community/Clay acceptance outside the repo."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint99ExternalAcceptanceTerminalBoundaryReceipt :
  YMSprint99ExternalAcceptanceTerminalBoundaryReceipt
canonicalYMSprint99ExternalAcceptanceTerminalBoundaryReceipt =
  record
    { sprint98ClayStatementBoundaryCandidateReceipt =
        Sprint98.canonicalYMSprint98ClayStatementBoundaryCandidateReceipt
    ; terminalBoundary =
        canonicalExternalAcceptanceTerminalBoundary
    ; internalCandidateComplete =
        refl
    ; externalAcceptanceUnavailable =
        refl
    ; externalAcceptanceNotRepoInternal =
        refl
    ; route =
        refl
    ; remaining =
        refl
    ; noClayPromotion =
        refl
    }
