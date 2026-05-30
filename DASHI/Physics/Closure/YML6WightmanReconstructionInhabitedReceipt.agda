module DASHI.Physics.Closure.YML6WightmanReconstructionInhabitedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML6WightmanReconstructionReceipt as L6

data YML6InhabitationCondition : Set where
  conditionalOnL5 :
    YML6InhabitationCondition

data YML6TheoremStatus : Set where
  theorem :
    YML6TheoremStatus

  conditionalTheorem :
    YML6TheoremStatus

  candidateConditionalTheorem :
    YML6TheoremStatus

data YML6Citation : Set where
  OS1975 :
    YML6Citation

data YML6TheoremAuthority : Set where
  citationAuthority :
    YML6Citation →
    YML6TheoremAuthority

data YML6InhabitedPromotion : Set where

yml6InhabitedPromotionImpossibleHere :
  YML6InhabitedPromotion →
  ⊥
yml6InhabitedPromotionImpossibleHere ()

yml6WightmanReconstructionInhabitedStatement : String
yml6WightmanReconstructionInhabitedStatement =
  "YML6 Wightman reconstruction is a candidate conditional theorem target: OS1975 applies only if the candidate L5 OS package is promoted, and that package still depends on uninhabited L3."

record YML6WightmanReconstructionInhabitedReceipt : Setω where
  field
    priorYML6Receipt :
      L6.YML6WightmanReconstructionReceipt

    priorYML6ConditionalOnL5 :
      L6.conditionalOnYML5OSPackage priorYML6Receipt ≡ true

    priorYML6WightmanCandidate :
      L6.wightmanYMCandidateConstructed priorYML6Receipt ≡ true

    priorYML6UnconditionalPromotionFalse :
      L6.unconditionalWightmanReconstructionPromoted priorYML6Receipt
        ≡ false

    priorYML6ClayFalse :
      L6.clayYangMillsPromoted priorYML6Receipt ≡ false

    priorYML6TerminalFalse :
      L6.terminalClayClaimPromoted priorYML6Receipt ≡ false

    ymL6Inhabited :
      YML6InhabitationCondition

    ymL6InhabitedIsConditionalOnL5 :
      ymL6Inhabited ≡ conditionalOnL5

    osReconstructionTheorem :
      YML6TheoremAuthority

    osReconstructionTheoremIsOS1975CitationAuthority :
      osReconstructionTheorem ≡ citationAuthority OS1975

    ymL6StatusUpgraded :
      YML6TheoremStatus

    ymL6StatusUpgradedIsCandidateConditionalTheorem :
      ymL6StatusUpgraded ≡ candidateConditionalTheorem

    theoremStatusBoundary :
      YML6TheoremStatus

    theoremStatusBoundaryIsTheorem :
      theoremStatusBoundary ≡ theorem

    conditionalOnL5OSPackage :
      Bool

    conditionalOnL5OSPackageIsTrue :
      conditionalOnL5OSPackage ≡ true

    yml6WightmanReconstructionCandidateOnly :
      Bool

    yml6WightmanReconstructionCandidateOnlyIsTrue :
      yml6WightmanReconstructionCandidateOnly ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ yml6WightmanReconstructionInhabitedStatement

    promotionFlags :
      List YML6InhabitedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML6WightmanReconstructionInhabitedReceipt public

canonicalYML6WightmanReconstructionInhabitedReceipt :
  YML6WightmanReconstructionInhabitedReceipt
canonicalYML6WightmanReconstructionInhabitedReceipt =
  record
    { priorYML6Receipt =
        L6.canonicalYML6WightmanReconstructionReceipt
    ; priorYML6ConditionalOnL5 =
        refl
    ; priorYML6WightmanCandidate =
        refl
    ; priorYML6UnconditionalPromotionFalse =
        refl
    ; priorYML6ClayFalse =
        refl
    ; priorYML6TerminalFalse =
        refl
    ; ymL6Inhabited =
        conditionalOnL5
    ; ymL6InhabitedIsConditionalOnL5 =
        refl
    ; osReconstructionTheorem =
        citationAuthority OS1975
    ; osReconstructionTheoremIsOS1975CitationAuthority =
        refl
    ; ymL6StatusUpgraded =
        candidateConditionalTheorem
    ; ymL6StatusUpgradedIsCandidateConditionalTheorem =
        refl
    ; theoremStatusBoundary =
        theorem
    ; theoremStatusBoundaryIsTheorem =
        refl
    ; conditionalOnL5OSPackage =
        true
    ; conditionalOnL5OSPackageIsTrue =
        refl
    ; yml6WightmanReconstructionCandidateOnly =
        true
    ; yml6WightmanReconstructionCandidateOnlyIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        yml6WightmanReconstructionInhabitedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "ymL6Inhabited is conditionalOnL5"
        ∷ "osReconstructionTheorem is citationAuthority OS1975"
        ∷ "ymL6StatusUpgraded is candidateConditionalTheorem because L5 still depends on uninhabited L3"
        ∷ "Clay Yang-Mills and terminal Clay promotions remain false"
        ∷ []
    }

yml6InhabitedIsConditionalOnL5 :
  ymL6Inhabited canonicalYML6WightmanReconstructionInhabitedReceipt
  ≡
  conditionalOnL5
yml6InhabitedIsConditionalOnL5 =
  refl

yml6InhabitedOSReconstructionTheoremIsOS1975 :
  osReconstructionTheorem canonicalYML6WightmanReconstructionInhabitedReceipt
  ≡
  citationAuthority OS1975
yml6InhabitedOSReconstructionTheoremIsOS1975 =
  refl

yml6InhabitedStatusUpgraded :
  ymL6StatusUpgraded canonicalYML6WightmanReconstructionInhabitedReceipt
  ≡
  candidateConditionalTheorem
yml6InhabitedStatusUpgraded =
  refl

yml6InhabitedKeepsClayFalse :
  clayYangMillsPromoted canonicalYML6WightmanReconstructionInhabitedReceipt
  ≡
  false
yml6InhabitedKeepsClayFalse =
  refl

yml6InhabitedKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML6WightmanReconstructionInhabitedReceipt
  ≡
  false
yml6InhabitedKeepsTerminalFalse =
  refl
