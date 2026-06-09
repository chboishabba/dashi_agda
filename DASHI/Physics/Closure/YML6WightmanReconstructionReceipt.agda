module DASHI.Physics.Closure.YML6WightmanReconstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WightmanReconstructionCandidateReceipt as Existing
import DASHI.Physics.Closure.YML5OSAxiomsForGaugeSectorReceipt as L5
import DASHI.Physics.Closure.YML4ContinuumLimitReceipt as L4
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3

data YML6WightmanReconstructionStatus : Set where
  wightmanReconstructionConditionallyReceiptedFromOS :
    YML6WightmanReconstructionStatus

data YML6WightmanAuthority : Set where
  osterwalderSchraderReconstructionTheorem :
    YML6WightmanAuthority
  schwingerFunctionsSatisfyOSAxioms :
    YML6WightmanAuthority
  reconstructedHilbertSpaceAndVacuum :
    YML6WightmanAuthority
  reconstructedWightmanFields :
    YML6WightmanAuthority

canonicalYML6WightmanAuthorities : List YML6WightmanAuthority
canonicalYML6WightmanAuthorities =
  osterwalderSchraderReconstructionTheorem
  ∷ schwingerFunctionsSatisfyOSAxioms
  ∷ reconstructedHilbertSpaceAndVacuum
  ∷ reconstructedWightmanFields
  ∷ []

data YML6WightmanPromotion : Set where

yml6WightmanPromotionImpossibleHere : YML6WightmanPromotion → ⊥
yml6WightmanPromotionImpossibleHere ()

yml6WightmanStatement : String
yml6WightmanStatement =
  "YML6 accepts OS reconstruction only as conditional authority over the YML5 candidate OS package, which remains conditional on candidate-only L3; Clay YM remains false."

record YML6WightmanReconstructionReceipt : Setω where
  field
    status :
      YML6WightmanReconstructionStatus

    osReceipt :
      L5.YML5OSAxiomsForGaugeSectorReceipt

    osAxiomsConditionallyComplete :
      L5.gaugeSectorOSAxiomsConditionallyComplete osReceipt ≡ true

    osReceiptKeepsClayFalse :
      L5.clayYangMillsPromoted osReceipt ≡ false

    osReceiptPriorL3StillCandidateOnly :
      L3.ymL3TightnessConstructed
        (L4.priorL3Receipt
          (L5.continuumLimitReceipt osReceipt))
        ≡ false

    priorCandidateReceipt :
      Existing.WightmanReconstructionCandidateReceipt

    priorCandidateKeptUnapplied :
      Existing.wightmanReconstructionApplied priorCandidateReceipt
        ≡ false

    conditionalOnYML5OSPackage :
      Bool
    conditionalOnYML5OSPackageIsTrue :
      conditionalOnYML5OSPackage ≡ true

    osReconstructionTheoremAccepted :
      Bool
    osReconstructionTheoremAcceptedIsTrue :
      osReconstructionTheoremAccepted ≡ true

    reconstructedHilbertSpaceCandidate :
      Bool
    reconstructedHilbertSpaceCandidateIsTrue :
      reconstructedHilbertSpaceCandidate ≡ true

    reconstructedVacuumCandidate :
      Bool
    reconstructedVacuumCandidateIsTrue :
      reconstructedVacuumCandidate ≡ true

    reconstructedWightmanFieldCandidate :
      Bool
    reconstructedWightmanFieldCandidateIsTrue :
      reconstructedWightmanFieldCandidate ≡ true

    wightmanYMCandidateConstructed :
      Bool
    wightmanYMCandidateConstructedIsTrue :
      wightmanYMCandidateConstructed ≡ true

    unconditionalWightmanReconstructionPromoted :
      Bool
    unconditionalWightmanReconstructionPromotedIsFalse :
      unconditionalWightmanReconstructionPromoted ≡ false

    clayYangMillsPromoted :
      Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool
    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    authorities :
      List YML6WightmanAuthority
    authoritiesAreCanonical :
      authorities ≡ canonicalYML6WightmanAuthorities

    statement :
      String
    statementIsCanonical :
      statement ≡ yml6WightmanStatement

    promotionFlags :
      List YML6WightmanPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML6WightmanReconstructionReceipt public

canonicalYML6WightmanReconstructionReceipt :
  YML6WightmanReconstructionReceipt
canonicalYML6WightmanReconstructionReceipt =
  record
    { status = wightmanReconstructionConditionallyReceiptedFromOS
    ; osReceipt = L5.canonicalYML5OSAxiomsForGaugeSectorReceipt
    ; osAxiomsConditionallyComplete = refl
    ; osReceiptKeepsClayFalse = refl
    ; osReceiptPriorL3StillCandidateOnly = refl
    ; priorCandidateReceipt =
        Existing.canonicalWightmanReconstructionCandidateReceipt
    ; priorCandidateKeptUnapplied = refl
    ; conditionalOnYML5OSPackage = true
    ; conditionalOnYML5OSPackageIsTrue = refl
    ; osReconstructionTheoremAccepted = true
    ; osReconstructionTheoremAcceptedIsTrue = refl
    ; reconstructedHilbertSpaceCandidate = true
    ; reconstructedHilbertSpaceCandidateIsTrue = refl
    ; reconstructedVacuumCandidate = true
    ; reconstructedVacuumCandidateIsTrue = refl
    ; reconstructedWightmanFieldCandidate = true
    ; reconstructedWightmanFieldCandidateIsTrue = refl
    ; wightmanYMCandidateConstructed = true
    ; wightmanYMCandidateConstructedIsTrue = refl
    ; unconditionalWightmanReconstructionPromoted = false
    ; unconditionalWightmanReconstructionPromotedIsFalse = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    ; terminalClayClaimPromoted = false
    ; terminalClayClaimPromotedIsFalse = refl
    ; authorities = canonicalYML6WightmanAuthorities
    ; authoritiesAreCanonical = refl
    ; statement = yml6WightmanStatement
    ; statementIsCanonical = refl
    ; promotionFlags = []
    ; promotionFlagsAreEmpty = refl
    ; receiptBoundary =
        "The OS reconstruction theorem is accepted as a theorem authority only after the candidate/conditional YML5 OS package is supplied"
        ∷ "The reconstructed Hilbert space, vacuum, and Wightman fields are candidate objects in that conditional scope"
        ∷ "The YML5 package still traces back to candidate-only/blocked L3 tightness"
        ∷ "The older unconditional Wightman candidate receipt remains unapplied"
        ∷ "No Clay YM or terminal Clay promotion follows"
        ∷ []
    }

yml6WightmanKeepsClayFalse :
  clayYangMillsPromoted canonicalYML6WightmanReconstructionReceipt
  ≡ false
yml6WightmanKeepsClayFalse = refl

yml6WightmanKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML6WightmanReconstructionReceipt
  ≡ false
yml6WightmanKeepsTerminalFalse = refl
