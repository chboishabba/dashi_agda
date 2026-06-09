module DASHI.Physics.Closure.ProgrammeStateAfterComputationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Programme state after computation receipt.
--
-- This C4 receipt records the post-computation upgrades and the remaining
-- gaps without promoting any terminal or Clay claim.

data ProgrammeStateAfterComputationStatus : Set where
  programmeStateAfterComputationRecordedNoPromotion :
    ProgrammeStateAfterComputationStatus

data ProgrammeComputationUpgrade : Set where
  nsFlowPreservationUpgrade :
    ProgrammeComputationUpgrade

  ymShimuraTowerUpgrade :
    ProgrammeComputationUpgrade

  ckmCPPhaseUpgrade :
    ProgrammeComputationUpgrade

canonicalProgrammeComputationUpgrades :
  List ProgrammeComputationUpgrade
canonicalProgrammeComputationUpgrades =
  nsFlowPreservationUpgrade
  ∷ ymShimuraTowerUpgrade
  ∷ ckmCPPhaseUpgrade
  ∷ []

data ProgrammeRemainingGap : Set where
  nsUniformityGap :
    ProgrammeRemainingGap

  ymUniversalityHyperbolicVsEuclideanGap :
    ProgrammeRemainingGap

  ckmFormalAtkinLehnerDerivationGap :
    ProgrammeRemainingGap

canonicalProgrammeRemainingGaps :
  List ProgrammeRemainingGap
canonicalProgrammeRemainingGaps =
  nsUniformityGap
  ∷ ymUniversalityHyperbolicVsEuclideanGap
  ∷ ckmFormalAtkinLehnerDerivationGap
  ∷ []

data ProgrammeStateAfterComputationPromotion : Set where

programmeStateAfterComputationPromotionImpossibleHere :
  ProgrammeStateAfterComputationPromotion →
  ⊥
programmeStateAfterComputationPromotionImpossibleHere ()

programmeStateAfterComputationStatement : String
programmeStateAfterComputationStatement =
  "C4 programme state after computation: upgrades recorded are NS flow preservation, YM Shimura tower, and CKM CP phase; remaining gaps are NS uniformity, YM universality hyperbolic-vs-Euclidean, and CKM formal Atkin-Lehner derivation; terminal and Clay promotions remain false."

record ProgrammeStateAfterComputationReceipt : Setω where
  field
    status :
      ProgrammeStateAfterComputationStatus

    upgrades :
      List ProgrammeComputationUpgrade

    upgradesAreCanonical :
      upgrades ≡ canonicalProgrammeComputationUpgrades

    remainingGaps :
      List ProgrammeRemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalProgrammeRemainingGaps

    nsFlowPreservationRecorded :
      Bool

    nsFlowPreservationRecordedIsTrue :
      nsFlowPreservationRecorded ≡ true

    ymShimuraTowerRecorded :
      Bool

    ymShimuraTowerRecordedIsTrue :
      ymShimuraTowerRecorded ≡ true

    ckmCPPhaseRecorded :
      Bool

    ckmCPPhaseRecordedIsTrue :
      ckmCPPhaseRecorded ≡ true

    nsUniformityOpen :
      Bool

    nsUniformityOpenIsTrue :
      nsUniformityOpen ≡ true

    ymUniversalityHyperbolicVsEuclideanOpen :
      Bool

    ymUniversalityHyperbolicVsEuclideanOpenIsTrue :
      ymUniversalityHyperbolicVsEuclideanOpen ≡ true

    ckmFormalAtkinLehnerDerivationOpen :
      Bool

    ckmFormalAtkinLehnerDerivationOpenIsTrue :
      ckmFormalAtkinLehnerDerivationOpen ≡ true

    computationStateComplete :
      Bool

    computationStateCompleteIsTrue :
      computationStateComplete ≡ true

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

    promotionFlags :
      List ProgrammeStateAfterComputationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ programmeStateAfterComputationStatement

    receiptBoundary :
      List String

open ProgrammeStateAfterComputationReceipt public

canonicalProgrammeStateAfterComputationReceipt :
  ProgrammeStateAfterComputationReceipt
canonicalProgrammeStateAfterComputationReceipt =
  record
    { status =
        programmeStateAfterComputationRecordedNoPromotion
    ; upgrades =
        canonicalProgrammeComputationUpgrades
    ; upgradesAreCanonical =
        refl
    ; remainingGaps =
        canonicalProgrammeRemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; nsFlowPreservationRecorded =
        true
    ; nsFlowPreservationRecordedIsTrue =
        refl
    ; ymShimuraTowerRecorded =
        true
    ; ymShimuraTowerRecordedIsTrue =
        refl
    ; ckmCPPhaseRecorded =
        true
    ; ckmCPPhaseRecordedIsTrue =
        refl
    ; nsUniformityOpen =
        true
    ; nsUniformityOpenIsTrue =
        refl
    ; ymUniversalityHyperbolicVsEuclideanOpen =
        true
    ; ymUniversalityHyperbolicVsEuclideanOpenIsTrue =
        refl
    ; ckmFormalAtkinLehnerDerivationOpen =
        true
    ; ckmFormalAtkinLehnerDerivationOpenIsTrue =
        refl
    ; computationStateComplete =
        true
    ; computationStateCompleteIsTrue =
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
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        programmeStateAfterComputationStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "C4 records three computation upgrades and three remaining gaps"
        ∷ "NS flow preservation, YM Shimura tower, and CKM CP phase are upgrades, not terminal closures"
        ∷ "NS uniformity, YM hyperbolic-vs-Euclidean universality, and formal CKM Atkin-Lehner derivation remain open"
        ∷ "No terminal, Clay Yang-Mills, or Clay Navier-Stokes promotion is introduced"
        ∷ []
    }

programmeStateAfterComputationComplete :
  computationStateComplete canonicalProgrammeStateAfterComputationReceipt
  ≡
  true
programmeStateAfterComputationComplete =
  refl

programmeStateAfterComputationKeepsClayYMFalse :
  clayYangMillsPromoted canonicalProgrammeStateAfterComputationReceipt
  ≡
  false
programmeStateAfterComputationKeepsClayYMFalse =
  refl

programmeStateAfterComputationKeepsClayNSFalse :
  clayNavierStokesPromoted canonicalProgrammeStateAfterComputationReceipt
  ≡
  false
programmeStateAfterComputationKeepsClayNSFalse =
  refl

programmeStateAfterComputationKeepsTerminalFalse :
  terminalUnificationPromoted canonicalProgrammeStateAfterComputationReceipt
  ≡
  false
programmeStateAfterComputationKeepsTerminalFalse =
  refl

programmeStateAfterComputationNoPromotion :
  ProgrammeStateAfterComputationPromotion →
  ⊥
programmeStateAfterComputationNoPromotion =
  programmeStateAfterComputationPromotionImpossibleHere
