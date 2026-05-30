module DASHI.Physics.Closure.ProgrammeUpgradeSummaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Programme upgrade summary receipt.
--
-- This C3 receipt records the current upgrade summary without converting
-- any conditional, candidate, or paper-draft result into a terminal or Clay
-- promotion.

data ProgrammeUpgradeSummaryStatus : Set where
  programmeUpgradeSummaryRecordedNoPromotion :
    ProgrammeUpgradeSummaryStatus

data ProgrammeUpgrade : Set where
  nsConditionallyReducedToLargeDataContractionProof :
    ProgrammeUpgrade

  ymShimuraTowerRefinementSolved :
    ProgrammeUpgrade

  ckmCPPhaseCandidateWithinPDGOneSigmaUpgrade :
    ProgrammeUpgrade

  papersSixAndEightDraftCompleteUpgrade :
    ProgrammeUpgrade

canonicalProgrammeUpgrades :
  List ProgrammeUpgrade
canonicalProgrammeUpgrades =
  nsConditionallyReducedToLargeDataContractionProof
  ∷ ymShimuraTowerRefinementSolved
  ∷ ckmCPPhaseCandidateWithinPDGOneSigmaUpgrade
  ∷ papersSixAndEightDraftCompleteUpgrade
  ∷ []

data ProgrammeUpgradeRemainingGap : Set where
  nsLargeDataContractionProofStillRequired :
    ProgrammeUpgradeRemainingGap

  ymHyperbolicFlatLimitUniversalityStillRequired :
    ProgrammeUpgradeRemainingGap

  ckmVubStillNeedsVtdAndRub :
    ProgrammeUpgradeRemainingGap

  papersSixAndEightStillNeedReview :
    ProgrammeUpgradeRemainingGap

canonicalProgrammeUpgradeRemainingGaps :
  List ProgrammeUpgradeRemainingGap
canonicalProgrammeUpgradeRemainingGaps =
  nsLargeDataContractionProofStillRequired
  ∷ ymHyperbolicFlatLimitUniversalityStillRequired
  ∷ ckmVubStillNeedsVtdAndRub
  ∷ papersSixAndEightStillNeedReview
  ∷ []

data ProgrammeUpgradeSummaryPromotion : Set where

programmeUpgradeSummaryPromotionImpossibleHere :
  ProgrammeUpgradeSummaryPromotion →
  ⊥
programmeUpgradeSummaryPromotionImpossibleHere ()

programmeUpgradeSummaryStatement : String
programmeUpgradeSummaryStatement =
  "C3 programme upgrade summary: NS is reduced conditionally to one large-data contraction proof; YM Shimura tower solves refinement but hyperbolic/flat-limit universality remains; CKM CP candidate arctan(sqrt7)*(1-alpha1)=1.1596 is within PDG 1 sigma and Vub still needs Vtd/Rub; Papers 6/8 are draft-complete with review points; terminal and Clay promotions remain false."

record ProgrammeUpgradeSummaryReceipt : Setω where
  field
    status :
      ProgrammeUpgradeSummaryStatus

    upgrades :
      List ProgrammeUpgrade

    upgradesAreCanonical :
      upgrades ≡ canonicalProgrammeUpgrades

    remainingGaps :
      List ProgrammeUpgradeRemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalProgrammeUpgradeRemainingGaps

    nsReducedConditionallyToOneLargeDataContractionProof :
      Bool

    nsReducedConditionallyToOneLargeDataContractionProofIsTrue :
      nsReducedConditionallyToOneLargeDataContractionProof ≡ true

    nsLargeDataContractionProofConstructed :
      Bool

    nsLargeDataContractionProofConstructedIsFalse :
      nsLargeDataContractionProofConstructed ≡ false

    ymShimuraTowerSolvesRefinement :
      Bool

    ymShimuraTowerSolvesRefinementIsTrue :
      ymShimuraTowerSolvesRefinement ≡ true

    ymHyperbolicFlatLimitUniversalityConstructed :
      Bool

    ymHyperbolicFlatLimitUniversalityConstructedIsFalse :
      ymHyperbolicFlatLimitUniversalityConstructed ≡ false

    ckmCPPhaseCandidateFormula :
      String

    ckmCPPhaseCandidateFormulaIsCanonical :
      ckmCPPhaseCandidateFormula
      ≡
      "arctan(sqrt7)*(1-alpha1)"

    ckmCPPhaseCandidateRadians :
      String

    ckmCPPhaseCandidateRadiansIsCanonical :
      ckmCPPhaseCandidateRadians ≡ "1.1596"

    ckmCPPhaseCandidateWithinPDGOneSigma :
      Bool

    ckmCPPhaseCandidateWithinPDGOneSigmaIsTrue :
      ckmCPPhaseCandidateWithinPDGOneSigma ≡ true

    vubStillNeedsVtd :
      Bool

    vubStillNeedsVtdIsTrue :
      vubStillNeedsVtd ≡ true

    vubStillNeedsRub :
      Bool

    vubStillNeedsRubIsTrue :
      vubStillNeedsRub ≡ true

    papersSixAndEightDraftComplete :
      Bool

    papersSixAndEightDraftCompleteIsTrue :
      papersSixAndEightDraftComplete ≡ true

    papersSixAndEightReviewPointsRemain :
      Bool

    papersSixAndEightReviewPointsRemainIsTrue :
      papersSixAndEightReviewPointsRemain ≡ true

    programmeUpgradeSummaryComplete :
      Bool

    programmeUpgradeSummaryCompleteIsTrue :
      programmeUpgradeSummaryComplete ≡ true

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

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    paperSubmissionPromoted :
      Bool

    paperSubmissionPromotedIsFalse :
      paperSubmissionPromoted ≡ false

    promotionFlags :
      List ProgrammeUpgradeSummaryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ programmeUpgradeSummaryStatement

    receiptBoundary :
      List String

open ProgrammeUpgradeSummaryReceipt public

canonicalProgrammeUpgradeSummaryReceipt :
  ProgrammeUpgradeSummaryReceipt
canonicalProgrammeUpgradeSummaryReceipt =
  record
    { status =
        programmeUpgradeSummaryRecordedNoPromotion
    ; upgrades =
        canonicalProgrammeUpgrades
    ; upgradesAreCanonical =
        refl
    ; remainingGaps =
        canonicalProgrammeUpgradeRemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; nsReducedConditionallyToOneLargeDataContractionProof =
        true
    ; nsReducedConditionallyToOneLargeDataContractionProofIsTrue =
        refl
    ; nsLargeDataContractionProofConstructed =
        false
    ; nsLargeDataContractionProofConstructedIsFalse =
        refl
    ; ymShimuraTowerSolvesRefinement =
        true
    ; ymShimuraTowerSolvesRefinementIsTrue =
        refl
    ; ymHyperbolicFlatLimitUniversalityConstructed =
        false
    ; ymHyperbolicFlatLimitUniversalityConstructedIsFalse =
        refl
    ; ckmCPPhaseCandidateFormula =
        "arctan(sqrt7)*(1-alpha1)"
    ; ckmCPPhaseCandidateFormulaIsCanonical =
        refl
    ; ckmCPPhaseCandidateRadians =
        "1.1596"
    ; ckmCPPhaseCandidateRadiansIsCanonical =
        refl
    ; ckmCPPhaseCandidateWithinPDGOneSigma =
        true
    ; ckmCPPhaseCandidateWithinPDGOneSigmaIsTrue =
        refl
    ; vubStillNeedsVtd =
        true
    ; vubStillNeedsVtdIsTrue =
        refl
    ; vubStillNeedsRub =
        true
    ; vubStillNeedsRubIsTrue =
        refl
    ; papersSixAndEightDraftComplete =
        true
    ; papersSixAndEightDraftCompleteIsTrue =
        refl
    ; papersSixAndEightReviewPointsRemain =
        true
    ; papersSixAndEightReviewPointsRemainIsTrue =
        refl
    ; programmeUpgradeSummaryComplete =
        true
    ; programmeUpgradeSummaryCompleteIsTrue =
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
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; paperSubmissionPromoted =
        false
    ; paperSubmissionPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        programmeUpgradeSummaryStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "NS is conditionally reduced to one remaining large-data contraction proof"
        ∷ "YM Shimura tower refinement is recorded while hyperbolic/flat-limit universality remains open"
        ∷ "CKM CP phase candidate is within PDG one sigma, but Vub still needs Vtd and Rub"
        ∷ "Papers 6 and 8 are draft-complete with review points, not submission or claim promotions"
        ∷ "Terminal, Clay, and physical CKM promotions are explicitly false"
        ∷ []
    }

programmeUpgradeSummaryCompleteFlag :
  programmeUpgradeSummaryComplete canonicalProgrammeUpgradeSummaryReceipt
  ≡
  true
programmeUpgradeSummaryCompleteFlag =
  refl

programmeUpgradeSummaryKeepsClayYMFalse :
  clayYangMillsPromoted canonicalProgrammeUpgradeSummaryReceipt
  ≡
  false
programmeUpgradeSummaryKeepsClayYMFalse =
  refl

programmeUpgradeSummaryKeepsClayNSFalse :
  clayNavierStokesPromoted canonicalProgrammeUpgradeSummaryReceipt
  ≡
  false
programmeUpgradeSummaryKeepsClayNSFalse =
  refl

programmeUpgradeSummaryKeepsTerminalFalse :
  terminalUnificationPromoted canonicalProgrammeUpgradeSummaryReceipt
  ≡
  false
programmeUpgradeSummaryKeepsTerminalFalse =
  refl

programmeUpgradeSummaryKeepsPhysicalCKMFalse :
  physicalCKMPromoted canonicalProgrammeUpgradeSummaryReceipt
  ≡
  false
programmeUpgradeSummaryKeepsPhysicalCKMFalse =
  refl

programmeUpgradeSummaryNoPromotion :
  ProgrammeUpgradeSummaryPromotion →
  ⊥
programmeUpgradeSummaryNoPromotion =
  programmeUpgradeSummaryPromotionImpossibleHere
