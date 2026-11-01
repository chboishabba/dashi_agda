module DASHI.Physics.Closure.ProgrammeFinalStateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Final programme-state receipt after phase2-ns-ym-ckm-v2.
--
-- This is a self-contained ledger receipt.  It records the final state of
-- the NS, YM, and CKM lanes after phase2-ns-ym-ckm-v2 without importing
-- other receipts or promoting any Clay theorem.

data Empty : Set where

data Phase : Set where
  phase2-ns-ym-ckm-v2 :
    Phase

data CompletionState : Set where
  complete :
    CompletionState

  draftComplete :
    CompletionState

  openState :
    CompletionState

data PromotionState : Set where
  notPromoted :
    PromotionState

data ClayDistance : Set where
  minimal :
    ClayDistance

data NSFinalFact : Set where
  nsGlobalH118BoundComplete :
    NSFinalFact

  nsExplicitConstantsForCarrierStructuredData :
    NSFinalFact

  nsCarrierToGeneralGapOpen :
    NSFinalFact

  nsSingleRemainingStructuralQuestion :
    NSFinalFact

canonicalNSFinalFacts : List NSFinalFact
canonicalNSFinalFacts =
  nsGlobalH118BoundComplete
  ∷ nsExplicitConstantsForCarrierStructuredData
  ∷ nsCarrierToGeneralGapOpen
  ∷ nsSingleRemainingStructuralQuestion
  ∷ []

data YMFinalFact : Set where
  ymCuspUniversalityReducesCarrierClayToFlatClay :
    YMFinalFact

  ymNoNewGapIntroduced :
    YMFinalFact

  ymMinimalClayDistance :
    YMFinalFact

canonicalYMFinalFacts : List YMFinalFact
canonicalYMFinalFacts =
  ymCuspUniversalityReducesCarrierClayToFlatClay
  ∷ ymNoNewGapIntroduced
  ∷ ymMinimalClayDistance
  ∷ []

data CKMQuantity : Set where
  ckmVusOrLambda :
    CKMQuantity

  ckmVcb :
    CKMQuantity

  ckmVub :
    CKMQuantity

  ckmBeta :
    CKMQuantity

  ckmGamma :
    CKMQuantity

  ckmJarlskogOrCPScale :
    CKMQuantity

canonicalCKMQuantities : List CKMQuantity
canonicalCKMQuantities =
  ckmVusOrLambda
  ∷ ckmVcb
  ∷ ckmVub
  ∷ ckmBeta
  ∷ ckmGamma
  ∷ ckmJarlskogOrCPScale
  ∷ []

data CKMFinalFact : Set where
  ckmSixQuantitiesAtLeadingCarrierOrder :
    CKMFinalFact

  ckmAccuracyBandZeroToSixPercent :
    CKMFinalFact

  ckmPaper6DraftComplete :
    CKMFinalFact

canonicalCKMFinalFacts : List CKMFinalFact
canonicalCKMFinalFacts =
  ckmSixQuantitiesAtLeadingCarrierOrder
  ∷ ckmAccuracyBandZeroToSixPercent
  ∷ ckmPaper6DraftComplete
  ∷ []

data FinalProgrammeFact : Set where
  nsLaneFinalStateRecorded :
    FinalProgrammeFact

  ymLaneFinalStateRecorded :
    FinalProgrammeFact

  ckmLaneFinalStateRecorded :
    FinalProgrammeFact

  noClayPromotionOnNSSide :
    FinalProgrammeFact

  noClayPromotionOnYMSide :
    FinalProgrammeFact

canonicalFinalProgrammeFacts : List FinalProgrammeFact
canonicalFinalProgrammeFacts =
  nsLaneFinalStateRecorded
  ∷ ymLaneFinalStateRecorded
  ∷ ckmLaneFinalStateRecorded
  ∷ noClayPromotionOnNSSide
  ∷ noClayPromotionOnYMSide
  ∷ []

data NSClayPromotion : Set where

data YMClayPromotion : Set where

nsClayPromotionImpossibleHere :
  NSClayPromotion →
  Empty
nsClayPromotionImpossibleHere ()

ymClayPromotionImpossibleHere :
  YMClayPromotion →
  Empty
ymClayPromotionImpossibleHere ()

programmePhaseLabel : String
programmePhaseLabel =
  "phase2-ns-ym-ckm-v2"

nsFinalStateStatement : String
nsFinalStateStatement =
  "NS final state: global H^11/8 bound complete with explicit constants for carrier-structured data; carrier-to-general gap remains open as the single remaining NS structural question."

ymFinalStateStatement : String
ymFinalStateStatement =
  "YM final state: cusp universality reduces carrier YM Clay to flat YM Clay; no new gap is introduced; Clay distance is minimal."

ckmFinalStateStatement : String
ckmFinalStateStatement =
  "CKM final state: six quantities are recorded at leading carrier order with 0%-6% accuracy; Paper 6 is draft-complete."

programmeFinalStateStatement : String
programmeFinalStateStatement =
  "Definitive programme state after phase2-ns-ym-ckm-v2: NS global H^11/8 bound complete with explicit constants for carrier-structured data, carrier-to-general gap open as the single remaining NS structural question; YM cusp universality reduces carrier YM Clay to flat YM Clay, no new gap introduced, minimal Clay distance; CKM six quantities at leading carrier order, 0%-6% accuracy, Paper 6 draft-complete; no Clay promotion on either side."

record ProgrammeFinalStateReceipt : Set where
  field
    phase :
      Phase

    phaseIsCanonical :
      phase ≡ phase2-ns-ym-ckm-v2

    phaseLabel :
      String

    phaseLabelIsCanonical :
      phaseLabel ≡ programmePhaseLabel

    nsGlobalH118Bound :
      CompletionState

    nsGlobalH118BoundIsComplete :
      nsGlobalH118Bound ≡ complete

    nsExplicitConstantsForCarrierData :
      Bool

    nsExplicitConstantsForCarrierDataIsTrue :
      nsExplicitConstantsForCarrierData ≡ true

    nsCarrierStructuredDataScope :
      Bool

    nsCarrierStructuredDataScopeIsTrue :
      nsCarrierStructuredDataScope ≡ true

    nsCarrierToGeneralGap :
      CompletionState

    nsCarrierToGeneralGapIsOpen :
      nsCarrierToGeneralGap ≡ openState

    nsRemainingStructuralQuestionCount :
      Nat

    nsRemainingStructuralQuestionCountIsOne :
      nsRemainingStructuralQuestionCount ≡ 1

    nsFacts :
      List NSFinalFact

    nsFactsAreCanonical :
      nsFacts ≡ canonicalNSFinalFacts

    nsStatement :
      String

    nsStatementIsCanonical :
      nsStatement ≡ nsFinalStateStatement

    ymCuspUniversalityReduction :
      Bool

    ymCuspUniversalityReductionIsTrue :
      ymCuspUniversalityReduction ≡ true

    ymCarrierClayTarget :
      String

    ymCarrierClayTargetIsCanonical :
      ymCarrierClayTarget ≡ "carrier YM Clay"

    ymReducedClayTarget :
      String

    ymReducedClayTargetIsFlatYMClay :
      ymReducedClayTarget ≡ "flat YM Clay"

    ymNewGapIntroduced :
      Bool

    ymNewGapIntroducedIsFalse :
      ymNewGapIntroduced ≡ false

    ymClayDistance :
      ClayDistance

    ymClayDistanceIsMinimal :
      ymClayDistance ≡ minimal

    ymFacts :
      List YMFinalFact

    ymFactsAreCanonical :
      ymFacts ≡ canonicalYMFinalFacts

    ymStatement :
      String

    ymStatementIsCanonical :
      ymStatement ≡ ymFinalStateStatement

    ckmLeadingCarrierOrder :
      Bool

    ckmLeadingCarrierOrderIsTrue :
      ckmLeadingCarrierOrder ≡ true

    ckmQuantityCount :
      Nat

    ckmQuantityCountIsSix :
      ckmQuantityCount ≡ 6

    ckmQuantities :
      List CKMQuantity

    ckmQuantitiesAreCanonical :
      ckmQuantities ≡ canonicalCKMQuantities

    ckmAccuracyLowerPercent :
      Nat

    ckmAccuracyLowerPercentIsZero :
      ckmAccuracyLowerPercent ≡ 0

    ckmAccuracyUpperPercent :
      Nat

    ckmAccuracyUpperPercentIsSix :
      ckmAccuracyUpperPercent ≡ 6

    ckmAccuracyBandLabel :
      String

    ckmAccuracyBandLabelIsCanonical :
      ckmAccuracyBandLabel ≡ "0%-6%"

    paper6State :
      CompletionState

    paper6StateIsDraftComplete :
      paper6State ≡ draftComplete

    ckmFacts :
      List CKMFinalFact

    ckmFactsAreCanonical :
      ckmFacts ≡ canonicalCKMFinalFacts

    ckmStatement :
      String

    ckmStatementIsCanonical :
      ckmStatement ≡ ckmFinalStateStatement

    nsClayPromotion :
      PromotionState

    nsClayPromotionIsFalse :
      nsClayPromotion ≡ notPromoted

    ymClayPromotion :
      PromotionState

    ymClayPromotionIsFalse :
      ymClayPromotion ≡ notPromoted

    terminalClayPromotionEitherSide :
      PromotionState

    terminalClayPromotionEitherSideIsFalse :
      terminalClayPromotionEitherSide ≡ notPromoted

    facts :
      List FinalProgrammeFact

    factsAreCanonical :
      facts ≡ canonicalFinalProgrammeFacts

    statement :
      String

    statementIsCanonical :
      statement ≡ programmeFinalStateStatement

    nsPromotionFlags :
      List NSClayPromotion

    nsPromotionFlagsAreEmpty :
      nsPromotionFlags ≡ []

    ymPromotionFlags :
      List YMClayPromotion

    ymPromotionFlagsAreEmpty :
      ymPromotionFlags ≡ []

    receiptBoundary :
      List String

open ProgrammeFinalStateReceipt public

canonicalProgrammeFinalStateReceipt :
  ProgrammeFinalStateReceipt
canonicalProgrammeFinalStateReceipt =
  record
    { phase =
        phase2-ns-ym-ckm-v2
    ; phaseIsCanonical =
        refl
    ; phaseLabel =
        programmePhaseLabel
    ; phaseLabelIsCanonical =
        refl
    ; nsGlobalH118Bound =
        complete
    ; nsGlobalH118BoundIsComplete =
        refl
    ; nsExplicitConstantsForCarrierData =
        true
    ; nsExplicitConstantsForCarrierDataIsTrue =
        refl
    ; nsCarrierStructuredDataScope =
        true
    ; nsCarrierStructuredDataScopeIsTrue =
        refl
    ; nsCarrierToGeneralGap =
        openState
    ; nsCarrierToGeneralGapIsOpen =
        refl
    ; nsRemainingStructuralQuestionCount =
        1
    ; nsRemainingStructuralQuestionCountIsOne =
        refl
    ; nsFacts =
        canonicalNSFinalFacts
    ; nsFactsAreCanonical =
        refl
    ; nsStatement =
        nsFinalStateStatement
    ; nsStatementIsCanonical =
        refl
    ; ymCuspUniversalityReduction =
        true
    ; ymCuspUniversalityReductionIsTrue =
        refl
    ; ymCarrierClayTarget =
        "carrier YM Clay"
    ; ymCarrierClayTargetIsCanonical =
        refl
    ; ymReducedClayTarget =
        "flat YM Clay"
    ; ymReducedClayTargetIsFlatYMClay =
        refl
    ; ymNewGapIntroduced =
        false
    ; ymNewGapIntroducedIsFalse =
        refl
    ; ymClayDistance =
        minimal
    ; ymClayDistanceIsMinimal =
        refl
    ; ymFacts =
        canonicalYMFinalFacts
    ; ymFactsAreCanonical =
        refl
    ; ymStatement =
        ymFinalStateStatement
    ; ymStatementIsCanonical =
        refl
    ; ckmLeadingCarrierOrder =
        true
    ; ckmLeadingCarrierOrderIsTrue =
        refl
    ; ckmQuantityCount =
        6
    ; ckmQuantityCountIsSix =
        refl
    ; ckmQuantities =
        canonicalCKMQuantities
    ; ckmQuantitiesAreCanonical =
        refl
    ; ckmAccuracyLowerPercent =
        0
    ; ckmAccuracyLowerPercentIsZero =
        refl
    ; ckmAccuracyUpperPercent =
        6
    ; ckmAccuracyUpperPercentIsSix =
        refl
    ; ckmAccuracyBandLabel =
        "0%-6%"
    ; ckmAccuracyBandLabelIsCanonical =
        refl
    ; paper6State =
        draftComplete
    ; paper6StateIsDraftComplete =
        refl
    ; ckmFacts =
        canonicalCKMFinalFacts
    ; ckmFactsAreCanonical =
        refl
    ; ckmStatement =
        ckmFinalStateStatement
    ; ckmStatementIsCanonical =
        refl
    ; nsClayPromotion =
        notPromoted
    ; nsClayPromotionIsFalse =
        refl
    ; ymClayPromotion =
        notPromoted
    ; ymClayPromotionIsFalse =
        refl
    ; terminalClayPromotionEitherSide =
        notPromoted
    ; terminalClayPromotionEitherSideIsFalse =
        refl
    ; facts =
        canonicalFinalProgrammeFacts
    ; factsAreCanonical =
        refl
    ; statement =
        programmeFinalStateStatement
    ; statementIsCanonical =
        refl
    ; nsPromotionFlags =
        []
    ; nsPromotionFlagsAreEmpty =
        refl
    ; ymPromotionFlags =
        []
    ; ymPromotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Phase: phase2-ns-ym-ckm-v2"
        ∷ "NS: global H^11/8 bound complete with explicit constants for carrier-structured data"
        ∷ "NS: carrier-to-general gap remains open as the single remaining structural question"
        ∷ "YM: cusp universality reduces carrier YM Clay to flat YM Clay"
        ∷ "YM: no new gap is introduced and Clay distance is minimal"
        ∷ "CKM: six quantities at leading carrier order with 0%-6% accuracy"
        ∷ "CKM: Paper 6 draft-complete"
        ∷ "No Clay promotion on either side"
        ∷ []
    }

programmeFinalStatePhaseRecorded :
  phase canonicalProgrammeFinalStateReceipt
  ≡
  phase2-ns-ym-ckm-v2
programmeFinalStatePhaseRecorded =
  refl

programmeFinalStateNSBoundComplete :
  nsGlobalH118Bound canonicalProgrammeFinalStateReceipt
  ≡
  complete
programmeFinalStateNSBoundComplete =
  refl

programmeFinalStateNSOnlyCarrierGapOpen :
  nsRemainingStructuralQuestionCount canonicalProgrammeFinalStateReceipt
  ≡
  1
programmeFinalStateNSOnlyCarrierGapOpen =
  refl

programmeFinalStateYMReducesToFlatClay :
  ymReducedClayTarget canonicalProgrammeFinalStateReceipt
  ≡
  "flat YM Clay"
programmeFinalStateYMReducesToFlatClay =
  refl

programmeFinalStateYMIntroducesNoNewGap :
  ymNewGapIntroduced canonicalProgrammeFinalStateReceipt
  ≡
  false
programmeFinalStateYMIntroducesNoNewGap =
  refl

programmeFinalStateCKMSixQuantities :
  ckmQuantityCount canonicalProgrammeFinalStateReceipt
  ≡
  6
programmeFinalStateCKMSixQuantities =
  refl

programmeFinalStateCKMAccuracyUpperBound :
  ckmAccuracyUpperPercent canonicalProgrammeFinalStateReceipt
  ≡
  6
programmeFinalStateCKMAccuracyUpperBound =
  refl

programmeFinalStateNoNSClayPromotion :
  nsClayPromotion canonicalProgrammeFinalStateReceipt
  ≡
  notPromoted
programmeFinalStateNoNSClayPromotion =
  refl

programmeFinalStateNoYMClayPromotion :
  ymClayPromotion canonicalProgrammeFinalStateReceipt
  ≡
  notPromoted
programmeFinalStateNoYMClayPromotion =
  refl
