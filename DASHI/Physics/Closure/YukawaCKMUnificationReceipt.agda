module DASHI.Physics.Closure.YukawaCKMUnificationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yukawa/CKM unification receipt.
--
-- This receipt records a structural unification claim: the Wolfenstein
-- lambda carrier is read as the down-type 1-2 Yukawa depth separation.  The
-- same carrier quantity connects the CKM and Yukawa programmes.  The
-- Georgi-Jarlskog coincidence is recorded only as a candidate structural
-- explanation, so CKM, terminal, and Clay promotions remain false.

data ReceiptJudgement : Set where
  structural :
    ReceiptJudgement

  candidate :
    ReceiptJudgement

data YukawaCKMCarrierQuantity : Set where
  alphaD :
    YukawaCKMCarrierQuantity

data YukawaCKMUnificationStatus : Set where
  yukawaCKMUnifiedByDownTwelveDepthSeparationNoPromotion :
    YukawaCKMUnificationStatus

data DownTypeYukawaDepthSlot : Set where
  downOneDepth :
    DownTypeYukawaDepthSlot

  downTwoDepth :
    DownTypeYukawaDepthSlot

canonicalDownTypeTwelveDepthSlots :
  List DownTypeYukawaDepthSlot
canonicalDownTypeTwelveDepthSlots =
  downOneDepth
  ∷ downTwoDepth
  ∷ []

downTypeDepth :
  DownTypeYukawaDepthSlot →
  Nat
downTypeDepth downOneDepth =
  zero
downTypeDepth downTwoDepth =
  suc zero

canonicalDownTypeTwelveDepthSeparation : Nat
canonicalDownTypeTwelveDepthSeparation =
  suc zero

data YukawaCKMUnificationReading : Set where
  wolfensteinLambdaReadsAlphaD :
    YukawaCKMUnificationReading

  alphaDReadsDownTypeTwelveDepthSeparation :
    YukawaCKMUnificationReading

  georgiJarlskogCoincidenceReadsSharedCarrier :
    YukawaCKMUnificationReading

  ckmAndYukawaProgrammesShareCarrierQuantity :
    YukawaCKMUnificationReading

canonicalYukawaCKMUnificationReadings :
  List YukawaCKMUnificationReading
canonicalYukawaCKMUnificationReadings =
  wolfensteinLambdaReadsAlphaD
  ∷ alphaDReadsDownTypeTwelveDepthSeparation
  ∷ georgiJarlskogCoincidenceReadsSharedCarrier
  ∷ ckmAndYukawaProgrammesShareCarrierQuantity
  ∷ []

data YukawaCKMUnificationBlocker : Set where
  missingCertifiedPhysicalCKMDiagonalisation :
    YukawaCKMUnificationBlocker

  missingAcceptedRunningMassConvention :
    YukawaCKMUnificationBlocker

  missingGeorgiJarlskogTheorem :
    YukawaCKMUnificationBlocker

  missingPDGCKMAuthorityBinding :
    YukawaCKMUnificationBlocker

canonicalYukawaCKMUnificationBlockers :
  List YukawaCKMUnificationBlocker
canonicalYukawaCKMUnificationBlockers =
  missingCertifiedPhysicalCKMDiagonalisation
  ∷ missingAcceptedRunningMassConvention
  ∷ missingGeorgiJarlskogTheorem
  ∷ missingPDGCKMAuthorityBinding
  ∷ []

data YukawaCKMUnificationPromotion : Set where

yukawaCKMUnificationPromotionImpossibleHere :
  YukawaCKMUnificationPromotion →
  ⊥
yukawaCKMUnificationPromotionImpossibleHere ()

unificationStatement : String
unificationStatement =
  "Wolfenstein lambda is recorded as alpha_D, the down-type 1-2 Yukawa depth separation; the same alpha_D carrier connects the CKM and Yukawa programmes, while the Georgi-Jarlskog coincidence remains a candidate structural explanation."

record YukawaCKMUnificationReceipt : Set where
  field
    status :
      YukawaCKMUnificationStatus

    sharedCarrierQuantity :
      YukawaCKMCarrierQuantity

    sharedCarrierQuantityIsAlphaD :
      sharedCarrierQuantity ≡ alphaD

    downTypeDepthSlots :
      List DownTypeYukawaDepthSlot

    downTypeDepthSlotsAreCanonical :
      downTypeDepthSlots ≡ canonicalDownTypeTwelveDepthSlots

    downOneSlotDepth :
      Nat

    downOneSlotDepthIsCanonical :
      downOneSlotDepth ≡ downTypeDepth downOneDepth

    downTwoSlotDepth :
      Nat

    downTwoSlotDepthIsCanonical :
      downTwoSlotDepth ≡ downTypeDepth downTwoDepth

    downTypeTwelveYukawaDepthSeparation :
      Nat

    downTypeTwelveYukawaDepthSeparationIsCanonical :
      downTypeTwelveYukawaDepthSeparation
      ≡
      canonicalDownTypeTwelveDepthSeparation

    wolfensteinLambdaIsAlphaD :
      ReceiptJudgement

    wolfensteinLambdaIsAlphaDIsStructural :
      wolfensteinLambdaIsAlphaD ≡ structural

    alphaDIsDownTypeTwelveYukawaDepthSeparation :
      Bool

    alphaDIsDownTypeTwelveYukawaDepthSeparationIsTrue :
      alphaDIsDownTypeTwelveYukawaDepthSeparation ≡ true

    georgiJarlskogExplained :
      ReceiptJudgement

    georgiJarlskogExplainedIsCandidate :
      georgiJarlskogExplained ≡ candidate

    georgiJarlskogCarrierExplanation :
      String

    ckmAndYukawaUnified :
      Bool

    ckmAndYukawaUnifiedIsTrue :
      ckmAndYukawaUnified ≡ true

    ckmAndYukawaConnectedBySameCarrierQuantity :
      Bool

    ckmAndYukawaConnectedBySameCarrierQuantityIsTrue :
      ckmAndYukawaConnectedBySameCarrierQuantity ≡ true

    readings :
      List YukawaCKMUnificationReading

    readingsAreCanonical :
      readings ≡ canonicalYukawaCKMUnificationReadings

    ckmPromoted :
      Bool

    ckmPromotedIsFalse :
      ckmPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    blockers :
      List YukawaCKMUnificationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYukawaCKMUnificationBlockers

    promotionFlags :
      List YukawaCKMUnificationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ unificationStatement

    receiptBoundary :
      List String

open YukawaCKMUnificationReceipt public

canonicalYukawaCKMUnificationReceipt :
  YukawaCKMUnificationReceipt
canonicalYukawaCKMUnificationReceipt =
  record
    { status =
        yukawaCKMUnifiedByDownTwelveDepthSeparationNoPromotion
    ; sharedCarrierQuantity =
        alphaD
    ; sharedCarrierQuantityIsAlphaD =
        refl
    ; downTypeDepthSlots =
        canonicalDownTypeTwelveDepthSlots
    ; downTypeDepthSlotsAreCanonical =
        refl
    ; downOneSlotDepth =
        downTypeDepth downOneDepth
    ; downOneSlotDepthIsCanonical =
        refl
    ; downTwoSlotDepth =
        downTypeDepth downTwoDepth
    ; downTwoSlotDepthIsCanonical =
        refl
    ; downTypeTwelveYukawaDepthSeparation =
        canonicalDownTypeTwelveDepthSeparation
    ; downTypeTwelveYukawaDepthSeparationIsCanonical =
        refl
    ; wolfensteinLambdaIsAlphaD =
        structural
    ; wolfensteinLambdaIsAlphaDIsStructural =
        refl
    ; alphaDIsDownTypeTwelveYukawaDepthSeparation =
        true
    ; alphaDIsDownTypeTwelveYukawaDepthSeparationIsTrue =
        refl
    ; georgiJarlskogExplained =
        candidate
    ; georgiJarlskogExplainedIsCandidate =
        refl
    ; georgiJarlskogCarrierExplanation =
        "The down-type alpha_D carrier also supplies the structural place where the Georgi-Jarlskog factor can live; this is a candidate explanation, not a proved theorem."
    ; ckmAndYukawaUnified =
        true
    ; ckmAndYukawaUnifiedIsTrue =
        refl
    ; ckmAndYukawaConnectedBySameCarrierQuantity =
        true
    ; ckmAndYukawaConnectedBySameCarrierQuantityIsTrue =
        refl
    ; readings =
        canonicalYukawaCKMUnificationReadings
    ; readingsAreCanonical =
        refl
    ; ckmPromoted =
        false
    ; ckmPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; blockers =
        canonicalYukawaCKMUnificationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        unificationStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The receipt unifies CKM lambda and the down-type 1-2 Yukawa depth separation through alpha_D"
        ∷ "The Georgi-Jarlskog coincidence is explained only as a candidate structural carrier reading"
        ∷ "The CKM and Yukawa programmes are connected by the same carrier quantity"
        ∷ "CKM, terminal, and Clay promotion flags remain false"
        ∷ []
    }

canonicalCKMAndYukawaUnified :
  ckmAndYukawaUnified canonicalYukawaCKMUnificationReceipt ≡ true
canonicalCKMAndYukawaUnified =
  refl

canonicalWolfensteinLambdaIsAlphaD :
  wolfensteinLambdaIsAlphaD canonicalYukawaCKMUnificationReceipt
  ≡
  structural
canonicalWolfensteinLambdaIsAlphaD =
  refl

canonicalGeorgiJarlskogExplained :
  georgiJarlskogExplained canonicalYukawaCKMUnificationReceipt
  ≡
  candidate
canonicalGeorgiJarlskogExplained =
  refl

canonicalYukawaCKMNoPromotionBoundary :
  ckmPromoted canonicalYukawaCKMUnificationReceipt ≡ false
canonicalYukawaCKMNoPromotionBoundary =
  refl
