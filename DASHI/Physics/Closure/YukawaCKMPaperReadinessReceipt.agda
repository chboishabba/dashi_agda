module DASHI.Physics.Closure.YukawaCKMPaperReadinessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C5: Paper 6 CKM/Yukawa readiness receipt.

data Paper6CKMResult : Set where
  alphaOneAlphaTwoUpTypeDepths :
    Paper6CKMResult

  alphaDEqualsLambdaGeorgiJarlskog :
    Paper6CKMResult

  vubAlphaOneAlphaTwo :
    Paper6CKMResult

  gammaFromDMinusSevenHeegnerPoint :
    Paper6CKMResult

  betaDerivedFromCarrierApex :
    Paper6CKMResult

canonicalPaper6CKMResults : List Paper6CKMResult
canonicalPaper6CKMResults =
  alphaOneAlphaTwoUpTypeDepths
  ∷ alphaDEqualsLambdaGeorgiJarlskog
  ∷ vubAlphaOneAlphaTwo
  ∷ gammaFromDMinusSevenHeegnerPoint
  ∷ betaDerivedFromCarrierApex
  ∷ []

data Paper6NewResult : Set where
  paper6NewVub :
    Paper6NewResult

  paper6NewBeta :
    Paper6NewResult

canonicalPaper6NewResults : List Paper6NewResult
canonicalPaper6NewResults =
  paper6NewVub
  ∷ paper6NewBeta
  ∷ []

paper6CKMReadinessStatement : String
paper6CKMReadinessStatement =
  "Paper 6 CKM/Yukawa package is ready for draft completion: alpha1 and alpha2 are up-type depth separations; alpha_d=lambda records Georgi-Jarlskog; |Vub|=alpha1 alpha2; gamma comes from arctan(sqrt 7)(1-alpha1); beta is derived from the carrier apex. All are candidate-level claims with stated errors."

data YukawaCKMPaperReadinessPromotion : Set where

yukawaCKMPaperReadinessPromotionImpossibleHere :
  YukawaCKMPaperReadinessPromotion →
  ⊥
yukawaCKMPaperReadinessPromotionImpossibleHere ()

record YukawaCKMPaperReadinessReceipt : Setω where
  field
    paper6CKMDraftReady :
      Bool

    paper6CKMDraftReadyIsTrue :
      paper6CKMDraftReady ≡ true

    results :
      List Paper6CKMResult

    resultsAreCanonical :
      results ≡ canonicalPaper6CKMResults

    resultCount :
      Nat

    resultCountIsFive :
      resultCount ≡ 5

    paper6NewResults :
      List Paper6NewResult

    paper6NewResultsAreCanonical :
      paper6NewResults ≡ canonicalPaper6NewResults

    paper6NewResultCount :
      Nat

    paper6NewResultCountIsTwo :
      paper6NewResultCount ≡ 2

    allResultsCandidateLabelled :
      Bool

    allResultsCandidateLabelledIsTrue :
      allResultsCandidateLabelled ≡ true

    vubFormulaForPaper :
      String

    vubFormulaForPaperIsAlphaOneAlphaTwo :
      vubFormulaForPaper ≡ "|Vub| = alpha1 alpha2"

    gammaFormulaForPaper :
      String

    gammaFormulaForPaperIsCanonical :
      gammaFormulaForPaper ≡ "gamma = arctan(sqrt 7)*(1-alpha1)"

    betaDerivationForPaper :
      String

    betaDerivationForPaperIsCarrierApex :
      betaDerivationForPaper ≡ "beta from rho, eta carrier apex"

    statement :
      String

    statementIsCanonical :
      statement ≡ paper6CKMReadinessStatement

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    promotionFlags :
      List YukawaCKMPaperReadinessPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YukawaCKMPaperReadinessReceipt public

canonicalYukawaCKMPaperReadinessReceipt :
  YukawaCKMPaperReadinessReceipt
canonicalYukawaCKMPaperReadinessReceipt =
  record
    { paper6CKMDraftReady =
        true
    ; paper6CKMDraftReadyIsTrue =
        refl
    ; results =
        canonicalPaper6CKMResults
    ; resultsAreCanonical =
        refl
    ; resultCount =
        5
    ; resultCountIsFive =
        refl
    ; paper6NewResults =
        canonicalPaper6NewResults
    ; paper6NewResultsAreCanonical =
        refl
    ; paper6NewResultCount =
        2
    ; paper6NewResultCountIsTwo =
        refl
    ; allResultsCandidateLabelled =
        true
    ; allResultsCandidateLabelledIsTrue =
        refl
    ; vubFormulaForPaper =
        "|Vub| = alpha1 alpha2"
    ; vubFormulaForPaperIsAlphaOneAlphaTwo =
        refl
    ; gammaFormulaForPaper =
        "gamma = arctan(sqrt 7)*(1-alpha1)"
    ; gammaFormulaForPaperIsCanonical =
        refl
    ; betaDerivationForPaper =
        "beta from rho, eta carrier apex"
    ; betaDerivationForPaperIsCarrierApex =
        refl
    ; statement =
        paper6CKMReadinessStatement
    ; statementIsCanonical =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Manager C5 records Paper 6 CKM/Yukawa readiness"
        ∷ "Vub and beta are new candidate results for the draft"
        ∷ "No physical CKM promotion is made"
        ∷ []
    }

canonicalYukawaCKMPaperReadinessKeepsCKMFalse :
  physicalCKMPromoted canonicalYukawaCKMPaperReadinessReceipt ≡ false
canonicalYukawaCKMPaperReadinessKeepsCKMFalse =
  refl

canonicalYukawaCKMPaperReadinessNoPromotion :
  YukawaCKMPaperReadinessPromotion →
  ⊥
canonicalYukawaCKMPaperReadinessNoPromotion =
  yukawaCKMPaperReadinessPromotionImpossibleHere
