module DASHI.Physics.Closure.CKMGammaDemotionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM gamma demotion receipt.
--
-- The Paper 6 gamma row uses gamma = arctan(sqrt7)*(1-alpha1).  This receipt
-- records the formula as a D=-7 Heegner structural hypothesis only.  Among the
-- class-number-1 Heegner discriminants listed below, this file does not supply
-- a carrier-CM proof that forces the D=-7 choice.

data CKMGammaDemotionStatus : Set where
  ungroundedStructuralHypothesis :
    CKMGammaDemotionStatus

data HeegnerClassNumberOneDiscriminant : Set where
  D=-1 :
    HeegnerClassNumberOneDiscriminant

  D=-2 :
    HeegnerClassNumberOneDiscriminant

  D=-3 :
    HeegnerClassNumberOneDiscriminant

  D=-7 :
    HeegnerClassNumberOneDiscriminant

  D=-11 :
    HeegnerClassNumberOneDiscriminant

  D=-19 :
    HeegnerClassNumberOneDiscriminant

  D=-43 :
    HeegnerClassNumberOneDiscriminant

  D=-67 :
    HeegnerClassNumberOneDiscriminant

  D=-163 :
    HeegnerClassNumberOneDiscriminant

canonicalClassNumberOneHeegnerDiscriminants :
  List HeegnerClassNumberOneDiscriminant
canonicalClassNumberOneHeegnerDiscriminants =
  D=-1
  ∷ D=-2
  ∷ D=-3
  ∷ D=-7
  ∷ D=-11
  ∷ D=-19
  ∷ D=-43
  ∷ D=-67
  ∷ D=-163
  ∷ []

data GammaSelectionBlocker : Set where
  noCarrierCMForcesD=-7Receipt :
    GammaSelectionBlocker

  D=-7SelectedByStructuralHypothesisOnly :
    GammaSelectionBlocker

  competingHeegnerDiscriminantsNotEliminatedByReceipt :
    GammaSelectionBlocker

canonicalGammaSelectionBlockers :
  List GammaSelectionBlocker
canonicalGammaSelectionBlockers =
  noCarrierCMForcesD=-7Receipt
  ∷ D=-7SelectedByStructuralHypothesisOnly
  ∷ competingHeegnerDiscriminantsNotEliminatedByReceipt
  ∷ []

data CarrierCMForcesD=-7Receipt : Set where

carrierCMForcesD=-7ReceiptImpossibleHere :
  CarrierCMForcesD=-7Receipt →
  ⊥
carrierCMForcesD=-7ReceiptImpossibleHere ()

record CorrectionReference : Set where
  field
    correctedModule :
      String

    correctedLine :
      Nat

open CorrectionReference public

ckmFullHonestyGammaReference : CorrectionReference
ckmFullHonestyGammaReference =
  record
    { correctedModule =
        "CKMFullHonestyReceipt"
    ; correctedLine =
        188
    }

paper6DraftGammaReference : CorrectionReference
paper6DraftGammaReference =
  record
    { correctedModule =
        "Paper6DraftCompleteReceipt"
    ; correctedLine =
        220
    }

canonicalGammaDemotionCorrects :
  List CorrectionReference
canonicalGammaDemotionCorrects =
  ckmFullHonestyGammaReference
  ∷ paper6DraftGammaReference
  ∷ []

gammaDemotionFormula : String
gammaDemotionFormula =
  "gamma = arctan(sqrt7)*(1-alpha1)"

gammaDemotionStatement : String
gammaDemotionStatement =
  "The gamma formula uses the D=-7 Heegner discriminant as a structural hypothesis; no typechecked carrier-CM receipt here proves that the carrier structure forces D=-7 among the class-number-1 Heegner discriminants."

record CKMGammaDemotionReceipt : Set where
  field
    gammaStatus :
      CKMGammaDemotionStatus

    gammaStatusIsUngroundedStructuralHypothesis :
      gammaStatus ≡ ungroundedStructuralHypothesis

    formula :
      String

    formulaIsGammaArcTanSqrt7 :
      formula ≡ gammaDemotionFormula

    selectedDiscriminant :
      HeegnerClassNumberOneDiscriminant

    selectedDiscriminantIsD=-7 :
      selectedDiscriminant ≡ D=-7

    classNumberOneHeegnerDiscriminants :
      List HeegnerClassNumberOneDiscriminant

    classNumberOneHeegnerDiscriminantsAreCanonical :
      classNumberOneHeegnerDiscriminants
      ≡
      canonicalClassNumberOneHeegnerDiscriminants

    structuralHypothesisSelection :
      Bool

    structuralHypothesisSelectionIsTrue :
      structuralHypothesisSelection ≡ true

    D=-7SelectionUnproved :
      Bool

    D=-7SelectionUnprovedIsTrue :
      D=-7SelectionUnproved ≡ true

    carrierCMForcesD=-7ReceiptPresent :
      Bool

    carrierCMForcesD=-7ReceiptPresentIsFalse :
      carrierCMForcesD=-7ReceiptPresent ≡ false

    noTypecheckedReceiptDemonstratesCarrierCMForcesD=-7 :
      Bool

    noTypecheckedReceiptDemonstratesCarrierCMForcesD=-7IsTrue :
      noTypecheckedReceiptDemonstratesCarrierCMForcesD=-7 ≡ true

    selectionBlockers :
      List GammaSelectionBlocker

    selectionBlockersAreCanonical :
      selectionBlockers ≡ canonicalGammaSelectionBlockers

    corrects :
      List CorrectionReference

    correctsAreCanonical :
      corrects ≡ canonicalGammaDemotionCorrects

    statement :
      String

    statementIsCanonical :
      statement ≡ gammaDemotionStatement

    receiptBoundary :
      List String

open CKMGammaDemotionReceipt public

canonicalCKMGammaDemotionReceipt :
  CKMGammaDemotionReceipt
canonicalCKMGammaDemotionReceipt =
  record
    { gammaStatus =
        ungroundedStructuralHypothesis
    ; gammaStatusIsUngroundedStructuralHypothesis =
        refl
    ; formula =
        gammaDemotionFormula
    ; formulaIsGammaArcTanSqrt7 =
        refl
    ; selectedDiscriminant =
        D=-7
    ; selectedDiscriminantIsD=-7 =
        refl
    ; classNumberOneHeegnerDiscriminants =
        canonicalClassNumberOneHeegnerDiscriminants
    ; classNumberOneHeegnerDiscriminantsAreCanonical =
        refl
    ; structuralHypothesisSelection =
        true
    ; structuralHypothesisSelectionIsTrue =
        refl
    ; D=-7SelectionUnproved =
        true
    ; D=-7SelectionUnprovedIsTrue =
        refl
    ; carrierCMForcesD=-7ReceiptPresent =
        false
    ; carrierCMForcesD=-7ReceiptPresentIsFalse =
        refl
    ; noTypecheckedReceiptDemonstratesCarrierCMForcesD=-7 =
        true
    ; noTypecheckedReceiptDemonstratesCarrierCMForcesD=-7IsTrue =
        refl
    ; selectionBlockers =
        canonicalGammaSelectionBlockers
    ; selectionBlockersAreCanonical =
        refl
    ; corrects =
        canonicalGammaDemotionCorrects
    ; correctsAreCanonical =
        refl
    ; statement =
        gammaDemotionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Demotes the gamma row from carrier arithmetic to ungrounded structural hypothesis"
        ∷ "The recorded formula is gamma = arctan(sqrt7)*(1-alpha1)"
        ∷ "The formula uses the D=-7 Heegner discriminant"
        ∷ "The class-number-1 Heegner alternatives recorded here are {-1,-2,-3,-7,-11,-19,-43,-67,-163}"
        ∷ "No typechecked receipt in this file demonstrates that carrier CM structure forces D=-7 among those alternatives"
        ∷ "The D=-7 selection is retained only as a structural hypothesis"
        ∷ "Flags: gammaStatus=ungroundedStructuralHypothesis; D=-7SelectionUnproved=true"
        ∷ "Corrects: CKMFullHonestyReceipt:188; Paper6DraftCompleteReceipt:220"
        ∷ []
    }

ckmGammaStatusDemoted :
  gammaStatus canonicalCKMGammaDemotionReceipt
    ≡ ungroundedStructuralHypothesis
ckmGammaStatusDemoted =
  refl

ckmGammaD=-7SelectionUnproved :
  D=-7SelectionUnproved canonicalCKMGammaDemotionReceipt ≡ true
ckmGammaD=-7SelectionUnproved =
  refl

ckmGammaCarrierCMForcesD=-7NotPresent :
  carrierCMForcesD=-7ReceiptPresent canonicalCKMGammaDemotionReceipt ≡ false
ckmGammaCarrierCMForcesD=-7NotPresent =
  refl

ckmGammaNoCarrierCMForcesD=-7Receipt :
  CarrierCMForcesD=-7Receipt →
  ⊥
ckmGammaNoCarrierCMForcesD=-7Receipt =
  carrierCMForcesD=-7ReceiptImpossibleHere
