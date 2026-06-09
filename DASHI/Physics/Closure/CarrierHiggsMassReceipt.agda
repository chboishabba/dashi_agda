module DASHI.Physics.Closure.CarrierHiggsMassReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierVEVReceipt as VEV

------------------------------------------------------------------------
-- Higgs-mass golden-ratio diagnostic.

data CarrierHiggsMassBlocker : Set where
  vevStillPDGInput :
    CarrierHiggsMassBlocker

  su2LevelFourIdentificationStillCandidate :
    CarrierHiggsMassBlocker

  noCarrierHiggsMassDerivation :
    CarrierHiggsMassBlocker

canonicalCarrierHiggsMassBlockers :
  List CarrierHiggsMassBlocker
canonicalCarrierHiggsMassBlockers =
  vevStillPDGInput
  ∷ su2LevelFourIdentificationStillCandidate
  ∷ noCarrierHiggsMassDerivation
  ∷ []

data CarrierHiggsMassPromotion : Set where

carrierHiggsMassPromotionImpossibleHere :
  CarrierHiggsMassPromotion →
  ⊥
carrierHiggsMassPromotionImpossibleHere ()

record CarrierHiggsMassReceipt : Setω where
  field
    carrierVEVReceipt :
      String

    vevStillOpenInCarrier :
      Bool

    vevStillOpenInCarrierIsTrue :
      vevStillOpenInCarrier ≡ true

    csLevel :
      Nat

    csLevelIsFour :
      csLevel ≡ 4

    pdgVEVGeV :
      Float

    preliminaryFormula :
      String

    higgsMassPreliminaryGeV :
      Float

    phi :
      Float

    higgsMassPhiCorrectedGeV :
      Float

    pdgHiggsMassGeV :
      Float

    higgsMassPhiCorrectedRelativeError :
      Float

    higgsMassDiagnostic :
      Bool

    higgsMassDiagnosticIsTrue :
      higgsMassDiagnostic ≡ true

    higgsMassPhiCorrectionHypothesis :
      Bool

    higgsMassPhiCorrectionHypothesisIsTrue :
      higgsMassPhiCorrectionHypothesis ≡ true

    higgsMassDerivedFromCarrier :
      Bool

    higgsMassDerivedFromCarrierIsFalse :
      higgsMassDerivedFromCarrier ≡ false

    physicalHiggsPromoted :
      Bool

    physicalHiggsPromotedIsFalse :
      physicalHiggsPromoted ≡ false

    blockers :
      List CarrierHiggsMassBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierHiggsMassBlockers

    promotionFlags :
      List CarrierHiggsMassPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CarrierHiggsMassReceipt public

canonicalCarrierHiggsMassReceipt :
  CarrierHiggsMassReceipt
canonicalCarrierHiggsMassReceipt =
  record
    { carrierVEVReceipt =
        "DASHI.Physics.Closure.CarrierVEVReceipt.canonicalCarrierVEVReceipt"
    ; vevStillOpenInCarrier =
        true
    ; vevStillOpenInCarrierIsTrue =
        refl
    ; csLevel =
        4
    ; csLevelIsFour =
        refl
    ; pdgVEVGeV =
        246.22
    ; preliminaryFormula =
        "M_H(prelim) = k * v / (4*pi), k = 4"
    ; higgsMassPreliminaryGeV =
        78.37426017617294
    ; phi =
        1.618033988749895
    ; higgsMassPhiCorrectedGeV =
        126.81221680817514
    ; pdgHiggsMassGeV =
        125.25
    ; higgsMassPhiCorrectedRelativeError =
        0.012472788887625843
    ; higgsMassDiagnostic =
        true
    ; higgsMassDiagnosticIsTrue =
        refl
    ; higgsMassPhiCorrectionHypothesis =
        true
    ; higgsMassPhiCorrectionHypothesisIsTrue =
        refl
    ; higgsMassDerivedFromCarrier =
        false
    ; higgsMassDerivedFromCarrierIsFalse =
        refl
    ; physicalHiggsPromoted =
        false
    ; physicalHiggsPromotedIsFalse =
        refl
    ; blockers =
        canonicalCarrierHiggsMassBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The k=4 CS-style Higgs mass estimate is diagnostic and uses the PDG VEV input"
        ∷ "The phi-corrected value is about 1.25 percent high against the PDG Higgs mass"
        ∷ "No carrier derivation of the Higgs mass or VEV is asserted"
        ∷ []
    }

carrierHiggsMassDoesNotPromotePhysicalHiggs :
  physicalHiggsPromoted canonicalCarrierHiggsMassReceipt ≡ false
carrierHiggsMassDoesNotPromotePhysicalHiggs =
  refl
