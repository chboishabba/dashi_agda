module DASHI.Physics.Closure.VEVAsPDGInputReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierVEVReceipt as CarrierVEV
import DASHI.Physics.Closure.PhysicalMassMatrixReceipt as Mass

data VEVAsPDGInputStatus : Set where
  pdgVEVRecordedAsExternalInput :
    VEVAsPDGInputStatus

data VEVAsPDGInputBlocker : Set where
  vevIsPDGExternalInput :
    VEVAsPDGInputBlocker

  missingCarrierDerivedHiggsVEV :
    VEVAsPDGInputBlocker

  missingW4HiggsNumericalCalibration :
    VEVAsPDGInputBlocker

  missingPhysicalMassMatrixPromotion :
    VEVAsPDGInputBlocker

canonicalVEVAsPDGInputBlockers :
  List VEVAsPDGInputBlocker
canonicalVEVAsPDGInputBlockers =
  vevIsPDGExternalInput
  ∷ missingCarrierDerivedHiggsVEV
  ∷ missingW4HiggsNumericalCalibration
  ∷ missingPhysicalMassMatrixPromotion
  ∷ []

data VEVAsPDGInputPromotion : Set where

vevAsPDGInputPromotionImpossibleHere :
  VEVAsPDGInputPromotion →
  ⊥
vevAsPDGInputPromotionImpossibleHere ()

vevAsPDGInputBoundaryStatement : String
vevAsPDGInputBoundaryStatement =
  "The electroweak VEV is recorded as a PDG numerical input, not as a carrier-derived Higgs-sector theorem."

record VEVAsPDGInputReceipt : Setω where
  field
    status :
      VEVAsPDGInputStatus

    carrierVEVReceipt :
      CarrierVEV.CarrierVEVReceipt

    carrierVEVCandidateRecorded :
      CarrierVEV.vevFromW4Sector carrierVEVReceipt ≡ true

    carrierHiggsExpectationValueStillOpen :
      CarrierVEV.higgsExpectationValueIdentified carrierVEVReceipt ≡ false

    carrierVEVNumericalValueStillOpen :
      CarrierVEV.vevNumericalValueConstructed carrierVEVReceipt ≡ false

    physicalMassMatrixReceipt :
      Mass.PhysicalMassMatrixReceipt

    physicalMassStillDiagnostic :
      Mass.physicalMassMatchesPDG physicalMassMatrixReceipt ≡ false

    physicalCKMStillUnpromoted :
      Mass.physicalCKMPromoted physicalMassMatrixReceipt ≡ false

    pdgVEVInputGeV :
      Float

    pdgVEVInputRecorded :
      Bool

    pdgVEVInputRecordedIsTrue :
      pdgVEVInputRecorded ≡ true

    higgsVEVDerivedFromCarrier :
      Bool

    higgsVEVDerivedFromCarrierIsFalse :
      higgsVEVDerivedFromCarrier ≡ false

    higgsVEVDerivedFromW4 :
      Bool

    higgsVEVDerivedFromW4IsFalse :
      higgsVEVDerivedFromW4 ≡ false

    physicalMassMatrixPromoted :
      Bool

    physicalMassMatrixPromotedIsFalse :
      physicalMassMatrixPromoted ≡ false

    higgsVEVDerivationPromoted :
      Bool

    higgsVEVDerivationPromotedIsFalse :
      higgsVEVDerivationPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ vevAsPDGInputBoundaryStatement

    blockers :
      List VEVAsPDGInputBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVEVAsPDGInputBlockers

    promotionFlags :
      List VEVAsPDGInputPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VEVAsPDGInputReceipt public

canonicalVEVAsPDGInputReceipt :
  VEVAsPDGInputReceipt
canonicalVEVAsPDGInputReceipt =
  record
    { status =
        pdgVEVRecordedAsExternalInput
    ; carrierVEVReceipt =
        CarrierVEV.canonicalCarrierVEVReceipt
    ; carrierVEVCandidateRecorded =
        refl
    ; carrierHiggsExpectationValueStillOpen =
        refl
    ; carrierVEVNumericalValueStillOpen =
        refl
    ; physicalMassMatrixReceipt =
        Mass.canonicalPhysicalMassMatrixReceipt
    ; physicalMassStillDiagnostic =
        refl
    ; physicalCKMStillUnpromoted =
        refl
    ; pdgVEVInputGeV =
        246.22
    ; pdgVEVInputRecorded =
        true
    ; pdgVEVInputRecordedIsTrue =
        refl
    ; higgsVEVDerivedFromCarrier =
        false
    ; higgsVEVDerivedFromCarrierIsFalse =
        refl
    ; higgsVEVDerivedFromW4 =
        false
    ; higgsVEVDerivedFromW4IsFalse =
        refl
    ; physicalMassMatrixPromoted =
        false
    ; physicalMassMatrixPromotedIsFalse =
        refl
    ; higgsVEVDerivationPromoted =
        false
    ; higgsVEVDerivationPromotedIsFalse =
        refl
    ; boundaryStatement =
        vevAsPDGInputBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; blockers =
        canonicalVEVAsPDGInputBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The W4/Higgs sector remains only a carrier VEV candidate"
        ∷ "The numerical VEV is imported as the PDG value 246.22 GeV"
        ∷ "No Higgs VEV derivation, physical mass promotion, or physical CKM promotion is made"
        ∷ []
    }

higgsVEVNotCarrierDerived :
  higgsVEVDerivedFromCarrier canonicalVEVAsPDGInputReceipt ≡ false
higgsVEVNotCarrierDerived =
  refl

pdgVEVInputOnly :
  pdgVEVInputRecorded canonicalVEVAsPDGInputReceipt ≡ true
pdgVEVInputOnly =
  refl
