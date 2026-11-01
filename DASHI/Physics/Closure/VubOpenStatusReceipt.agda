module DASHI.Physics.Closure.VubOpenStatusReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- |V_ub| open-status receipt.
--
-- The carrier currently contributes lambda, |Vcb|, and the
-- delta_CP candidate arctan(sqrt 7)*(1-alpha1).  The unitarity-triangle
-- route still requires beta from carrier arithmetic rather than PDG input;
-- without that carrier beta angle, the triangle is underdetermined.

data VubOpenStatus : Set where
  vubOpen :
    VubOpenStatus

data CarrierCKMDerivedParameter : Set where
  lambda :
    CarrierCKMDerivedParameter

  vcbMagnitude :
    CarrierCKMDerivedParameter

  deltaCP-candidate :
    CarrierCKMDerivedParameter

canonicalCarrierCKMDerivedParameters :
  List CarrierCKMDerivedParameter
canonicalCarrierCKMDerivedParameters =
  lambda
  ∷ vcbMagnitude
  ∷ deltaCP-candidate
  ∷ []

data VubOpenBlocker : Set where
  betaAngleNotDerivedFromCarrierArithmetic :
    VubOpenBlocker

  pdgBetaNotAdmissibleForCarrierPromotion :
    VubOpenBlocker

  unitarityTriangleUnderdeterminedWithoutCarrierBeta :
    VubOpenBlocker

canonicalVubOpenBlockers :
  List VubOpenBlocker
canonicalVubOpenBlockers =
  betaAngleNotDerivedFromCarrierArithmetic
  ∷ pdgBetaNotAdmissibleForCarrierPromotion
  ∷ unitarityTriangleUnderdeterminedWithoutCarrierBeta
  ∷ []

data VubOpenPromotion : Set where

vubOpenPromotionImpossibleHere :
  VubOpenPromotion →
  ⊥
vubOpenPromotionImpossibleHere ()

record VubOpenStatusReceipt : Set where
  field
    vubStatus :
      VubOpenStatus

    vubStatusIsOpen :
      vubStatus ≡ vubOpen

    vubStatusLabel :
      String

    vubStatusLabelIsOpen :
      vubStatusLabel ≡ "open"

    requiresBetaFromCarrier :
      Bool

    requiresBetaFromCarrierIsTrue :
      requiresBetaFromCarrier ≡ true

    betaSourceRequired :
      String

    betaSourceRequiredIsCarrierArithmetic :
      betaSourceRequired ≡ "carrier arithmetic"

    betaSourcePDGAdmitted :
      Bool

    betaSourcePDGAdmittedIsFalse :
      betaSourcePDGAdmitted ≡ false

    currentCarrierCKMDerivedParameters :
      List CarrierCKMDerivedParameter

    currentCarrierCKMDerivedParametersAreCanonical :
      currentCarrierCKMDerivedParameters
      ≡
      canonicalCarrierCKMDerivedParameters

    currentCarrierCKMDerivedParameterLabels :
      List String

    currentCarrierCKMDerivedParameterLabelsAreCanonical :
      currentCarrierCKMDerivedParameterLabels
      ≡
      "lambda"
      ∷ "|Vcb|"
      ∷ "deltaCP_candidate = arctan(sqrt 7)*(1-alpha1)"
      ∷ []

    unitarityTriangleApproach :
      String

    betaAngleDerivedFromCarrier :
      Bool

    betaAngleDerivedFromCarrierIsFalse :
      betaAngleDerivedFromCarrier ≡ false

    triangleUnderdetermined :
      Bool

    triangleUnderdeterminedIsTrue :
      triangleUnderdetermined ≡ true

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    fullVubPromoted :
      Bool

    fullVubPromotedIsFalse :
      fullVubPromoted ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    blockers :
      List VubOpenBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubOpenBlockers

    promotionFlags :
      List VubOpenPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubOpenStatusReceipt public

canonicalVubOpenStatusReceipt :
  VubOpenStatusReceipt
canonicalVubOpenStatusReceipt =
  record
    { vubStatus =
        vubOpen
    ; vubStatusIsOpen =
        refl
    ; vubStatusLabel =
        "open"
    ; vubStatusLabelIsOpen =
        refl
    ; requiresBetaFromCarrier =
        true
    ; requiresBetaFromCarrierIsTrue =
        refl
    ; betaSourceRequired =
        "carrier arithmetic"
    ; betaSourceRequiredIsCarrierArithmetic =
        refl
    ; betaSourcePDGAdmitted =
        false
    ; betaSourcePDGAdmittedIsFalse =
        refl
    ; currentCarrierCKMDerivedParameters =
        canonicalCarrierCKMDerivedParameters
    ; currentCarrierCKMDerivedParametersAreCanonical =
        refl
    ; currentCarrierCKMDerivedParameterLabels =
        "lambda"
        ∷ "|Vcb|"
        ∷ "deltaCP_candidate = arctan(sqrt 7)*(1-alpha1)"
        ∷ []
    ; currentCarrierCKMDerivedParameterLabelsAreCanonical =
        refl
    ; unitarityTriangleApproach =
        "requires beta angle from carrier arithmetic, not PDG"
    ; betaAngleDerivedFromCarrier =
        false
    ; betaAngleDerivedFromCarrierIsFalse =
        refl
    ; triangleUnderdetermined =
        true
    ; triangleUnderdeterminedIsTrue =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; fullVubPromoted =
        false
    ; fullVubPromotedIsFalse =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubOpenBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "|V_ub| remains open"
        ∷ "Current carrier CKM-derived parameters are lambda, |Vcb|, and deltaCP_candidate = arctan(sqrt 7)*(1-alpha1)"
        ∷ "The unitarity triangle needs beta from carrier arithmetic rather than PDG input"
        ∷ "Without beta from carrier structure, the triangle is underdetermined"
        ∷ "No physical CKM or full Vub promotion is asserted"
        ∷ []
    }

vubOpenStatusRemainsOpen :
  vubStatus canonicalVubOpenStatusReceipt ≡ vubOpen
vubOpenStatusRemainsOpen =
  refl

vubOpenStatusRequiresCarrierBeta :
  requiresBetaFromCarrier canonicalVubOpenStatusReceipt ≡ true
vubOpenStatusRequiresCarrierBeta =
  refl

vubOpenStatusDoesNotPromotePhysicalCKM :
  physicalCKMPromoted canonicalVubOpenStatusReceipt ≡ false
vubOpenStatusDoesNotPromotePhysicalCKM =
  refl

vubOpenStatusDoesNotPromoteFullVub :
  fullVubPromoted canonicalVubOpenStatusReceipt ≡ false
vubOpenStatusDoesNotPromoteFullVub =
  refl
