module DASHI.Physics.Closure.VubFromCKMUnitarityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Vub from CKM unitarity via a CP-phase candidate.
--
-- This receipt records the obstruction rather than promoting |Vub|.  Given
-- lambda, |Vcb|, and a CP phase candidate, the unitarity triangle determines
-- only an angle gamma/delta.  It does not determine the radius R_ub without
-- another side, equivalently an additional input such as |Vtd|.  Therefore
-- the Wolfenstein relation |Vub| = A lambda^3 sqrt (rho^2 + eta^2) remains
-- underdetermined here.

data VubFromCKMUnitarityStatus : Set where
  vubFromUnitarityViaCPPhaseOpenRecorded :
    VubFromCKMUnitarityStatus

data VubFromCKMUnitarityBlocker : Set where
  cpPhaseGivesAngleNotRadius :
    VubFromCKMUnitarityBlocker

  missingSecondTriangleSide :
    VubFromCKMUnitarityBlocker

  missingVtdInput :
    VubFromCKMUnitarityBlocker

  missingRubDetermination :
    VubFromCKMUnitarityBlocker

canonicalVubFromCKMUnitarityBlockers :
  List VubFromCKMUnitarityBlocker
canonicalVubFromCKMUnitarityBlockers =
  cpPhaseGivesAngleNotRadius
  ∷ missingSecondTriangleSide
  ∷ missingVtdInput
  ∷ missingRubDetermination
  ∷ []

data VubFromCKMUnitarityPromotion : Set where

vubFromCKMUnitarityPromotionImpossibleHere :
  VubFromCKMUnitarityPromotion →
  ⊥
vubFromCKMUnitarityPromotionImpossibleHere ()

openStatusLabel : String
openStatusLabel =
  "open"

cpPhaseAngleGammaLabel : String
cpPhaseAngleGammaLabel =
  "arctan(sqrt7)*(1-alpha1)"

wolfensteinVubFormulaLabel : String
wolfensteinVubFormulaLabel =
  "|Vub| = A lambda^3 sqrt(rho^2+eta^2)"

cpPhaseInsufficiencyLabel : String
cpPhaseInsufficiencyLabel =
  "CP phase fixes gamma/delta but not the radius R_ub"

record VubFromCKMUnitarityReceipt : Set where
  field
    status :
      VubFromCKMUnitarityStatus

    vubFromUnitarityViaCPPhase :
      String

    vubFromUnitarityViaCPPhaseIsOpen :
      vubFromUnitarityViaCPPhase ≡ openStatusLabel

    lambdaSupplied :
      Bool

    lambdaSuppliedIsTrue :
      lambdaSupplied ≡ true

    vcbMagnitudeSupplied :
      Bool

    vcbMagnitudeSuppliedIsTrue :
      vcbMagnitudeSupplied ≡ true

    cpPhaseCandidateSupplied :
      Bool

    cpPhaseCandidateSuppliedIsTrue :
      cpPhaseCandidateSupplied ≡ true

    cpPhaseAngleGamma :
      String

    cpPhaseAngleGammaIsCanonical :
      cpPhaseAngleGamma ≡ cpPhaseAngleGammaLabel

    wolfensteinVubFormula :
      String

    wolfensteinVubFormulaIsCanonical :
      wolfensteinVubFormula ≡ wolfensteinVubFormulaLabel

    cpPhaseDeterminesAngle :
      Bool

    cpPhaseDeterminesAngleIsTrue :
      cpPhaseDeterminesAngle ≡ true

    cpPhaseDeterminesRadiusRub :
      Bool

    cpPhaseDeterminesRadiusRubIsFalse :
      cpPhaseDeterminesRadiusRub ≡ false

    cpPhaseInsufficiency :
      String

    cpPhaseInsufficiencyIsCanonical :
      cpPhaseInsufficiency ≡ cpPhaseInsufficiencyLabel

    requiresAnotherSide :
      Bool

    requiresAnotherSideIsTrue :
      requiresAnotherSide ≡ true

    requiresVtd :
      Bool

    requiresVtdIsTrue :
      requiresVtd ≡ true

    rhoEtaDeterminedByInputs :
      Bool

    rhoEtaDeterminedByInputsIsFalse :
      rhoEtaDeterminedByInputs ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubFromCKMUnitarityBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubFromCKMUnitarityBlockers

    promotionFlags :
      List VubFromCKMUnitarityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubFromCKMUnitarityReceipt public

canonicalVubFromCKMUnitarityReceipt :
  VubFromCKMUnitarityReceipt
canonicalVubFromCKMUnitarityReceipt =
  record
    { status =
        vubFromUnitarityViaCPPhaseOpenRecorded
    ; vubFromUnitarityViaCPPhase =
        openStatusLabel
    ; vubFromUnitarityViaCPPhaseIsOpen =
        refl
    ; lambdaSupplied =
        true
    ; lambdaSuppliedIsTrue =
        refl
    ; vcbMagnitudeSupplied =
        true
    ; vcbMagnitudeSuppliedIsTrue =
        refl
    ; cpPhaseCandidateSupplied =
        true
    ; cpPhaseCandidateSuppliedIsTrue =
        refl
    ; cpPhaseAngleGamma =
        cpPhaseAngleGammaLabel
    ; cpPhaseAngleGammaIsCanonical =
        refl
    ; wolfensteinVubFormula =
        wolfensteinVubFormulaLabel
    ; wolfensteinVubFormulaIsCanonical =
        refl
    ; cpPhaseDeterminesAngle =
        true
    ; cpPhaseDeterminesAngleIsTrue =
        refl
    ; cpPhaseDeterminesRadiusRub =
        false
    ; cpPhaseDeterminesRadiusRubIsFalse =
        refl
    ; cpPhaseInsufficiency =
        cpPhaseInsufficiencyLabel
    ; cpPhaseInsufficiencyIsCanonical =
        refl
    ; requiresAnotherSide =
        true
    ; requiresAnotherSideIsTrue =
        refl
    ; requiresVtd =
        true
    ; requiresVtdIsTrue =
        refl
    ; rhoEtaDeterminedByInputs =
        false
    ; rhoEtaDeterminedByInputsIsFalse =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubFromCKMUnitarityBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "vubFromUnitarityViaCPPhase is recorded as open"
        ∷ "lambda, |Vcb|, and the CP phase candidate are recorded as supplied"
        ∷ "cpPhaseAngleGamma is arctan(sqrt7)*(1-alpha1)"
        ∷ "The CP phase gives gamma/delta but not the radius R_ub"
        ∷ "The formula |Vub| = A lambda^3 sqrt(rho^2+eta^2) still needs rho and eta radius data"
        ∷ "Another side, for example |Vtd|, is required"
        ∷ "physicalVubPromoted remains false"
        ∷ []
    }

vubFromUnitarityViaCPPhaseRemainsOpen :
  vubFromUnitarityViaCPPhase canonicalVubFromCKMUnitarityReceipt
  ≡
  openStatusLabel
vubFromUnitarityViaCPPhaseRemainsOpen =
  refl

vubFromUnitarityViaCPPhaseRequiresVtd :
  requiresVtd canonicalVubFromCKMUnitarityReceipt ≡ true
vubFromUnitarityViaCPPhaseRequiresVtd =
  refl

vubFromUnitarityViaCPPhaseDoesNotDetermineRub :
  cpPhaseDeterminesRadiusRub canonicalVubFromCKMUnitarityReceipt ≡ false
vubFromUnitarityViaCPPhaseDoesNotDetermineRub =
  refl

vubFromUnitarityViaCPPhaseDoesNotPromoteVub :
  physicalVubPromoted canonicalVubFromCKMUnitarityReceipt ≡ false
vubFromUnitarityViaCPPhaseDoesNotPromoteVub =
  refl
