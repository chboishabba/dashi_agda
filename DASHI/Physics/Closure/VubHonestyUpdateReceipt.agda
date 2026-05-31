module DASHI.Physics.Closure.VubHonestyUpdateReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Honest Vub update receipt.
--
-- The adjacent-only carrier chain still identifies the structural source
-- of the up-type 1-3 entry: alpha1 alpha2.  This receipt records the
-- honesty boundary around that identification.  The formula |Vub| =
-- alpha1 alpha2 is only a leading-order readback in the pure up-type
-- rotation approximation U_d approx I.  When the next-order down-type
-- mixing contribution is included as the full three-term phased sum, the
-- numerical result is not a PDG match: the recorded diagnostic error is
-- 1073 percent.  Therefore the public claim must be labelled as a
-- leading-order / diagonal-Ud approximation, with the 4.2 percent PDG
-- comparison attached only to that approximation.

data VubApproximationRegime : Set where
  pureUpTypeRotationDiagonalUd :
    VubApproximationRegime

data VubNextOrderStatus : Set where
  fullDownTypeThreeTermPhasedSumFailsPDG :
    VubNextOrderStatus

data VubStructuralStatus : Set where
  upTypeOneThreeCarrierChainProductValid :
    VubStructuralStatus

data VubPrecisionRequirement : Set where
  requiresFullCarrierDiagonalisation :
    VubPrecisionRequirement

canonicalVubLeadingOrderFormula : String
canonicalVubLeadingOrderFormula =
  "|Vub| = alpha1 alpha2"

canonicalVubClaimLabel : String
canonicalVubClaimLabel =
  "leading-order / diagonal-Ud approximation"

canonicalDiagonalUdAssumption : String
canonicalDiagonalUdAssumption =
  "U_d approx I"

canonicalFullNextOrderFormula : String
canonicalFullNextOrderFormula =
  "full next-order down-type mixing is a three-term sum with phases"

canonicalFullNextOrderErrorLabel : String
canonicalFullNextOrderErrorLabel =
  "1073% error"

canonicalLeadingOrderErrorLabel : String
canonicalLeadingOrderErrorLabel =
  "4.2% error"

canonicalPrecisionRequirementLabel : String
canonicalPrecisionRequirementLabel =
  "precise |Vub| requires full carrier diagonalisation"

canonicalVubHonestyBoundary :
  List String
canonicalVubHonestyBoundary =
  "The formula |Vub| = alpha1 alpha2 holds only in the pure up-type rotation approximation U_d approx I"
  ∷ "The claim must be labelled as a leading-order / diagonal-Ud approximation"
  ∷ "That leading-order approximation matches the PDG-sized |Vub| comparison at 4.2% error"
  ∷ "The full next-order down-type mixing calculation is a three-term sum with phases"
  ∷ "The full next-order down-type mixing result has 1073% error and fails as a PDG match"
  ∷ "The structural identification of Vub with the up-type 1-3 carrier chain product remains valid"
  ∷ "A precise value requires full carrier diagonalisation"
  ∷ []

record VubHonestyUpdateReceipt : Set where
  field
    vubLeadingOrderOnly :
      Bool

    vubLeadingOrderOnlyIsTrue :
      vubLeadingOrderOnly ≡ true

    vubFormula :
      String

    vubFormulaIsAlpha1Alpha2 :
      vubFormula ≡ canonicalVubLeadingOrderFormula

    approximationRegime :
      VubApproximationRegime

    approximationRegimeIsPureUpTypeRotation :
      approximationRegime ≡ pureUpTypeRotationDiagonalUd

    diagonalUdAssumption :
      String

    diagonalUdAssumptionIsCanonical :
      diagonalUdAssumption ≡ canonicalDiagonalUdAssumption

    diagnosticLabelRequired :
      Bool

    diagnosticLabelRequiredIsTrue :
      diagnosticLabelRequired ≡ true

    requiredDiagnosticLabel :
      String

    requiredDiagnosticLabelIsCanonical :
      requiredDiagnosticLabel ≡ canonicalVubClaimLabel

    leadingOrderPDGErrorPercent :
      Float

    leadingOrderPDGErrorPercentIsFourPointTwo :
      leadingOrderPDGErrorPercent ≡ 4.2

    leadingOrderPDGErrorLabel :
      String

    leadingOrderPDGErrorLabelIsCanonical :
      leadingOrderPDGErrorLabel ≡ canonicalLeadingOrderErrorLabel

    vubFullNextOrderFails :
      Bool

    vubFullNextOrderFailsIsTrue :
      vubFullNextOrderFails ≡ true

    fullNextOrderStatus :
      VubNextOrderStatus

    fullNextOrderStatusIsThreeTermPhasedSumFailsPDG :
      fullNextOrderStatus ≡ fullDownTypeThreeTermPhasedSumFailsPDG

    fullNextOrderFormula :
      String

    fullNextOrderFormulaIsCanonical :
      fullNextOrderFormula ≡ canonicalFullNextOrderFormula

    fullNextOrderErrorPercent :
      Float

    fullNextOrderErrorPercentIsOneThousandSeventyThree :
      fullNextOrderErrorPercent ≡ 1073.0

    fullNextOrderErrorLabel :
      String

    fullNextOrderErrorLabelIsCanonical :
      fullNextOrderErrorLabel ≡ canonicalFullNextOrderErrorLabel

    structuralIdentificationValid :
      Bool

    structuralIdentificationValidIsTrue :
      structuralIdentificationValid ≡ true

    structuralStatus :
      VubStructuralStatus

    structuralStatusIsUpTypeOneThreeCarrierChainProductValid :
      structuralStatus ≡ upTypeOneThreeCarrierChainProductValid

    precisionRequirement :
      VubPrecisionRequirement

    precisionRequirementIsFullCarrierDiagonalisation :
      precisionRequirement ≡ requiresFullCarrierDiagonalisation

    precisionRequirementLabel :
      String

    precisionRequirementLabelIsCanonical :
      precisionRequirementLabel ≡ canonicalPrecisionRequirementLabel

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalVubHonestyBoundary

open VubHonestyUpdateReceipt public

canonicalVubHonestyUpdateReceipt :
  VubHonestyUpdateReceipt
canonicalVubHonestyUpdateReceipt =
  record
    { vubLeadingOrderOnly =
        true
    ; vubLeadingOrderOnlyIsTrue =
        refl
    ; vubFormula =
        canonicalVubLeadingOrderFormula
    ; vubFormulaIsAlpha1Alpha2 =
        refl
    ; approximationRegime =
        pureUpTypeRotationDiagonalUd
    ; approximationRegimeIsPureUpTypeRotation =
        refl
    ; diagonalUdAssumption =
        canonicalDiagonalUdAssumption
    ; diagonalUdAssumptionIsCanonical =
        refl
    ; diagnosticLabelRequired =
        true
    ; diagnosticLabelRequiredIsTrue =
        refl
    ; requiredDiagnosticLabel =
        canonicalVubClaimLabel
    ; requiredDiagnosticLabelIsCanonical =
        refl
    ; leadingOrderPDGErrorPercent =
        4.2
    ; leadingOrderPDGErrorPercentIsFourPointTwo =
        refl
    ; leadingOrderPDGErrorLabel =
        canonicalLeadingOrderErrorLabel
    ; leadingOrderPDGErrorLabelIsCanonical =
        refl
    ; vubFullNextOrderFails =
        true
    ; vubFullNextOrderFailsIsTrue =
        refl
    ; fullNextOrderStatus =
        fullDownTypeThreeTermPhasedSumFailsPDG
    ; fullNextOrderStatusIsThreeTermPhasedSumFailsPDG =
        refl
    ; fullNextOrderFormula =
        canonicalFullNextOrderFormula
    ; fullNextOrderFormulaIsCanonical =
        refl
    ; fullNextOrderErrorPercent =
        1073.0
    ; fullNextOrderErrorPercentIsOneThousandSeventyThree =
        refl
    ; fullNextOrderErrorLabel =
        canonicalFullNextOrderErrorLabel
    ; fullNextOrderErrorLabelIsCanonical =
        refl
    ; structuralIdentificationValid =
        true
    ; structuralIdentificationValidIsTrue =
        refl
    ; structuralStatus =
        upTypeOneThreeCarrierChainProductValid
    ; structuralStatusIsUpTypeOneThreeCarrierChainProductValid =
        refl
    ; precisionRequirement =
        requiresFullCarrierDiagonalisation
    ; precisionRequirementIsFullCarrierDiagonalisation =
        refl
    ; precisionRequirementLabel =
        canonicalPrecisionRequirementLabel
    ; precisionRequirementLabelIsCanonical =
        refl
    ; receiptBoundary =
        canonicalVubHonestyBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

vubHonestyLeadingOrderOnly :
  vubLeadingOrderOnly canonicalVubHonestyUpdateReceipt ≡ true
vubHonestyLeadingOrderOnly =
  refl

vubHonestyFullNextOrderFails :
  vubFullNextOrderFails canonicalVubHonestyUpdateReceipt ≡ true
vubHonestyFullNextOrderFails =
  refl

vubHonestyFullNextOrderErrorIs1073Percent :
  fullNextOrderErrorLabel canonicalVubHonestyUpdateReceipt
  ≡
  "1073% error"
vubHonestyFullNextOrderErrorIs1073Percent =
  refl

vubHonestyDiagnosticLabelRequired :
  diagnosticLabelRequired canonicalVubHonestyUpdateReceipt ≡ true
vubHonestyDiagnosticLabelRequired =
  refl

vubHonestyStructuralIdentificationValid :
  structuralIdentificationValid canonicalVubHonestyUpdateReceipt ≡ true
vubHonestyStructuralIdentificationValid =
  refl

vubHonestyPrecisionRequiresFullCarrierDiagonalisation :
  precisionRequirement canonicalVubHonestyUpdateReceipt
  ≡
  requiresFullCarrierDiagonalisation
vubHonestyPrecisionRequiresFullCarrierDiagonalisation =
  refl
