module DASHI.Physics.Closure.CKMFullMatrixFromCarrierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YukawaNormalisationStructureReceipt as Norm

------------------------------------------------------------------------
-- Full CKM carrier matrix diagnostic.
--
-- This records the current direct carrier readback for the CKM matrix.  The
-- lambda entry is the direct formula, while the degree-12 route is recorded
-- as internally inconsistent because it requires a non-integer exponent.

data CKMFullMatrixFromCarrierStatus : Set where
  ckmFullMatrixCarrierDiagnosticRecorded :
    CKMFullMatrixFromCarrierStatus

data CKMFullMatrixFromCarrierBlocker : Set where
  deg12NonIntegerExponentInconsistency :
    CKMFullMatrixFromCarrierBlocker

  missingCertifiedPhysicalDiagonalisation :
    CKMFullMatrixFromCarrierBlocker

  missingPDGCKMAuthorityBinding :
    CKMFullMatrixFromCarrierBlocker

canonicalCKMFullMatrixFromCarrierBlockers :
  List CKMFullMatrixFromCarrierBlocker
canonicalCKMFullMatrixFromCarrierBlockers =
  deg12NonIntegerExponentInconsistency
  ∷ missingCertifiedPhysicalDiagonalisation
  ∷ missingPDGCKMAuthorityBinding
  ∷ []

data CKMFullMatrixFromCarrierPromotion : Set where

ckmFullMatrixFromCarrierPromotionImpossibleHere :
  CKMFullMatrixFromCarrierPromotion →
  ⊥
ckmFullMatrixFromCarrierPromotionImpossibleHere ()

lambdaDirectFormulaLabel : String
lambdaDirectFormulaLabel =
  "lambda_direct = alpha1*pi*sqrt(3)"

deg12InconsistencyLabel : String
deg12InconsistencyLabel =
  "degree-12 lambda route is inconsistent: matching lambda requires a non-integer carrier exponent"

record CKMFullMatrixFromCarrierReceipt : Set where
  field
    status :
      CKMFullMatrixFromCarrierStatus

    normalisationReceipt :
      Norm.YukawaNormalisationStructureReceipt

    normalisationReceiptIsCanonical :
      normalisationReceipt
      ≡
      Norm.canonicalYukawaNormalisationStructureReceipt

    lambdaFormula :
      String

    lambdaFormulaIsDirectCarrierFormula :
      lambdaFormula ≡ lambdaDirectFormulaLabel

    lambdaDirect :
      Float

    matrixConvention :
      String

    ckmRow1Diagnostic :
      String

    ckmRow2Diagnostic :
      String

    ckmRow3Diagnostic :
      String

    deg12RouteDegree :
      Nat

    deg12RouteDegreeIsTwelve :
      deg12RouteDegree ≡ 12

    deg12DiagnosticStatement :
      String

    deg12DiagnosticStatementIsCanonical :
      deg12DiagnosticStatement ≡ deg12InconsistencyLabel

    deg12RouteHasNonIntegerExponentInconsistency :
      Bool

    deg12RouteHasNonIntegerExponentInconsistencyIsTrue :
      deg12RouteHasNonIntegerExponentInconsistency ≡ true

    fullMatrixDiagnosticRecorded :
      Bool

    fullMatrixDiagnosticRecordedIsTrue :
      fullMatrixDiagnosticRecorded ≡ true

    certifiedPhysicalDiagonalisationConstructed :
      Bool

    certifiedPhysicalDiagonalisationConstructedIsFalse :
      certifiedPhysicalDiagonalisationConstructed ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    fullCKMPromoted :
      Bool

    fullCKMPromotedIsFalse :
      fullCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    blockers :
      List CKMFullMatrixFromCarrierBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMFullMatrixFromCarrierBlockers

    promotionFlags :
      List CKMFullMatrixFromCarrierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMFullMatrixFromCarrierReceipt public

canonicalCKMFullMatrixFromCarrierReceipt :
  CKMFullMatrixFromCarrierReceipt
canonicalCKMFullMatrixFromCarrierReceipt =
  record
    { status =
        ckmFullMatrixCarrierDiagnosticRecorded
    ; normalisationReceipt =
        Norm.canonicalYukawaNormalisationStructureReceipt
    ; normalisationReceiptIsCanonical =
        refl
    ; lambdaFormula =
        lambdaDirectFormulaLabel
    ; lambdaFormulaIsDirectCarrierFormula =
        refl
    ; lambdaDirect =
        0.2244032573430574
    ; matrixConvention =
        "carrier CKM diagnostic uses lambda_direct plus carrier hierarchy entries; rows are comparison labels, not certified diagonalisation output"
    ; ckmRow1Diagnostic =
        "[Vud,Vus,Vub] diagnostic row uses lambda_direct and the recorded carrier Vub diagnostic"
    ; ckmRow2Diagnostic =
        "[Vcd,Vcs,Vcb] diagnostic row uses lambda_direct and carrier Vcb hierarchy"
    ; ckmRow3Diagnostic =
        "[Vtd,Vts,Vtb] diagnostic row is retained as a carrier full-matrix diagnostic only"
    ; deg12RouteDegree =
        12
    ; deg12RouteDegreeIsTwelve =
        refl
    ; deg12DiagnosticStatement =
        deg12InconsistencyLabel
    ; deg12DiagnosticStatementIsCanonical =
        refl
    ; deg12RouteHasNonIntegerExponentInconsistency =
        true
    ; deg12RouteHasNonIntegerExponentInconsistencyIsTrue =
        refl
    ; fullMatrixDiagnosticRecorded =
        true
    ; fullMatrixDiagnosticRecordedIsTrue =
        refl
    ; certifiedPhysicalDiagonalisationConstructed =
        false
    ; certifiedPhysicalDiagonalisationConstructedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; fullCKMPromoted =
        false
    ; fullCKMPromotedIsFalse =
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
        canonicalCKMFullMatrixFromCarrierBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The full CKM carrier matrix is recorded as a diagnostic surface"
        ∷ "lambda is the direct alpha1*pi*sqrt(3) carrier formula"
        ∷ "The degree-12 lambda route fails because it requires a non-integer exponent"
        ∷ "No full CKM, physical CKM, terminal, or Clay promotion is asserted"
        ∷ []
    }

ckmFullMatrixFromCarrierDoesNotPromoteCKM :
  physicalCKMPromoted canonicalCKMFullMatrixFromCarrierReceipt ≡ false
ckmFullMatrixFromCarrierDoesNotPromoteCKM =
  refl

ckmFullMatrixFromCarrierDoesNotPromoteFullCKM :
  fullCKMPromoted canonicalCKMFullMatrixFromCarrierReceipt ≡ false
ckmFullMatrixFromCarrierDoesNotPromoteFullCKM =
  refl

ckmFullMatrixFromCarrierRecordsDeg12Inconsistency :
  deg12RouteHasNonIntegerExponentInconsistency
    canonicalCKMFullMatrixFromCarrierReceipt
  ≡
  true
ckmFullMatrixFromCarrierRecordsDeg12Inconsistency =
  refl
