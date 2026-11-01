module DASHI.Physics.Closure.WolfensteinFullDiagnosticReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.VcbGeometricResummationReceipt as Vcb
import DASHI.Physics.Closure.Y13AlternativeFormulasReceipt as Y13
import DASHI.Physics.Closure.HeckeCharacterPhaseReceipt as Phase

------------------------------------------------------------------------
-- Full Wolfenstein diagnostic surface.

data WolfensteinFullDiagnosticStatus : Set where
  wolfensteinFullDiagnosticRecorded :
    WolfensteinFullDiagnosticStatus

data WolfensteinFullDiagnosticBlocker : Set where
  missingPhysicalCKMDiagonalisation :
    WolfensteinFullDiagnosticBlocker

  missingPhiDerivation :
    WolfensteinFullDiagnosticBlocker

  heckePhaseMismatch :
    WolfensteinFullDiagnosticBlocker

canonicalWolfensteinFullDiagnosticBlockers :
  List WolfensteinFullDiagnosticBlocker
canonicalWolfensteinFullDiagnosticBlockers =
  missingPhysicalCKMDiagonalisation
  ∷ missingPhiDerivation
  ∷ heckePhaseMismatch
  ∷ []

data WolfensteinFullDiagnosticPromotion : Set where

wolfensteinFullDiagnosticPromotionImpossibleHere :
  WolfensteinFullDiagnosticPromotion →
  ⊥
wolfensteinFullDiagnosticPromotionImpossibleHere ()

record WolfensteinFullDiagnosticReceipt : Setω where
  field
    status :
      WolfensteinFullDiagnosticStatus

    vcbReceipt :
      Vcb.VcbGeometricResummationReceipt

    y13AlternativesReceipt :
      Y13.Y13AlternativeFormulasReceipt

    y13AlternativesReceiptIsCanonical :
      y13AlternativesReceipt ≡ Y13.canonicalY13AlternativeFormulasReceipt

    heckePhaseReceipt :
      Phase.HeckeCharacterPhaseReceipt

    heckePhaseReceiptIsCanonical :
      heckePhaseReceipt ≡ Phase.canonicalHeckeCharacterPhaseReceipt

    lambdaFormula :
      String

    lambdaCarrier :
      Float

    lambdaRelativeErrorLabel :
      String

    aFormula :
      String

    aCarrierGeometric :
      Float

    aRelativeError :
      Float

    vubCandidateFormula :
      String

    vubCandidate :
      Float

    vubCandidateRelativeError :
      Float

    deltaFormula :
      String

    deltaCarrier :
      Float

    deltaRelativeErrorLabel :
      String

    correctedJarlskog :
      Float

    correctedJarlskogOverPDG :
      Float

    wolfensteinDiagnosticRecorded :
      Bool

    wolfensteinDiagnosticRecordedIsTrue :
      wolfensteinDiagnosticRecorded ≡ true

    physicalWolfensteinParametersDerived :
      Bool

    physicalWolfensteinParametersDerivedIsFalse :
      physicalWolfensteinParametersDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List WolfensteinFullDiagnosticBlocker

    blockersAreCanonical :
      blockers ≡ canonicalWolfensteinFullDiagnosticBlockers

    promotionFlags :
      List WolfensteinFullDiagnosticPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open WolfensteinFullDiagnosticReceipt public

canonicalWolfensteinFullDiagnosticReceipt :
  WolfensteinFullDiagnosticReceipt
canonicalWolfensteinFullDiagnosticReceipt =
  record
    { status =
        wolfensteinFullDiagnosticRecorded
    ; vcbReceipt =
        Vcb.canonicalVcbGeometricResummationReceipt
    ; y13AlternativesReceipt =
        Y13.canonicalY13AlternativeFormulasReceipt
    ; y13AlternativesReceiptIsCanonical =
        refl
    ; heckePhaseReceipt =
        Phase.canonicalHeckeCharacterPhaseReceipt
    ; heckePhaseReceiptIsCanonical =
        refl
    ; lambdaFormula =
        "lambda = alpha1*pi*sqrt(3)"
    ; lambdaCarrier =
        0.2244032573430574
    ; lambdaRelativeErrorLabel =
        "about -0.056 percent against lambda=0.22453"
    ; aFormula =
        "A = 14/(1-alpha1/2) * (8*pi/3)/(sqrt(24)*(pi*sqrt(3))^2)"
    ; aCarrierGeometric =
        0.8255982974316682
    ; aRelativeError =
        -0.00048632272195123347
    ; vubCandidateFormula =
        "|Vub| candidate = alpha1^3 * phi * 14/(1-alpha1/2) * (8*pi/3)/sqrt(24)"
    ; vubCandidate =
        0.002774172094698646
    ; vubCandidateRelativeError =
        -0.24819184425510948
    ; deltaFormula =
        "delta_29 = arg((1 + 2 i sqrt(7))/(5 + 2 i))"
    ; deltaCarrier =
        1.003510488600938
    ; deltaRelativeErrorLabel =
        "about -16 percent against 1.196 radians"
    ; correctedJarlskog =
        0.000021827497876325602
    ; correctedJarlskogOverPDG =
        0.7086849959845974
    ; wolfensteinDiagnosticRecorded =
        true
    ; wolfensteinDiagnosticRecordedIsTrue =
        refl
    ; physicalWolfensteinParametersDerived =
        false
    ; physicalWolfensteinParametersDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalWolfensteinFullDiagnosticBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "lambda and A are strong diagnostics"
        ∷ "The present Vub candidate still undershoots the PDG-sized target under the requested phi*14 convention"
        ∷ "The corrected Jarlskog is order-correct but remains diagnostic"
        ∷ "No physical Wolfenstein or CKM promotion is asserted"
        ∷ []
    }
