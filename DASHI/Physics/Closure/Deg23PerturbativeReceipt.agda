module DASHI.Physics.Closure.Deg23PerturbativeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- deg23 perturbative/geometric correction diagnostic.
--
-- This receipt separates two comparison surfaces that were previously easy
-- to conflate:
--
--   * The Wolfenstein-A residual is almost removed by the geometric factor
--     1/(1-alpha1/2), giving A ~= 0.825598 against a PDG-sized 0.826 target.
--   * The same factor does not improve a direct |V_cb| comparison to 0.0408;
--     it raises the diagnostic value to ~= 0.041575.
--
-- Therefore the receipt records a useful A-lane diagnostic, not a physical
-- Vcb derivation.

data Deg23PerturbativeStatus : Set where
  deg23PerturbativeAndGeometricDiagnosticsRecorded :
    Deg23PerturbativeStatus

data Deg23PerturbativeBlocker : Set where
  geometricFactorLacksDiagrammaticProof :
    Deg23PerturbativeBlocker

  wolfensteinAComparisonIsNotPhysicalVcb :
    Deg23PerturbativeBlocker

  directVcbComparisonNotImproved :
    Deg23PerturbativeBlocker

  missingPDGAuthorityBinding :
    Deg23PerturbativeBlocker

canonicalDeg23PerturbativeBlockers :
  List Deg23PerturbativeBlocker
canonicalDeg23PerturbativeBlockers =
  geometricFactorLacksDiagrammaticProof
  ∷ wolfensteinAComparisonIsNotPhysicalVcb
  ∷ directVcbComparisonNotImproved
  ∷ missingPDGAuthorityBinding
  ∷ []

data Deg23PerturbativePromotion : Set where

deg23PerturbativePromotionImpossibleHere :
  Deg23PerturbativePromotion →
  ⊥
deg23PerturbativePromotionImpossibleHere ()

record Deg23PerturbativeReceipt : Setω where
  field
    status :
      Deg23PerturbativeStatus

    diagnosticScript :
      String

    alpha1Label :
      String

    firstOrderFormula :
      String

    firstOrderDeg23 :
      Float

    firstOrderA :
      Float

    firstOrderRelativeErrorAgainstA :
      Float

    geometricFormula :
      String

    geometricDeg23 :
      Float

    geometricA :
      Float

    geometricRelativeErrorAgainstA :
      Float

    geometricVcb :
      Float

    geometricRelativeErrorAgainstVcb :
      Float

    deg23PerturbativeDiagnosticRecorded :
      Bool

    deg23PerturbativeDiagnosticRecordedIsTrue :
      deg23PerturbativeDiagnosticRecorded ≡ true

    wolfensteinADiagnosticImproved :
      Bool

    wolfensteinADiagnosticImprovedIsTrue :
      wolfensteinADiagnosticImproved ≡ true

    directPhysicalVcbDerived :
      Bool

    directPhysicalVcbDerivedIsFalse :
      directPhysicalVcbDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Deg23PerturbativeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23PerturbativeBlockers

    promotionFlags :
      List Deg23PerturbativePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23PerturbativeReceipt public

canonicalDeg23PerturbativeReceipt :
  Deg23PerturbativeReceipt
canonicalDeg23PerturbativeReceipt =
  record
    { status =
        deg23PerturbativeAndGeometricDiagnosticsRecorded
    ; diagnosticScript =
        "scripts/check_golden_ratio_ckm_diagnostics.py"
    ; alpha1Label =
        "alpha1 = 0.041240"
    ; firstOrderFormula =
        "deg23 = 14 * (1 + alpha1/2)"
    ; firstOrderDeg23 =
        14.288680000000001
    ; firstOrderA =
        0.8252472659149338
    ; firstOrderRelativeErrorAgainstA =
        -0.0009113003451164086
    ; geometricFormula =
        "deg23 = 14 / (1 - alpha1/2)"
    ; geometricDeg23 =
        14.294757908064284
    ; geometricA =
        0.8255982974316682
    ; geometricRelativeErrorAgainstA =
        -0.00048632272195123347
    ; geometricVcb =
        0.04157450642980736
    ; geometricRelativeErrorAgainstVcb =
        0.018983000730572488
    ; deg23PerturbativeDiagnosticRecorded =
        true
    ; deg23PerturbativeDiagnosticRecordedIsTrue =
        refl
    ; wolfensteinADiagnosticImproved =
        true
    ; wolfensteinADiagnosticImprovedIsTrue =
        refl
    ; directPhysicalVcbDerived =
        false
    ; directPhysicalVcbDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23PerturbativeBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The geometric factor improves the Wolfenstein-A comparison to about -0.049 percent"
        ∷ "The same factor does not derive the direct physical |V_cb| value"
        ∷ "No CKM or Vcb promotion is asserted by this diagnostic"
        ∷ []
    }

deg23PerturbativeDoesNotPromoteCKM :
  physicalCKMPromoted canonicalDeg23PerturbativeReceipt ≡ false
deg23PerturbativeDoesNotPromoteCKM =
  refl
