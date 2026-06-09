module DASHI.Physics.Closure.VcbGeometricResummationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23PerturbativeReceipt as Deg23

------------------------------------------------------------------------
-- Geometric resummation diagnostic for the p3-p5 lane.

data VcbGeometricResummationStatus : Set where
  vcbGeometricResummationDiagnosticRecorded :
    VcbGeometricResummationStatus

data VcbGeometricResummationBlocker : Set where
  missingDysonLadderProof :
    VcbGeometricResummationBlocker

  missingSymmetryFactorProof :
    VcbGeometricResummationBlocker

  wolfensteinADiagnosticNotPhysicalVcb :
    VcbGeometricResummationBlocker

canonicalVcbGeometricResummationBlockers :
  List VcbGeometricResummationBlocker
canonicalVcbGeometricResummationBlockers =
  missingDysonLadderProof
  ∷ missingSymmetryFactorProof
  ∷ wolfensteinADiagnosticNotPhysicalVcb
  ∷ []

data VcbGeometricResummationPromotion : Set where

vcbGeometricResummationPromotionImpossibleHere :
  VcbGeometricResummationPromotion →
  ⊥
vcbGeometricResummationPromotionImpossibleHere ()

record VcbGeometricResummationReceipt : Setω where
  field
    status :
      VcbGeometricResummationStatus

    y23Formula :
      String

    vcbFormula :
      String

    resummationInterpretation :
      String

    resummedDeg23 :
      Float

    resummedY23 :
      Float

    resummedWolfensteinA :
      Float

    resummedWolfensteinARelativeError :
      Float

    resummedVcb :
      Float

    resummedVcbRelativeError :
      Float

    vcbGeometricResummationDiagnostic :
      Bool

    vcbGeometricResummationDiagnosticIsTrue :
      vcbGeometricResummationDiagnostic ≡ true

    dysonLadderDerivationInhabited :
      Bool

    dysonLadderDerivationInhabitedIsFalse :
      dysonLadderDerivationInhabited ≡ false

    physicalVcbPromoted :
      Bool

    physicalVcbPromotedIsFalse :
      physicalVcbPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VcbGeometricResummationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVcbGeometricResummationBlockers

    promotionFlags :
      List VcbGeometricResummationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VcbGeometricResummationReceipt public

canonicalVcbGeometricResummationReceipt :
  VcbGeometricResummationReceipt
canonicalVcbGeometricResummationReceipt =
  record
    { status =
        vcbGeometricResummationDiagnosticRecorded
    ; y23Formula =
        "(Y_d)23 = (14/(1-alpha1/2)) * (8*pi/3)/sqrt(24)"
    ; vcbFormula =
        "|V_cb|_diag = alpha1^2 * (Y_d)23"
    ; resummationInterpretation =
        "1/(1-alpha1/2) is recorded as a Dyson-ladder self-energy hypothesis with p2-loop symmetry factor 1/2"
    ; resummedDeg23 =
        14.294757908064284
    ; resummedY23 =
        24.445275244892734
    ; resummedWolfensteinA =
        0.8255982974316682
    ; resummedWolfensteinARelativeError =
        -0.00048632272195123347
    ; resummedVcb =
        0.04157450642980736
    ; resummedVcbRelativeError =
        0.018983000730572488
    ; vcbGeometricResummationDiagnostic =
        true
    ; vcbGeometricResummationDiagnosticIsTrue =
        refl
    ; dysonLadderDerivationInhabited =
        false
    ; dysonLadderDerivationInhabitedIsFalse =
        refl
    ; physicalVcbPromoted =
        false
    ; physicalVcbPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVcbGeometricResummationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The geometric factor is a sharp Wolfenstein-A diagnostic"
        ∷ "The ladder interpretation is a hypothesis, not a proved carrier diagram expansion"
        ∷ "Direct physical |V_cb| and CKM promotions remain false"
        ∷ []
    }

vcbGeometricResummationDoesNotPromote :
  physicalVcbPromoted canonicalVcbGeometricResummationReceipt ≡ false
vcbGeometricResummationDoesNotPromote =
  refl
