module DASHI.Physics.Closure.CKMUnitarityTriangleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WolfensteinFullDiagnosticReceipt as W

------------------------------------------------------------------------
-- Unitarity-triangle coordinates from the current diagnostic inputs.

data CKMUnitarityTriangleStatus : Set where
  ckmUnitarityTriangleDiagnosticRecorded :
    CKMUnitarityTriangleStatus

data CKMUnitarityTriangleBlocker : Set where
  vubMagnitudeStillDiagnostic :
    CKMUnitarityTriangleBlocker

  cpPhaseStillDiagnostic :
    CKMUnitarityTriangleBlocker

  missingCertifiedPhysicalCKMMatrix :
    CKMUnitarityTriangleBlocker

canonicalCKMUnitarityTriangleBlockers :
  List CKMUnitarityTriangleBlocker
canonicalCKMUnitarityTriangleBlockers =
  vubMagnitudeStillDiagnostic
  ∷ cpPhaseStillDiagnostic
  ∷ missingCertifiedPhysicalCKMMatrix
  ∷ []

data CKMUnitarityTrianglePromotion : Set where

ckmUnitarityTrianglePromotionImpossibleHere :
  CKMUnitarityTrianglePromotion →
  ⊥
ckmUnitarityTrianglePromotionImpossibleHere ()

record CKMUnitarityTriangleReceipt : Setω where
  field
    status :
      CKMUnitarityTriangleStatus

    wolfensteinFullReceipt :
      W.WolfensteinFullDiagnosticReceipt

    carrierLambda :
      Float

    carrierA :
      Float

    carrierVubCandidate :
      Float

    carrierDelta29 :
      Float

    carrierRhoBar :
      Float

    carrierEtaBar :
      Float

    pdgRhoBarComparison :
      Float

    pdgEtaBarComparison :
      Float

    triangleDiagnosticFigurePlan :
      String

    unitarityTriangleDiagnosticRecorded :
      Bool

    unitarityTriangleDiagnosticRecordedIsTrue :
      unitarityTriangleDiagnosticRecorded ≡ true

    triangleMatchesPDG :
      Bool

    triangleMatchesPDGIsFalse :
      triangleMatchesPDG ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CKMUnitarityTriangleBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMUnitarityTriangleBlockers

    promotionFlags :
      List CKMUnitarityTrianglePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMUnitarityTriangleReceipt public

canonicalCKMUnitarityTriangleReceipt :
  CKMUnitarityTriangleReceipt
canonicalCKMUnitarityTriangleReceipt =
  record
    { status =
        ckmUnitarityTriangleDiagnosticRecorded
    ; wolfensteinFullReceipt =
        W.canonicalWolfensteinFullDiagnosticReceipt
    ; carrierLambda =
        0.2244032573430574
    ; carrierA =
        0.8255982974316682
    ; carrierVubCandidate =
        0.002774172094698646
    ; carrierDelta29 =
        1.003510488600938
    ; carrierRhoBar =
        0.1597829220543562
    ; carrierEtaBar =
        0.2507791565071579
    ; pdgRhoBarComparison =
        0.145
    ; pdgEtaBarComparison =
        0.343
    ; triangleDiagnosticFigurePlan =
        "Plot vertices (0,0), (1,0), and (rho_bar,eta_bar) with carrier=(0.1598,0.2508) against PDG-sized comparison=(0.145,0.343)"
    ; unitarityTriangleDiagnosticRecorded =
        true
    ; unitarityTriangleDiagnosticRecordedIsTrue =
        refl
    ; triangleMatchesPDG =
        false
    ; triangleMatchesPDGIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMUnitarityTriangleBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The carrier unitarity triangle is a diagnostic plot target"
        ∷ "The eta coordinate is low under the current Hecke phase and Vub convention"
        ∷ "No CKM promotion is asserted"
        ∷ []
    }
