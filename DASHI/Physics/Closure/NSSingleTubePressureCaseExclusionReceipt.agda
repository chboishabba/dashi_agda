module DASHI.Physics.Closure.NSSingleTubePressureCaseExclusionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes single-tube pressure case exclusion receipt.
--
-- This file is a fail-closed bookkeeping surface for Route 1.
-- It records two branches only:
--
--   * straight tube: Q = 0, so the diagonal pressure route stays the
--     live sign gate
--   * curved tube: Q != 0, so the second-order sign surface stays
--     external and conditional
--
-- Neither branch is promoted.  No theorem, Clay, or terminal claim is
-- issued here.

data NSSingleTubePressureCaseExclusionStatus : Set where
  route1SingleTubePressureCaseRecordedFailClosed :
    NSSingleTubePressureCaseExclusionStatus

data NSSingleTubePressureCaseBranch : Set where
  straightTubeQZero :
    NSSingleTubePressureCaseBranch

  curvedTubeNonzeroQ :
    NSSingleTubePressureCaseBranch

canonicalBranches :
  List NSSingleTubePressureCaseBranch
canonicalBranches =
  straightTubeQZero
  ∷ curvedTubeNonzeroQ
  ∷ []

data NSSingleTubePressureCaseAssumption : Set where
  straightTubeHasQZero :
    NSSingleTubePressureCaseAssumption

  straightTubeKeepsDiagonalPressureRouteAsLiveSignGate :
    NSSingleTubePressureCaseAssumption

  curvedTubeHasNonzeroQ :
    NSSingleTubePressureCaseAssumption

  curvedTubeSecondOrderSignSurfaceIsExternalAndConditional :
    NSSingleTubePressureCaseAssumption

  bothBranchesStayNonPromoting :
    NSSingleTubePressureCaseAssumption

data NSSingleTubePressureCaseStage : Set where
  stage1StraightTubeQZeroAudit :
    NSSingleTubePressureCaseStage

  stage2DiagonalPressureGateAudit :
    NSSingleTubePressureCaseStage

  stage3CurvedTubeConditionalSurfaceAudit :
    NSSingleTubePressureCaseStage

  stage4NonPromotionLedger :
    NSSingleTubePressureCaseStage

data NSSingleTubePressureCaseBlocker : Set where
  noStraightTubeTheoremPromotion :
    NSSingleTubePressureCaseBlocker

  noCurvedTubeTheoremPromotion :
    NSSingleTubePressureCaseBlocker

  noExternalConditionalSurfacePromotion :
    NSSingleTubePressureCaseBlocker

  noTerminalPromotion :
    NSSingleTubePressureCaseBlocker

  noClayPromotion :
    NSSingleTubePressureCaseBlocker

data NSSingleTubePressureCasePromotion : Set where

canonicalAssumptions :
  List NSSingleTubePressureCaseAssumption
canonicalAssumptions =
  straightTubeHasQZero
  ∷ straightTubeKeepsDiagonalPressureRouteAsLiveSignGate
  ∷ curvedTubeHasNonzeroQ
  ∷ curvedTubeSecondOrderSignSurfaceIsExternalAndConditional
  ∷ bothBranchesStayNonPromoting
  ∷ []

canonicalStages :
  List NSSingleTubePressureCaseStage
canonicalStages =
  stage1StraightTubeQZeroAudit
  ∷ stage2DiagonalPressureGateAudit
  ∷ stage3CurvedTubeConditionalSurfaceAudit
  ∷ stage4NonPromotionLedger
  ∷ []

canonicalBlockers :
  List NSSingleTubePressureCaseBlocker
canonicalBlockers =
  noStraightTubeTheoremPromotion
  ∷ noCurvedTubeTheoremPromotion
  ∷ noExternalConditionalSurfacePromotion
  ∷ noTerminalPromotion
  ∷ noClayPromotion
  ∷ []

canonicalStraightTubeQZeroSurface : String
canonicalStraightTubeQZeroSurface =
  "Straight tube branch: Q=0."

canonicalDiagonalPressureRouteSurface : String
canonicalDiagonalPressureRouteSurface =
  "Diagonal pressure route remains the live sign gate."

canonicalCurvedTubeNonzeroQSurface : String
canonicalCurvedTubeNonzeroQSurface =
  "Curved tube branch: Q!=0."

canonicalCurvedTubeSecondOrderSurface : String
canonicalCurvedTubeSecondOrderSurface =
  "Curved tube second-order sign surface stays external and conditional."

canonicalNonPromotingSurface : String
canonicalNonPromotingSurface =
  "Both branches stay non-promoting."

controlSummary : List String
controlSummary =
  "O: Record the straight-tube and curved-tube Route 1 audit surface as fail-closed bookkeeping."
  ∷ "R: Straight tube Q=0 keeps the diagonal pressure route as the live sign gate."
  ∷ "C: Curved tube Q!=0 keeps the second-order sign surface external and conditional."
  ∷ "S: The two branches are tracked separately and neither one proves a sign theorem."
  ∷ "L: Straight tube -> diagonal pressure gate; curved tube -> external conditional second-order surface."
  ∷ "P: Promote nothing here; this is ledger-only routing."
  ∷ "G: Fail closed: theorem, Clay, terminal, and branch promotion bits stay false."
  ∷ "F: Both branches remain non-promoting."
  ∷ []

data NSSingleTubePressureCaseExclusionPromotionBit : Set where

record NSSingleTubePressureCaseExclusionReceipt : Set where
  field
    status :
      NSSingleTubePressureCaseExclusionStatus

    statusIsCanonical :
      status ≡ route1SingleTubePressureCaseRecordedFailClosed

    branches :
      List NSSingleTubePressureCaseBranch

    branchesAreCanonical :
      branches ≡ canonicalBranches

    assumptions :
      List NSSingleTubePressureCaseAssumption

    assumptionsAreCanonical :
      assumptions ≡ canonicalAssumptions

    stages :
      List NSSingleTubePressureCaseStage

    stagesAreCanonical :
      stages ≡ canonicalStages

    blockers :
      List NSSingleTubePressureCaseBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBlockers

    straightTubeQZeroSurfaceText :
      String

    straightTubeQZeroSurfaceTextIsCanonical :
      straightTubeQZeroSurfaceText ≡ canonicalStraightTubeQZeroSurface

    diagonalPressureRouteSurfaceText :
      String

    diagonalPressureRouteSurfaceTextIsCanonical :
      diagonalPressureRouteSurfaceText ≡ canonicalDiagonalPressureRouteSurface

    curvedTubeNonzeroQSurfaceText :
      String

    curvedTubeNonzeroQSurfaceTextIsCanonical :
      curvedTubeNonzeroQSurfaceText ≡ canonicalCurvedTubeNonzeroQSurface

    curvedTubeSecondOrderSurface :
      String

    curvedTubeSecondOrderSurfaceIsCanonical :
      curvedTubeSecondOrderSurface ≡ canonicalCurvedTubeSecondOrderSurface

    nonPromoting :
      String

    nonPromotingIsCanonical :
      nonPromoting ≡ canonicalNonPromotingSurface

    straightTubeTheoremPromoted :
      Bool

    straightTubeTheoremPromotedIsFalse :
      straightTubeTheoremPromoted ≡ false

    curvedTubeTheoremPromoted :
      Bool

    curvedTubeTheoremPromotedIsFalse :
      curvedTubeTheoremPromoted ≡ false

    diagonalPressureRoutePromoted :
      Bool

    diagonalPressureRoutePromotedIsFalse :
      diagonalPressureRoutePromoted ≡ false

    curvedTubeSecondOrderSurfacePromoted :
      Bool

    curvedTubeSecondOrderSurfacePromotedIsFalse :
      curvedTubeSecondOrderSurfacePromoted ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    clayPromotionPromoted :
      Bool

    clayPromotionPromotedIsFalse :
      clayPromotionPromoted ≡ false

    promotionBits :
      List NSSingleTubePressureCaseExclusionPromotionBit

    promotionBitsAreEmpty :
      promotionBits ≡ []

    noPromotionPossibleHere :
      NSSingleTubePressureCaseExclusionPromotionBit →
      ⊥

    controlSummaryText :
      List String

    controlSummaryTextIsCanonical :
      controlSummaryText ≡ controlSummary

open NSSingleTubePressureCaseExclusionReceipt public

canonicalNSSingleTubePressureCaseExclusionReceipt :
  NSSingleTubePressureCaseExclusionReceipt
canonicalNSSingleTubePressureCaseExclusionReceipt =
  record
    { status =
        route1SingleTubePressureCaseRecordedFailClosed
    ; statusIsCanonical =
        refl
    ; branches =
        canonicalBranches
    ; branchesAreCanonical =
        refl
    ; assumptions =
        canonicalAssumptions
    ; assumptionsAreCanonical =
        refl
    ; stages =
        canonicalStages
    ; stagesAreCanonical =
        refl
    ; blockers =
        canonicalBlockers
    ; blockersAreCanonical =
        refl
    ; straightTubeQZeroSurfaceText =
        canonicalStraightTubeQZeroSurface
    ; straightTubeQZeroSurfaceTextIsCanonical =
        refl
    ; diagonalPressureRouteSurfaceText =
        canonicalDiagonalPressureRouteSurface
    ; diagonalPressureRouteSurfaceTextIsCanonical =
        refl
    ; curvedTubeNonzeroQSurfaceText =
        canonicalCurvedTubeNonzeroQSurface
    ; curvedTubeNonzeroQSurfaceTextIsCanonical =
        refl
    ; curvedTubeSecondOrderSurface =
        canonicalCurvedTubeSecondOrderSurface
    ; curvedTubeSecondOrderSurfaceIsCanonical =
        refl
    ; nonPromoting =
        canonicalNonPromotingSurface
    ; nonPromotingIsCanonical =
        refl
    ; straightTubeTheoremPromoted =
        false
    ; straightTubeTheoremPromotedIsFalse =
        refl
    ; curvedTubeTheoremPromoted =
        false
    ; curvedTubeTheoremPromotedIsFalse =
        refl
    ; diagonalPressureRoutePromoted =
        false
    ; diagonalPressureRoutePromotedIsFalse =
        refl
    ; curvedTubeSecondOrderSurfacePromoted =
        false
    ; curvedTubeSecondOrderSurfacePromotedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; clayPromotionPromoted =
        false
    ; clayPromotionPromotedIsFalse =
        refl
    ; promotionBits =
        []
    ; promotionBitsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        λ ()
    ; controlSummaryText =
        controlSummary
    ; controlSummaryTextIsCanonical =
        refl
    }
