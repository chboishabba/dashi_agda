module DASHI.Physics.Closure.NSA4ResidualPositiveTheoremLadderBoundary where

-- NS A4 residual-positive theorem ladder boundary.
--
-- This worker-3 module composes the four current A4/A6 surfaces:
--
--   NSA4UniformErrorBudgetCompositeBoundary
--   NSA4ResidualPositiveAfterErrorsBoundary
--   NSA4NoAngularCollapseTransferCompositeBoundary
--   NSA4ToA6TransferLadderBoundary
--
-- into one fail-closed theorem ladder:
--
--   uniform error budget
--     -> residual positivity after all A4 errors
--     -> no-angular-collapse/output-support transfer
--     -> A5 kappa-bias vanishing target
--     -> A6 pointwise-to-Abel / leakage target
--     -> A7 residual depletion / CKN target.
--
-- It is a complete boundary ledger, not a proof-promotion.  The typed
-- carrier records every dependency edge and all promotion guards remain
-- false.  It proves no A4 theorem, no A6 theorem, no CKN/BKM closure, no
-- Navier-Stokes Clay result, and no terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4UniformErrorBudgetCompositeBoundary
  as Uniform
import DASHI.Physics.Closure.NSA4ResidualPositiveAfterErrorsBoundary
  as Residual
import DASHI.Physics.Closure.NSA4NoAngularCollapseTransferCompositeBoundary
  as NoCollapse
import DASHI.Physics.Closure.NSA4ToA6TransferLadderBoundary
  as Transfer

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported boundary anchors.

uniformErrorBudgetCompositeBoundaryReference : String
uniformErrorBudgetCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA4UniformErrorBudgetCompositeBoundary"

residualPositiveAfterErrorsBoundaryReference : String
residualPositiveAfterErrorsBoundaryReference =
  "DASHI.Physics.Closure.NSA4ResidualPositiveAfterErrorsBoundary"

noAngularCollapseTransferCompositeBoundaryReference : String
noAngularCollapseTransferCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA4NoAngularCollapseTransferCompositeBoundary"

a4ToA6TransferLadderBoundaryReference : String
a4ToA6TransferLadderBoundaryReference =
  "DASHI.Physics.Closure.NSA4ToA6TransferLadderBoundary"

record ImportedResidualPositiveTheoremLadderSupport : Set where
  field
    uniformBudgetBoundary :
      Uniform.NSA4UniformErrorBudgetCompositeBoundary
    uniformBudgetBoundaryIsCanonical :
      uniformBudgetBoundary
        ≡ Uniform.canonicalNSA4UniformErrorBudgetCompositeBoundary
    residualPositiveBoundary :
      Residual.NSA4ResidualPositiveAfterErrorsBoundary
    residualPositiveBoundaryIsCanonical :
      residualPositiveBoundary
        ≡ Residual.canonicalNSA4ResidualPositiveAfterErrorsBoundary
    noCollapseBoundary :
      NoCollapse.NSA4NoAngularCollapseTransferCompositeBoundary
    noCollapseBoundaryIsCanonical :
      noCollapseBoundary
        ≡ NoCollapse.canonicalNSA4NoAngularCollapseTransferCompositeBoundary
    transferLadderBoundary :
      Transfer.NSA4ToA6TransferLadderBoundary
    transferLadderBoundaryIsCanonical :
      transferLadderBoundary
        ≡ Transfer.canonicalNSA4ToA6TransferLadderBoundary

    uniformTarget :
      Uniform.UniformA4ErrorBudgetCompositeTarget
    uniformTargetIsCanonical :
      uniformTarget ≡ Uniform.canonicalUniformA4ErrorBudgetCompositeTarget
    residualTarget :
      Residual.A4ResidualPositiveWitnessTarget
    residualTargetIsCanonical :
      residualTarget ≡ Residual.canonicalA4ResidualPositiveWitnessTarget
    noCollapseTarget :
      NoCollapse.NoAngularCollapseOutputGreatCircleSupportTransferTarget
    noCollapseTargetIsCanonical :
      noCollapseTarget
        ≡ NoCollapse.canonicalNoAngularCollapseOutputGreatCircleSupportTransferTarget
    transferRows :
      Transfer.List Transfer.NSA4ToA6TransferLadderRow
    transferRowsAreCanonical :
      transferRows ≡ Transfer.canonicalNSA4ToA6TransferLadderRows

    uniformBoundaryRecorded :
      Uniform.NSA4UniformErrorBudgetCompositeBoundaryRecorded ≡ true
    residualBoundaryRecorded :
      Residual.NSA4ResidualPositiveAfterErrorsBoundaryRecorded ≡ true
    noCollapseBoundaryRecorded :
      NoCollapse.NSA4NoAngularCollapseTransferCompositeBoundaryRecorded
        ≡ true
    transferLadderBoundaryRecorded :
      Transfer.transferLadderBoundaryRecorded ≡ true

    uniformResidualStillFalse :
      Uniform.uniformResidualPositivityProved ≡ false
    residualPositiveStillFalse :
      Residual.residualPositiveAfterErrorsProved ≡ false
    totalErrorDominationStillFalse :
      Residual.totalErrorDominatedByCEtaMarginProved ≡ false
    noCollapseTransferStillFalse :
      NoCollapse.A4NoAngularCollapseTransferTheoremProved ≡ false
    noCollapseOutputSupportStillFalse :
      NoCollapse.A4LeiRenTianOutputSupportTransferProved ≡ false
    transferA4StillFalse :
      Transfer.A4NoAngularCollapseTheoremProved ≡ false
    transferA5StillFalse :
      Transfer.A5KappaBiasVanishingProved ≡ false
    transferA6StillFalse :
      Transfer.A6LeakageIdentityProved ≡ false
    transferA7StillFalse :
      Transfer.A7ResidualDepletionProved ≡ false
    transferClayStillFalse :
      Transfer.NSClayPromoted ≡ false

canonicalImportedResidualPositiveTheoremLadderSupport :
  ImportedResidualPositiveTheoremLadderSupport
canonicalImportedResidualPositiveTheoremLadderSupport =
  record
    { uniformBudgetBoundary =
        Uniform.canonicalNSA4UniformErrorBudgetCompositeBoundary
    ; uniformBudgetBoundaryIsCanonical =
        refl
    ; residualPositiveBoundary =
        Residual.canonicalNSA4ResidualPositiveAfterErrorsBoundary
    ; residualPositiveBoundaryIsCanonical =
        refl
    ; noCollapseBoundary =
        NoCollapse.canonicalNSA4NoAngularCollapseTransferCompositeBoundary
    ; noCollapseBoundaryIsCanonical =
        refl
    ; transferLadderBoundary =
        Transfer.canonicalNSA4ToA6TransferLadderBoundary
    ; transferLadderBoundaryIsCanonical =
        refl
    ; uniformTarget =
        Uniform.canonicalUniformA4ErrorBudgetCompositeTarget
    ; uniformTargetIsCanonical =
        refl
    ; residualTarget =
        Residual.canonicalA4ResidualPositiveWitnessTarget
    ; residualTargetIsCanonical =
        refl
    ; noCollapseTarget =
        NoCollapse.canonicalNoAngularCollapseOutputGreatCircleSupportTransferTarget
    ; noCollapseTargetIsCanonical =
        refl
    ; transferRows =
        Transfer.canonicalNSA4ToA6TransferLadderRows
    ; transferRowsAreCanonical =
        refl
    ; uniformBoundaryRecorded =
        refl
    ; residualBoundaryRecorded =
        refl
    ; noCollapseBoundaryRecorded =
        refl
    ; transferLadderBoundaryRecorded =
        refl
    ; uniformResidualStillFalse =
        refl
    ; residualPositiveStillFalse =
        refl
    ; totalErrorDominationStillFalse =
        refl
    ; noCollapseTransferStillFalse =
        refl
    ; noCollapseOutputSupportStillFalse =
        refl
    ; transferA4StillFalse =
        refl
    ; transferA5StillFalse =
        refl
    ; transferA6StillFalse =
        refl
    ; transferA7StillFalse =
        refl
    ; transferClayStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Residual-positive theorem ladder.

data ResidualPositiveTheoremLadderRung : Set where
  rung-uniform-a4-error-budget :
    ResidualPositiveTheoremLadderRung
  rung-residual-positive-after-errors :
    ResidualPositiveTheoremLadderRung
  rung-output-support-no-collapse :
    ResidualPositiveTheoremLadderRung
  rung-a5-kappa-bias-vanishing :
    ResidualPositiveTheoremLadderRung
  rung-a6-pointwise-to-abel-leakage :
    ResidualPositiveTheoremLadderRung
  rung-a7-residual-depletion :
    ResidualPositiveTheoremLadderRung
  rung-ckn-bkm-closure :
    ResidualPositiveTheoremLadderRung

canonicalResidualPositiveTheoremLadderRungs :
  List ResidualPositiveTheoremLadderRung
canonicalResidualPositiveTheoremLadderRungs =
  rung-uniform-a4-error-budget
  ∷ rung-residual-positive-after-errors
  ∷ rung-output-support-no-collapse
  ∷ rung-a5-kappa-bias-vanishing
  ∷ rung-a6-pointwise-to-abel-leakage
  ∷ rung-a7-residual-depletion
  ∷ rung-ckn-bkm-closure
  ∷ []

residualPositiveTheoremLadderRungCount : Nat
residualPositiveTheoremLadderRungCount =
  listLength canonicalResidualPositiveTheoremLadderRungs

residualPositiveTheoremLadderRungCountIs7 :
  residualPositiveTheoremLadderRungCount ≡ 7
residualPositiveTheoremLadderRungCountIs7 =
  refl

data ResidualPositiveTheoremLadderEdge : Set where
  uniformBudgetFeedsResidualPositivity :
    ResidualPositiveTheoremLadderEdge
  residualPositivityFeedsNoAngularCollapse :
    ResidualPositiveTheoremLadderEdge
  noAngularCollapseFeedsA5BiasVanishing :
    ResidualPositiveTheoremLadderEdge
  a5BiasVanishingFeedsA6PointwiseToAbel :
    ResidualPositiveTheoremLadderEdge
  a6PointwiseToAbelFeedsLeakageIdentity :
    ResidualPositiveTheoremLadderEdge
  leakageIdentityFeedsResidualDepletion :
    ResidualPositiveTheoremLadderEdge
  residualDepletionFeedsCKNBKMClosureTarget :
    ResidualPositiveTheoremLadderEdge
  cknBkmClosureDoesNotPromoteClayHere :
    ResidualPositiveTheoremLadderEdge

canonicalResidualPositiveTheoremLadderEdges :
  List ResidualPositiveTheoremLadderEdge
canonicalResidualPositiveTheoremLadderEdges =
  uniformBudgetFeedsResidualPositivity
  ∷ residualPositivityFeedsNoAngularCollapse
  ∷ noAngularCollapseFeedsA5BiasVanishing
  ∷ a5BiasVanishingFeedsA6PointwiseToAbel
  ∷ a6PointwiseToAbelFeedsLeakageIdentity
  ∷ leakageIdentityFeedsResidualDepletion
  ∷ residualDepletionFeedsCKNBKMClosureTarget
  ∷ cknBkmClosureDoesNotPromoteClayHere
  ∷ []

residualPositiveTheoremLadderEdgeCount : Nat
residualPositiveTheoremLadderEdgeCount =
  listLength canonicalResidualPositiveTheoremLadderEdges

residualPositiveTheoremLadderEdgeCountIs8 :
  residualPositiveTheoremLadderEdgeCount ≡ 8
residualPositiveTheoremLadderEdgeCountIs8 =
  refl

data ResidualPositiveTheoremLadderBlocker : Set where
  blocker-uniform-error-budget-not-theorem :
    ResidualPositiveTheoremLadderBlocker
  blocker-residual-positive-margin-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-no-angular-collapse-transfer-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-a5-kappa-bias-vanishing-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-a6-pointwise-to-abel-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-a6-leakage-identity-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-a7-residual-depletion-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-ckn-bkm-closure-unproved :
    ResidualPositiveTheoremLadderBlocker
  blocker-clay-promotion-forbidden-here :
    ResidualPositiveTheoremLadderBlocker

canonicalResidualPositiveTheoremLadderBlockers :
  List ResidualPositiveTheoremLadderBlocker
canonicalResidualPositiveTheoremLadderBlockers =
  blocker-uniform-error-budget-not-theorem
  ∷ blocker-residual-positive-margin-unproved
  ∷ blocker-no-angular-collapse-transfer-unproved
  ∷ blocker-a5-kappa-bias-vanishing-unproved
  ∷ blocker-a6-pointwise-to-abel-unproved
  ∷ blocker-a6-leakage-identity-unproved
  ∷ blocker-a7-residual-depletion-unproved
  ∷ blocker-ckn-bkm-closure-unproved
  ∷ blocker-clay-promotion-forbidden-here
  ∷ []

residualPositiveTheoremLadderBlockerCount : Nat
residualPositiveTheoremLadderBlockerCount =
  listLength canonicalResidualPositiveTheoremLadderBlockers

residualPositiveTheoremLadderBlockerCountIs9 :
  residualPositiveTheoremLadderBlockerCount ≡ 9
residualPositiveTheoremLadderBlockerCountIs9 =
  refl

data ResidualPositiveTheoremLadderStatusRow : Set where
  importsFourRequiredBoundariesStatus :
    ResidualPositiveTheoremLadderStatusRow
  uniformBudgetTargetRecordedStatus :
    ResidualPositiveTheoremLadderStatusRow
  residualPositiveTargetRecordedStatus :
    ResidualPositiveTheoremLadderStatusRow
  noCollapseTransferTargetRecordedStatus :
    ResidualPositiveTheoremLadderStatusRow
  a4ToA6TransferRowsRecordedStatus :
    ResidualPositiveTheoremLadderStatusRow
  a6CknDependencyTargetRecordedStatus :
    ResidualPositiveTheoremLadderStatusRow
  theoremPromotionFlagsRemainFalseStatus :
    ResidualPositiveTheoremLadderStatusRow
  clayAndTerminalPromotionFalseStatus :
    ResidualPositiveTheoremLadderStatusRow

canonicalResidualPositiveTheoremLadderStatusRows :
  List ResidualPositiveTheoremLadderStatusRow
canonicalResidualPositiveTheoremLadderStatusRows =
  importsFourRequiredBoundariesStatus
  ∷ uniformBudgetTargetRecordedStatus
  ∷ residualPositiveTargetRecordedStatus
  ∷ noCollapseTransferTargetRecordedStatus
  ∷ a4ToA6TransferRowsRecordedStatus
  ∷ a6CknDependencyTargetRecordedStatus
  ∷ theoremPromotionFlagsRemainFalseStatus
  ∷ clayAndTerminalPromotionFalseStatus
  ∷ []

residualPositiveTheoremLadderStatusRowCount : Nat
residualPositiveTheoremLadderStatusRowCount =
  listLength canonicalResidualPositiveTheoremLadderStatusRows

residualPositiveTheoremLadderStatusRowCountIs8 :
  residualPositiveTheoremLadderStatusRowCount ≡ 8
residualPositiveTheoremLadderStatusRowCountIs8 =
  refl

record ResidualPositiveTheoremLadderRow : Set where
  field
    rung :
      ResidualPositiveTheoremLadderRung
    sourceBoundary :
      String
    targetName :
      String
    blocker :
      ResidualPositiveTheoremLadderBlocker
    recorded :
      Bool
    recordedIsTrue :
      recorded ≡ true
    promoted :
      Bool
    promotedIsFalse :
      promoted ≡ false

uniformBudgetRow : ResidualPositiveTheoremLadderRow
uniformBudgetRow =
  record
    { rung =
        rung-uniform-a4-error-budget
    ; sourceBoundary =
        uniformErrorBudgetCompositeBoundaryReference
    ; targetName =
        "uniform c-eta error budget after all A4 perturbation classes"
    ; blocker =
        blocker-uniform-error-budget-not-theorem
    ; recorded =
        Uniform.uniformA4SubtractionLedgerRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        Uniform.uniformA4ErrorBudgetTheoremProved
    ; promotedIsFalse =
        refl
    }

residualPositiveRow : ResidualPositiveTheoremLadderRow
residualPositiveRow =
  record
    { rung =
        rung-residual-positive-after-errors
    ; sourceBoundary =
        residualPositiveAfterErrorsBoundaryReference
    ; targetName =
        "c eta minus log, antipodal, low/null, and Bony errors remains positive"
    ; blocker =
        blocker-residual-positive-margin-unproved
    ; recorded =
        Residual.positivityWitnessTargetRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        Residual.residualPositiveAfterErrorsProved
    ; promotedIsFalse =
        refl
    }

noAngularCollapseRow : ResidualPositiveTheoremLadderRow
noAngularCollapseRow =
  record
    { rung =
        rung-output-support-no-collapse
    ; sourceBoundary =
        noAngularCollapseTransferCompositeBoundaryReference
    ; targetName =
        "A4 no-angular-collapse/output great-circle support transfer"
    ; blocker =
        blocker-no-angular-collapse-transfer-unproved
    ; recorded =
        NoCollapse.conditionalA4NoAngularCollapseTheoremTargetRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        NoCollapse.A4NoAngularCollapseTransferTheoremProved
    ; promotedIsFalse =
        refl
    }

a5KappaBiasRow : ResidualPositiveTheoremLadderRow
a5KappaBiasRow =
  record
    { rung =
        rung-a5-kappa-bias-vanishing
    ; sourceBoundary =
        a4ToA6TransferLadderBoundaryReference
    ; targetName =
        "A5 kappa-bias vanishing from output support plus transfer neutrality"
    ; blocker =
        blocker-a5-kappa-bias-vanishing-unproved
    ; recorded =
        Transfer.conditionalA5KappaBiasVanishingTargetRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        Transfer.A5KappaBiasVanishingProved
    ; promotedIsFalse =
        refl
    }

a6PointwiseToAbelRow : ResidualPositiveTheoremLadderRow
a6PointwiseToAbelRow =
  record
    { rung =
        rung-a6-pointwise-to-abel-leakage
    ; sourceBoundary =
        a4ToA6TransferLadderBoundaryReference
    ; targetName =
        "A6 pointwise-to-Abel and compensated leakage identity target"
    ; blocker =
        blocker-a6-pointwise-to-abel-unproved
    ; recorded =
        Transfer.conditionalA6LeakageIdentityTargetRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        Transfer.A6PointwiseToAbelProved
    ; promotedIsFalse =
        refl
    }

a7ResidualDepletionRow : ResidualPositiveTheoremLadderRow
a7ResidualDepletionRow =
  record
    { rung =
        rung-a7-residual-depletion
    ; sourceBoundary =
        a4ToA6TransferLadderBoundaryReference
    ; targetName =
        "A7 residual depletion feeding local defect monotonicity"
    ; blocker =
        blocker-a7-residual-depletion-unproved
    ; recorded =
        Transfer.conditionalA7ResidualDepletionTargetRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        Transfer.A7ResidualDepletionProved
    ; promotedIsFalse =
        refl
    }

cknBkmClosureRow : ResidualPositiveTheoremLadderRow
cknBkmClosureRow =
  record
    { rung =
        rung-ckn-bkm-closure
    ; sourceBoundary =
        a4ToA6TransferLadderBoundaryReference
    ; targetName =
        "CKN/BKM closure remains downstream of theorem-grade residual depletion"
    ; blocker =
        blocker-ckn-bkm-closure-unproved
    ; recorded =
        Transfer.conditionalA7ResidualDepletionTargetRecorded
    ; recordedIsTrue =
        refl
    ; promoted =
        Transfer.A7LocalDefectMonotonicityProved
    ; promotedIsFalse =
        refl
    }

canonicalResidualPositiveTheoremLadderRows :
  List ResidualPositiveTheoremLadderRow
canonicalResidualPositiveTheoremLadderRows =
  uniformBudgetRow
  ∷ residualPositiveRow
  ∷ noAngularCollapseRow
  ∷ a5KappaBiasRow
  ∷ a6PointwiseToAbelRow
  ∷ a7ResidualDepletionRow
  ∷ cknBkmClosureRow
  ∷ []

residualPositiveTheoremLadderRowCount : Nat
residualPositiveTheoremLadderRowCount =
  listLength canonicalResidualPositiveTheoremLadderRows

residualPositiveTheoremLadderRowCountIs7 :
  residualPositiveTheoremLadderRowCount ≡ 7
residualPositiveTheoremLadderRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Composed ladder target and fail-closed governance.

data ResidualPositiveFeedsA6CKNTarget : Set where
  residualPositivityFeedsFailClosedA6AndCKNLadder :
    ImportedResidualPositiveTheoremLadderSupport →
    Uniform.UniformA4ErrorBudgetCompositeTarget →
    Residual.A4ResidualPositiveWitnessTarget →
    NoCollapse.NoAngularCollapseOutputGreatCircleSupportTransferTarget →
    Transfer.NSA4ToA6TransferLadderBoundary →
    List ResidualPositiveTheoremLadderRow →
    ResidualPositiveFeedsA6CKNTarget

canonicalResidualPositiveFeedsA6CKNTarget :
  ResidualPositiveFeedsA6CKNTarget
canonicalResidualPositiveFeedsA6CKNTarget =
  residualPositivityFeedsFailClosedA6AndCKNLadder
    canonicalImportedResidualPositiveTheoremLadderSupport
    Uniform.canonicalUniformA4ErrorBudgetCompositeTarget
    Residual.canonicalA4ResidualPositiveWitnessTarget
    NoCollapse.canonicalNoAngularCollapseOutputGreatCircleSupportTransferTarget
    Transfer.canonicalNSA4ToA6TransferLadderBoundary
    canonicalResidualPositiveTheoremLadderRows

NSA4ResidualPositiveTheoremLadderBoundaryRecorded : Bool
NSA4ResidualPositiveTheoremLadderBoundaryRecorded =
  true

residualPositiveFeedsA6CKNTargetRecorded : Bool
residualPositiveFeedsA6CKNTargetRecorded =
  true

uniformBudgetPromotedHere : Bool
uniformBudgetPromotedHere =
  false

residualPositivePromotedHere : Bool
residualPositivePromotedHere =
  false

a4NoCollapsePromotedHere : Bool
a4NoCollapsePromotedHere =
  false

a5BiasVanishingPromotedHere : Bool
a5BiasVanishingPromotedHere =
  false

a6LeakagePromotedHere : Bool
a6LeakagePromotedHere =
  false

a7ResidualDepletionPromotedHere : Bool
a7ResidualDepletionPromotedHere =
  false

cknBkmClosurePromotedHere : Bool
cknBkmClosurePromotedHere =
  false

clayNavierStokesPromotedHere : Bool
clayNavierStokesPromotedHere =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data ResidualPositiveTheoremLadderPromotion : Set where

residualPositiveTheoremLadderPromotionImpossibleHere :
  ResidualPositiveTheoremLadderPromotion →
  ⊥
residualPositiveTheoremLadderPromotionImpossibleHere ()

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker-3 Closure boundary composing A4 residual positivity with the A4-to-A6/CKN transfer ladder."

requirementString : String
requirementString =
  "R: Compose uniform error budget, residual positivity after errors, no-angular-collapse transfer, and A4-to-A6 ladder into one theorem-ladder boundary without editing docs or Everything.agda."

codeArtifactString : String
codeArtifactString =
  "C: NSA4ResidualPositiveTheoremLadderBoundary imports the four requested surfaces and exports typed support, rungs, edges, blockers, rows, target carrier, and no-promotion guards."

stateString : String
stateString =
  "S: The ladder target is recorded and all four child surfaces are consumed canonically; residual positivity, A4, A5, A6, A7, CKN/BKM, Clay, and terminal promotions remain false."

latticeString : String
latticeString =
  "L: uniform budget -> residual positivity -> no-collapse output support -> A5 bias vanishing -> A6 Abel/leakage -> A7 depletion -> CKN/BKM target; Clay remains outside this promotion lattice."

proposalString : String
proposalString =
  "P: Use this boundary as the canonical handoff from the A4 residual margin to A6/CKN, then discharge theorem blockers in ladder order before any promotion."

governanceString : String
governanceString =
  "G: Fail closed: a recorded ladder and target carrier do not upgrade any imported boundary receipt into a theorem or a Clay authority claim."

gapString : String
gapString =
  "F: Missing theorem-grade uniform budget, residual positive margin, A4 no-collapse transfer, A5 PDE bias vanishing, A6 leakage identity, A7 depletion, CKN/BKM closure, and Clay authority."

------------------------------------------------------------------------
-- Canonical receipt.

record NSA4ResidualPositiveTheoremLadderBoundary : Set where
  field
    O :
      String
    OIsCanonical :
      O ≡ organizationString
    R :
      String
    RIsCanonical :
      R ≡ requirementString
    C :
      String
    CIsCanonical :
      C ≡ codeArtifactString
    S :
      String
    SIsCanonical :
      S ≡ stateString
    L :
      String
    LIsCanonical :
      L ≡ latticeString
    P :
      String
    PIsCanonical :
      P ≡ proposalString
    G :
      String
    GIsCanonical :
      G ≡ governanceString
    F :
      String
    FIsCanonical :
      F ≡ gapString

    importedSupport :
      ImportedResidualPositiveTheoremLadderSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedResidualPositiveTheoremLadderSupport
    rungs :
      List ResidualPositiveTheoremLadderRung
    rungsAreCanonical :
      rungs ≡ canonicalResidualPositiveTheoremLadderRungs
    rungCountProof :
      residualPositiveTheoremLadderRungCount ≡ 7
    edges :
      List ResidualPositiveTheoremLadderEdge
    edgesAreCanonical :
      edges ≡ canonicalResidualPositiveTheoremLadderEdges
    edgeCountProof :
      residualPositiveTheoremLadderEdgeCount ≡ 8
    rows :
      List ResidualPositiveTheoremLadderRow
    rowsAreCanonical :
      rows ≡ canonicalResidualPositiveTheoremLadderRows
    rowCountProof :
      residualPositiveTheoremLadderRowCount ≡ 7
    blockers :
      List ResidualPositiveTheoremLadderBlocker
    blockersAreCanonical :
      blockers ≡ canonicalResidualPositiveTheoremLadderBlockers
    blockerCountProof :
      residualPositiveTheoremLadderBlockerCount ≡ 9
    statusRows :
      List ResidualPositiveTheoremLadderStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalResidualPositiveTheoremLadderStatusRows
    statusRowCountProof :
      residualPositiveTheoremLadderStatusRowCount ≡ 8
    target :
      ResidualPositiveFeedsA6CKNTarget
    targetIsCanonical :
      target ≡ canonicalResidualPositiveFeedsA6CKNTarget

    boundaryRecordedTrue :
      NSA4ResidualPositiveTheoremLadderBoundaryRecorded ≡ true
    targetRecordedTrue :
      residualPositiveFeedsA6CKNTargetRecorded ≡ true

    importedUniformResidualStillFalse :
      Uniform.uniformResidualPositivityProved ≡ false
    importedUniformBudgetStillFalse :
      Uniform.uniformA4ErrorBudgetTheoremProved ≡ false
    importedResidualStillFalse :
      Residual.residualPositiveAfterErrorsProved ≡ false
    importedTotalErrorStillFalse :
      Residual.totalErrorDominatedByCEtaMarginProved ≡ false
    importedNoCollapseStillFalse :
      NoCollapse.A4NoAngularCollapseTransferTheoremProved ≡ false
    importedNoCollapseOutputSupportStillFalse :
      NoCollapse.A4LeiRenTianOutputSupportTransferProved ≡ false
    importedTransferA5StillFalse :
      Transfer.A5KappaBiasVanishingProved ≡ false
    importedTransferA6StillFalse :
      Transfer.A6LeakageIdentityProved ≡ false
    importedTransferA7StillFalse :
      Transfer.A7ResidualDepletionProved ≡ false
    importedTransferClayStillFalse :
      Transfer.NSClayPromoted ≡ false

    uniformBudgetPromotedHereFalse :
      uniformBudgetPromotedHere ≡ false
    residualPositivePromotedHereFalse :
      residualPositivePromotedHere ≡ false
    a4NoCollapsePromotedHereFalse :
      a4NoCollapsePromotedHere ≡ false
    a5BiasVanishingPromotedHereFalse :
      a5BiasVanishingPromotedHere ≡ false
    a6LeakagePromotedHereFalse :
      a6LeakagePromotedHere ≡ false
    a7ResidualDepletionPromotedHereFalse :
      a7ResidualDepletionPromotedHere ≡ false
    cknBkmClosurePromotedHereFalse :
      cknBkmClosurePromotedHere ≡ false
    clayNavierStokesPromotedHereFalse :
      clayNavierStokesPromotedHere ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

canonicalNSA4ResidualPositiveTheoremLadderBoundary :
  NSA4ResidualPositiveTheoremLadderBoundary
canonicalNSA4ResidualPositiveTheoremLadderBoundary =
  record
    { O =
        organizationString
    ; OIsCanonical =
        refl
    ; R =
        requirementString
    ; RIsCanonical =
        refl
    ; C =
        codeArtifactString
    ; CIsCanonical =
        refl
    ; S =
        stateString
    ; SIsCanonical =
        refl
    ; L =
        latticeString
    ; LIsCanonical =
        refl
    ; P =
        proposalString
    ; PIsCanonical =
        refl
    ; G =
        governanceString
    ; GIsCanonical =
        refl
    ; F =
        gapString
    ; FIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedResidualPositiveTheoremLadderSupport
    ; importedSupportIsCanonical =
        refl
    ; rungs =
        canonicalResidualPositiveTheoremLadderRungs
    ; rungsAreCanonical =
        refl
    ; rungCountProof =
        refl
    ; edges =
        canonicalResidualPositiveTheoremLadderEdges
    ; edgesAreCanonical =
        refl
    ; edgeCountProof =
        refl
    ; rows =
        canonicalResidualPositiveTheoremLadderRows
    ; rowsAreCanonical =
        refl
    ; rowCountProof =
        refl
    ; blockers =
        canonicalResidualPositiveTheoremLadderBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountProof =
        refl
    ; statusRows =
        canonicalResidualPositiveTheoremLadderStatusRows
    ; statusRowsAreCanonical =
        refl
    ; statusRowCountProof =
        refl
    ; target =
        canonicalResidualPositiveFeedsA6CKNTarget
    ; targetIsCanonical =
        refl
    ; boundaryRecordedTrue =
        refl
    ; targetRecordedTrue =
        refl
    ; importedUniformResidualStillFalse =
        refl
    ; importedUniformBudgetStillFalse =
        refl
    ; importedResidualStillFalse =
        refl
    ; importedTotalErrorStillFalse =
        refl
    ; importedNoCollapseStillFalse =
        refl
    ; importedNoCollapseOutputSupportStillFalse =
        refl
    ; importedTransferA5StillFalse =
        refl
    ; importedTransferA6StillFalse =
        refl
    ; importedTransferA7StillFalse =
        refl
    ; importedTransferClayStillFalse =
        refl
    ; uniformBudgetPromotedHereFalse =
        refl
    ; residualPositivePromotedHereFalse =
        refl
    ; a4NoCollapsePromotedHereFalse =
        refl
    ; a5BiasVanishingPromotedHereFalse =
        refl
    ; a6LeakagePromotedHereFalse =
        refl
    ; a7ResidualDepletionPromotedHereFalse =
        refl
    ; cknBkmClosurePromotedHereFalse =
        refl
    ; clayNavierStokesPromotedHereFalse =
        refl
    ; terminalPromotionFalse =
        refl
    }

------------------------------------------------------------------------
-- External fail-closed checks.

keepsUniformBudgetFalse :
  uniformBudgetPromotedHere ≡ false
keepsUniformBudgetFalse =
  refl

keepsResidualPositiveFalse :
  residualPositivePromotedHere ≡ false
keepsResidualPositiveFalse =
  refl

keepsA4NoCollapseFalse :
  a4NoCollapsePromotedHere ≡ false
keepsA4NoCollapseFalse =
  refl

keepsA5BiasVanishingFalse :
  a5BiasVanishingPromotedHere ≡ false
keepsA5BiasVanishingFalse =
  refl

keepsA6LeakageFalse :
  a6LeakagePromotedHere ≡ false
keepsA6LeakageFalse =
  refl

keepsA7ResidualDepletionFalse :
  a7ResidualDepletionPromotedHere ≡ false
keepsA7ResidualDepletionFalse =
  refl

keepsCKNBKMClosureFalse :
  cknBkmClosurePromotedHere ≡ false
keepsCKNBKMClosureFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromotedHere ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl
