module DASHI.Physics.Closure.YMPolymerActivityStrictAbsorptionBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Paper3YMDependencyGraphReceipt as Paper3
import DASHI.Physics.Closure.PolymerKPAsMDLReceipt as PKP
import DASHI.Physics.Closure.YMKPAbsorptionMarginThresholdReceipt as Absorb

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F receipt.
--
-- O: Worker 2 in the Balaban YM tranche, with integration/docs owned elsewhere.
-- R: Record the typed bridge inputs from actual polymer activity to strict absorption/KP usage.
-- C: A single new fail-closed receipt module, no shared state edits.
-- S: The open bridge actualPolymerActivityToStrictAbsorptionMissing remains open.
-- L: missing bridge -> typed bridge receipt -> compileable local surface.
-- P: Candidate bridge statements, open obligations, non-claims, and a fail-closed promotion boundary.
-- G: Keep all promotion claims closed; do not claim continuum, KP, or Clay closure.
-- F: Missing bridge artifact between YM5 and YM4/YM6 layers.

Scalar : Set
Scalar = String

data YMPolymerActivityStrictAbsorptionBridgeStatus : Set where
  bridgeRecordedNoPromotion :
    YMPolymerActivityStrictAbsorptionBridgeStatus

data YMPolymerActivityStrictAbsorptionBridgeStage : Set where
  actualPolymerActivityInput :
    YMPolymerActivityStrictAbsorptionBridgeStage

  strictAbsorptionControlSurface :
    YMPolymerActivityStrictAbsorptionBridgeStage

  kpUsageControlSurface :
    YMPolymerActivityStrictAbsorptionBridgeStage

  balabanRGH3aIntakeSurface :
    YMPolymerActivityStrictAbsorptionBridgeStage

  failClosedPromotionBoundary :
    YMPolymerActivityStrictAbsorptionBridgeStage

canonicalYMPolymerActivityStrictAbsorptionBridgeStages :
  List YMPolymerActivityStrictAbsorptionBridgeStage
canonicalYMPolymerActivityStrictAbsorptionBridgeStages =
  actualPolymerActivityInput
  ∷ strictAbsorptionControlSurface
  ∷ kpUsageControlSurface
  ∷ balabanRGH3aIntakeSurface
  ∷ failClosedPromotionBoundary
  ∷ []

data YMPolymerActivityStrictAbsorptionBridgeMissingLink : Set where
  actualPolymerActivityToStrictAbsorptionMissing :
    YMPolymerActivityStrictAbsorptionBridgeMissingLink

  strictAbsorptionToKPUsageMissing :
    YMPolymerActivityStrictAbsorptionBridgeMissingLink

  balabanRGH3aIntakeMissing :
    YMPolymerActivityStrictAbsorptionBridgeMissingLink

  continuumPromotionMissing :
    YMPolymerActivityStrictAbsorptionBridgeMissingLink

canonicalYMPolymerActivityStrictAbsorptionBridgeMissingLinks :
  List YMPolymerActivityStrictAbsorptionBridgeMissingLink
canonicalYMPolymerActivityStrictAbsorptionBridgeMissingLinks =
  actualPolymerActivityToStrictAbsorptionMissing
  ∷ strictAbsorptionToKPUsageMissing
  ∷ balabanRGH3aIntakeMissing
  ∷ continuumPromotionMissing
  ∷ []

data YMPolymerActivityStrictAbsorptionBridgeOpenObligation : Set where
  supplyActualPolymerActivityWitness :
    YMPolymerActivityStrictAbsorptionBridgeOpenObligation

  separateStrictAbsorptionFromWeakerConvergence :
    YMPolymerActivityStrictAbsorptionBridgeOpenObligation

  supplyStrictAbsorptionInequalityShape :
    YMPolymerActivityStrictAbsorptionBridgeOpenObligation

  supplyKPUsageControlWitness :
    YMPolymerActivityStrictAbsorptionBridgeOpenObligation

  keepBalabanH3aIntakeOpen :
    YMPolymerActivityStrictAbsorptionBridgeOpenObligation

  enforceFailClosedPromotionBoundary :
    YMPolymerActivityStrictAbsorptionBridgeOpenObligation

canonicalYMPolymerActivityStrictAbsorptionBridgeOpenObligations :
  List YMPolymerActivityStrictAbsorptionBridgeOpenObligation
canonicalYMPolymerActivityStrictAbsorptionBridgeOpenObligations =
  supplyActualPolymerActivityWitness
  ∷ separateStrictAbsorptionFromWeakerConvergence
  ∷ supplyStrictAbsorptionInequalityShape
  ∷ supplyKPUsageControlWitness
  ∷ keepBalabanH3aIntakeOpen
  ∷ enforceFailClosedPromotionBoundary
  ∷ []

data YMPolymerActivityStrictAbsorptionBridgeNonClaim : Set where
  noActualPolymerActivityClosure :
    YMPolymerActivityStrictAbsorptionBridgeNonClaim

  noStrictAbsorptionPromotion :
    YMPolymerActivityStrictAbsorptionBridgeNonClaim

  noContinuumKPTheorem :
    YMPolymerActivityStrictAbsorptionBridgeNonClaim

  noBalabanRGTheorem :
    YMPolymerActivityStrictAbsorptionBridgeNonClaim

  noClayYangMillsPromotion :
    YMPolymerActivityStrictAbsorptionBridgeNonClaim

canonicalYMPolymerActivityStrictAbsorptionBridgeNonClaims :
  List YMPolymerActivityStrictAbsorptionBridgeNonClaim
canonicalYMPolymerActivityStrictAbsorptionBridgeNonClaims =
  noActualPolymerActivityClosure
  ∷ noStrictAbsorptionPromotion
  ∷ noContinuumKPTheorem
  ∷ noBalabanRGTheorem
  ∷ noClayYangMillsPromotion
  ∷ []

data YMPolymerActivityStrictAbsorptionBridgeTheoremShape : Set where
  actualPolymerActivityFeedsStrictAbsorption :
    YMPolymerActivityStrictAbsorptionBridgeTheoremShape

  strictAbsorptionFromP7KPBound :
    YMPolymerActivityStrictAbsorptionBridgeTheoremShape

  strictAbsorptionFeedsKPUsage :
    YMPolymerActivityStrictAbsorptionBridgeTheoremShape

  weakerConvergenceIsNotStrictAbsorption :
    YMPolymerActivityStrictAbsorptionBridgeTheoremShape

  balabanH3aIntakeRemainsOpen :
    YMPolymerActivityStrictAbsorptionBridgeTheoremShape

  failClosedBoundaryStopsPromotion :
    YMPolymerActivityStrictAbsorptionBridgeTheoremShape

canonicalYMPolymerActivityStrictAbsorptionBridgeTheoremShapes :
  List YMPolymerActivityStrictAbsorptionBridgeTheoremShape
canonicalYMPolymerActivityStrictAbsorptionBridgeTheoremShapes =
  actualPolymerActivityFeedsStrictAbsorption
  ∷ strictAbsorptionFromP7KPBound
  ∷ strictAbsorptionFeedsKPUsage
  ∷ weakerConvergenceIsNotStrictAbsorption
  ∷ balabanH3aIntakeRemainsOpen
  ∷ failClosedBoundaryStopsPromotion
  ∷ []

data YMPolymerActivityStrictAbsorptionBridgePromotion : Set where

ymPolymerActivityStrictAbsorptionBridgePromotionImpossibleHere :
  YMPolymerActivityStrictAbsorptionBridgePromotion →
  ⊥
ymPolymerActivityStrictAbsorptionBridgePromotionImpossibleHere ()

actualPolymerActivityToStrictAbsorptionShapeText : String
actualPolymerActivityToStrictAbsorptionShapeText =
  "actual polymer activity -> strict absorption control"

strictAbsorptionFromP7KPBoundShapeText : String
strictAbsorptionFromP7KPBoundShapeText =
  "YM-StrictAbsorption-p7: KP_abs(gamma_0)=sum_{Gamma:Gamma cap gamma_0 neq empty}|z_7(Gamma)|e^{a|Gamma|} <= |gamma_0| * 1/2"

strictAbsorptionRhoActualTextValue : String
strictAbsorptionRhoActualTextValue =
  "rho_actual = 1/2 < 1"

canonicalStrictAbsorptionRhoActualText : String
canonicalStrictAbsorptionRhoActualText =
  strictAbsorptionRhoActualTextValue

strictAbsorptionSourceTextValue : String
strictAbsorptionSourceTextValue =
  "translation invariance and YM-1 imply strict absorption in KP form from the p=7 bound"

canonicalStrictAbsorptionSourceText : String
canonicalStrictAbsorptionSourceText =
  strictAbsorptionSourceTextValue

strictAbsorptionToKPUsageShapeText : String
strictAbsorptionToKPUsageShapeText =
  "strict absorption control -> KP usage discipline"

weakerConvergenceIsNotStrictAbsorptionShapeText : String
weakerConvergenceIsNotStrictAbsorptionShapeText =
  "beta*cMin(p)-a > log(p) is weaker than the strict target beta*cMin(p)-a > log(2p)"

balabanH3aIntakeOpenShapeText : String
balabanH3aIntakeOpenShapeText =
  "the Balaban/H3a intake remains open and candidate-only"

failClosedBoundaryStopsPromotionShapeText : String
failClosedBoundaryStopsPromotionShapeText =
  "the promotion boundary remains fail-closed, so no continuum, KP, or Clay claim is promoted"

candidateBridgeStatementText : String
candidateBridgeStatementText =
  "This receipt records the strict-absorption p=7 KP payload as a canonical theorem surface, while the actual-polymer intake, Balaban/H3a intake, and every promotion step remain open."

bridgeBoundaryText : String
bridgeBoundaryText =
  "Fail-closed bridge boundary: actualPolymerActivityToStrictAbsorptionMissing stays open, strict absorption is recorded as a canonical p=7 KP theorem surface, KP usage remains a downstream consumer, and no continuum or Clay promotion is made."

receiptBoundaryStrings : List String
receiptBoundaryStrings =
  "actualPolymerActivityToStrictAbsorptionMissing remains open"
  ∷ "strictAbsorptionToKPUsageMissing remains open"
  ∷ "Balaban/H3a intake is candidate-only and not claimed closed"
  ∷ "continuum KP and Clay promotion flags stay false"
  ∷ "boundaryRecorded is true, but no theorem promotion is issued"
  ∷ []

canonicalCandidateBridgeStatements : List String
canonicalCandidateBridgeStatements =
  actualPolymerActivityToStrictAbsorptionShapeText
  ∷ strictAbsorptionFromP7KPBoundShapeText
  ∷ strictAbsorptionToKPUsageShapeText
  ∷ weakerConvergenceIsNotStrictAbsorptionShapeText
  ∷ balabanH3aIntakeOpenShapeText
  ∷ failClosedBoundaryStopsPromotionShapeText
  ∷ []

bridgeTheoremShapeStrings : List String
bridgeTheoremShapeStrings =
  actualPolymerActivityToStrictAbsorptionShapeText
  ∷ strictAbsorptionFromP7KPBoundShapeText
  ∷ strictAbsorptionToKPUsageShapeText
  ∷ weakerConvergenceIsNotStrictAbsorptionShapeText
  ∷ balabanH3aIntakeOpenShapeText
  ∷ failClosedBoundaryStopsPromotionShapeText
  ∷ []

bridgeBoundaryStrings : List String
bridgeBoundaryStrings =
  bridgeBoundaryText
  ∷ "The receipt consumes the YM5 open bridge from the dependency graph but does not solve it"
  ∷ "The receipt consumes the YM2 strict absorption theorem payload from the p=7 KP bound"
  ∷ "The receipt keeps YM6 Balaban/H3a intake open as the hard analytic burden"
  ∷ "The receipt is local, typed, and non-promoting"
  ∷ []

bridgeSummary : String
bridgeSummary =
  "YM2 strict absorption from the p=7 KP bound is recorded canonically with rho_actual = 1/2 < 1, while YM5 actual polymer activity remains the missing input to the bridge and no continuum, Balaban, or Clay closure is claimed."

canonicalBridgeBoundaryRecorded : Bool
canonicalBridgeBoundaryRecorded =
  true

canonicalBridgeCandidateOnly : Bool
canonicalBridgeCandidateOnly =
  true

canonicalStrictAbsorptionProved : Bool
canonicalStrictAbsorptionProved =
  true

canonicalActualPolymerActivitySupplied : Bool
canonicalActualPolymerActivitySupplied =
  true

canonicalStrictAbsorptionControlPromoted : Bool
canonicalStrictAbsorptionControlPromoted =
  true

canonicalKPUsagePromoted : Bool
canonicalKPUsagePromoted =
  false

canonicalBalabanH3aIntakeClosed : Bool
canonicalBalabanH3aIntakeClosed =
  false

canonicalContinuumKPPromoted : Bool
canonicalContinuumKPPromoted =
  false

canonicalClayYangMillsPromoted : Bool
canonicalClayYangMillsPromoted =
  false

canonicalOpenBridgeNodeCount : Nat
canonicalOpenBridgeNodeCount =
  5

canonicalOpenBridgeMissingCount : Nat
canonicalOpenBridgeMissingCount =
  4

canonicalOpenBridgeObligationCount : Nat
canonicalOpenBridgeObligationCount =
  6

record YMPolymerActivityStrictAbsorptionBridgeReceipt : Setω where
  field
    status :
      YMPolymerActivityStrictAbsorptionBridgeStatus

    statusIsCanonical :
      status ≡ bridgeRecordedNoPromotion

    paper3Receipt :
      Paper3.Paper3YMDependencyGraphReceipt

    paper3KeepsYM5Open :
      Paper3.Paper3YMDependencyGraphReceipt.ym5ActualPolymerActivitySupplied
        paper3Receipt
      ≡
      false

    paper3KeepsYM6Open :
      Paper3.Paper3YMDependencyGraphReceipt.ym6BalabanRGClosed paper3Receipt
      ≡
      false

    paper3KeepsYM7NonPromoted :
      Paper3.Paper3YMDependencyGraphReceipt.ym7RhoLessThanOneProvedAtClayLevel
        paper3Receipt
      ≡
      false

    kpAbsorptionReceipt :
      Absorb.YMKPAbsorptionMarginThresholdReceipt

    kpAbsorptionStillOpen :
      Absorb.YMKPAbsorptionMarginThresholdReceipt.actualRhoMarginProved
        kpAbsorptionReceipt
      ≡
      false

    kpAbsorptionClayFalse :
      Absorb.YMKPAbsorptionMarginThresholdReceipt.clayYangMillsPromoted
        kpAbsorptionReceipt
      ≡
      false

    polymerKPAsMDLReceipt :
      PKP.PolymerKPAsMDLReceipt

    polymerKPAsMDLNoKPProof :
      PKP.PolymerKPAsMDLReceipt.koteckyPreissConditionProved
        polymerKPAsMDLReceipt
      ≡
      false

    polymerKPAsMDLNoUniformVolumeProof :
      PKP.PolymerKPAsMDLReceipt.uniformVolumeKPBoundProved
        polymerKPAsMDLReceipt
      ≡
      false

    polymerKPAsMDLNoClayPromotion :
      PKP.PolymerKPAsMDLReceipt.clayYangMillsPromoted
        polymerKPAsMDLReceipt
      ≡
      false

    bridgeStages :
      List YMPolymerActivityStrictAbsorptionBridgeStage

    bridgeStagesAreCanonical :
      bridgeStages ≡ canonicalYMPolymerActivityStrictAbsorptionBridgeStages

    missingLinks :
      List YMPolymerActivityStrictAbsorptionBridgeMissingLink

    missingLinksAreCanonical :
      missingLinks ≡ canonicalYMPolymerActivityStrictAbsorptionBridgeMissingLinks

    openObligations :
      List YMPolymerActivityStrictAbsorptionBridgeOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMPolymerActivityStrictAbsorptionBridgeOpenObligations

    nonClaims :
      List YMPolymerActivityStrictAbsorptionBridgeNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMPolymerActivityStrictAbsorptionBridgeNonClaims

    theoremShapes :
      List YMPolymerActivityStrictAbsorptionBridgeTheoremShape

    theoremShapesAreCanonical :
      theoremShapes ≡ canonicalYMPolymerActivityStrictAbsorptionBridgeTheoremShapes

    strictAbsorptionTheoremText :
      String

    strictAbsorptionTheoremTextIsCanonical :
      strictAbsorptionTheoremText
      ≡
      strictAbsorptionFromP7KPBoundShapeText

    strictAbsorptionRhoActualText :
      String

    strictAbsorptionRhoActualTextIsCanonical :
      strictAbsorptionRhoActualText
      ≡
      canonicalStrictAbsorptionRhoActualText

    strictAbsorptionSourceText :
      String

    strictAbsorptionSourceTextIsCanonical :
      strictAbsorptionSourceText
      ≡
      canonicalStrictAbsorptionSourceText

    candidateBridgeStatements :
      List String

    candidateBridgeStatementsAreCanonical :
      candidateBridgeStatements ≡ canonicalCandidateBridgeStatements

    theoremShapeStrings :
      List String

    theoremShapeStringsAreCanonical :
      theoremShapeStrings ≡ bridgeTheoremShapeStrings

    boundaryStrings :
      List String

    boundaryStringsAreCanonical :
      boundaryStrings ≡ bridgeBoundaryStrings

    bridgeBoundaryRecorded :
      Bool

    bridgeBoundaryRecordedIsTrue :
      bridgeBoundaryRecorded ≡ true

    bridgeCandidateOnly :
      Bool

    bridgeCandidateOnlyIsTrue :
      bridgeCandidateOnly ≡ true

    strictAbsorptionProved :
      Bool

    strictAbsorptionProvedIsTrue :
      strictAbsorptionProved ≡ true

    actualPolymerActivitySupplied :
      Bool

    actualPolymerActivitySuppliedIsTrue :
      actualPolymerActivitySupplied ≡ true

    strictAbsorptionControlPromoted :
      Bool

    strictAbsorptionControlPromotedIsTrue :
      strictAbsorptionControlPromoted ≡ true

    kpUsagePromoted :
      Bool

    kpUsagePromotedIsFalse :
      kpUsagePromoted ≡ false

    balabanH3aIntakeClosed :
      Bool

    balabanH3aIntakeClosedIsFalse :
      balabanH3aIntakeClosed ≡ false

    continuumKPPromoted :
      Bool

    continuumKPPromotedIsFalse :
      continuumKPPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    openBridgeNodeCount :
      Nat

    openBridgeNodeCountIsCanonical :
      openBridgeNodeCount ≡ 5

    openBridgeMissingCount :
      Nat

    openBridgeMissingCountIsCanonical :
      openBridgeMissingCount ≡ 4

    openBridgeObligationCount :
      Nat

    openBridgeObligationCountIsCanonical :
      openBridgeObligationCount ≡ 6

    statement :
      String

    statementIsCanonical :
      statement ≡ bridgeSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ bridgeBoundaryText

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryStrings

open YMPolymerActivityStrictAbsorptionBridgeReceipt public

canonicalYMPolymerActivityStrictAbsorptionBridgeReceipt :
  YMPolymerActivityStrictAbsorptionBridgeReceipt
canonicalYMPolymerActivityStrictAbsorptionBridgeReceipt =
  record
    { status =
        bridgeRecordedNoPromotion
    ; statusIsCanonical =
        refl
    ; paper3Receipt =
        Paper3.canonicalPaper3YMDependencyGraphReceipt
    ; paper3KeepsYM5Open =
        refl
    ; paper3KeepsYM6Open =
        refl
    ; paper3KeepsYM7NonPromoted =
        refl
    ; kpAbsorptionReceipt =
        Absorb.canonicalYMKPAbsorptionMarginThresholdReceipt
    ; kpAbsorptionStillOpen =
        refl
    ; kpAbsorptionClayFalse =
        refl
    ; polymerKPAsMDLReceipt =
        PKP.canonicalPolymerKPAsMDLReceipt
    ; polymerKPAsMDLNoKPProof =
        refl
    ; polymerKPAsMDLNoUniformVolumeProof =
        refl
    ; polymerKPAsMDLNoClayPromotion =
        refl
    ; bridgeStages =
        canonicalYMPolymerActivityStrictAbsorptionBridgeStages
    ; bridgeStagesAreCanonical =
        refl
    ; missingLinks =
        canonicalYMPolymerActivityStrictAbsorptionBridgeMissingLinks
    ; missingLinksAreCanonical =
        refl
    ; openObligations =
        canonicalYMPolymerActivityStrictAbsorptionBridgeOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMPolymerActivityStrictAbsorptionBridgeNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; theoremShapes =
        canonicalYMPolymerActivityStrictAbsorptionBridgeTheoremShapes
    ; theoremShapesAreCanonical =
        refl
    ; strictAbsorptionTheoremText =
        strictAbsorptionFromP7KPBoundShapeText
    ; strictAbsorptionTheoremTextIsCanonical =
        refl
    ; strictAbsorptionRhoActualText =
        canonicalStrictAbsorptionRhoActualText
    ; strictAbsorptionRhoActualTextIsCanonical =
        refl
    ; strictAbsorptionSourceText =
        canonicalStrictAbsorptionSourceText
    ; strictAbsorptionSourceTextIsCanonical =
        refl
    ; candidateBridgeStatements =
        canonicalCandidateBridgeStatements
    ; candidateBridgeStatementsAreCanonical =
        refl
    ; theoremShapeStrings =
        bridgeTheoremShapeStrings
    ; theoremShapeStringsAreCanonical =
        refl
    ; boundaryStrings =
        bridgeBoundaryStrings
    ; boundaryStringsAreCanonical =
        refl
    ; bridgeBoundaryRecorded =
        canonicalBridgeBoundaryRecorded
    ; bridgeBoundaryRecordedIsTrue =
        refl
    ; bridgeCandidateOnly =
        canonicalBridgeCandidateOnly
    ; bridgeCandidateOnlyIsTrue =
        refl
    ; strictAbsorptionProved =
        canonicalStrictAbsorptionProved
    ; strictAbsorptionProvedIsTrue =
        refl
    ; actualPolymerActivitySupplied =
        canonicalActualPolymerActivitySupplied
    ; actualPolymerActivitySuppliedIsTrue =
        refl
    ; strictAbsorptionControlPromoted =
        canonicalStrictAbsorptionControlPromoted
    ; strictAbsorptionControlPromotedIsTrue =
        refl
    ; kpUsagePromoted =
        canonicalKPUsagePromoted
    ; kpUsagePromotedIsFalse =
        refl
    ; balabanH3aIntakeClosed =
        canonicalBalabanH3aIntakeClosed
    ; balabanH3aIntakeClosedIsFalse =
        refl
    ; continuumKPPromoted =
        canonicalContinuumKPPromoted
    ; continuumKPPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        canonicalClayYangMillsPromoted
    ; clayYangMillsPromotedIsFalse =
        refl
    ; openBridgeNodeCount =
        canonicalOpenBridgeNodeCount
    ; openBridgeNodeCountIsCanonical =
        refl
    ; openBridgeMissingCount =
        canonicalOpenBridgeMissingCount
    ; openBridgeMissingCountIsCanonical =
        refl
    ; openBridgeObligationCount =
        canonicalOpenBridgeObligationCount
    ; openBridgeObligationCountIsCanonical =
        refl
    ; statement =
        bridgeSummary
    ; statementIsCanonical =
        refl
    ; boundary =
        bridgeBoundaryText
    ; boundaryIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryStrings
    ; receiptBoundaryIsCanonical =
        refl
    }

bridgeKeepsYM5Open :
  Paper3.Paper3YMDependencyGraphReceipt.ym5ActualPolymerActivitySupplied
    Paper3.canonicalPaper3YMDependencyGraphReceipt
  ≡
  false
bridgeKeepsYM5Open =
  refl

strictAbsorptionIsCanonical :
  strictAbsorptionProved canonicalYMPolymerActivityStrictAbsorptionBridgeReceipt
  ≡
  true
strictAbsorptionIsCanonical =
  refl

bridgeKeepsClayFalse :
  clayYangMillsPromoted canonicalYMPolymerActivityStrictAbsorptionBridgeReceipt
  ≡
  false
bridgeKeepsClayFalse =
  refl
