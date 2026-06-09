module DASHI.Physics.Closure.UnificationGluingCrossTermNullClassBoundary where

-- Fail-closed unification boundary for the next U-1a sub-obligation.
--
-- Target:
--
--   G (s1 + s2) - G s1 - G s2
--
-- lies in the null class of the admissible defect quotient.  This is the
-- missing bridge between quotient vocabulary and true gluing additivity:
-- additivity may hold only modulo null gluing residuals, and the cross-term
-- must be proven null before four-point cancellation can consume the U-1a
-- surface.
--
-- This module records vocabulary, prerequisites, blockers, and promotion
-- gates only.  It proves no cross-term null-class theorem, no gluing
-- linearity theorem, no four-point cancellation theorem, no parallelogram
-- theorem, no quadratic emergence theorem, and no terminal promotion.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary
  as U1a
import DASHI.Physics.Closure.GluingResidualForcesFourPointCancellationBoundary
  as Residual

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Cross-term vocabulary.

record GluingCrossTermNullClassVocabulary
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    -V_ :
      U1a.DefectQuotientV V → U1a.DefectQuotientV V

    nullClass :
      U1a.DefectQuotientV V → Set

    crossTerm :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V

    crossTermEquationText :
      String

    crossTermEquationTextIsCanonical :
      crossTermEquationText
      ≡ "crossTerm s1 s2 = G(s1 +V s2) +V (-V G s1) +V (-V G s2)"

    nullClassVocabularyRecorded :
      Bool

    nullClassVocabularyRecordedIsTrue :
      nullClassVocabularyRecorded ≡ true

open GluingCrossTermNullClassVocabulary public

record GluingCrossTermNullClassObligation
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V)
  (vocabulary : GluingCrossTermNullClassVocabulary V G-boundary) : Setω where
  field
    crossTermNullForAdmissibleSections :
      String

    representativeInvarianceRequired :
      String

    nullClassStableUnderGRequired :
      String

    crossTermNullClassProved :
      Bool

    crossTermNullClassProvedIsFalse :
      crossTermNullClassProved ≡ false

open GluingCrossTermNullClassObligation public

------------------------------------------------------------------------
-- Boundary stages, statuses, and blockers.

data CrossTermNullClassStage : Set where
  admissibleDefectQuotientImported :
    CrossTermNullClassStage

  gluingOperatorImported :
    CrossTermNullClassStage

  additiveInverseVocabulary :
    CrossTermNullClassStage

  nullClassPredicateVocabulary :
    CrossTermNullClassStage

  crossTermExpression :
    CrossTermNullClassStage

  representativeInvariance :
    CrossTermNullClassStage

  nullClassStabilityUnderG :
    CrossTermNullClassStage

  crossTermNullClassTheorem :
    CrossTermNullClassStage

  gluingLinearityModuloNull :
    CrossTermNullClassStage

  fourPointCancellationConsumer :
    CrossTermNullClassStage

  terminalPromotionGate :
    CrossTermNullClassStage

data CrossTermNullClassStatus : Set where
  importedBoundary :
    CrossTermNullClassStatus

  vocabularyRecorded :
    CrossTermNullClassStatus

  prerequisiteOpen :
    CrossTermNullClassStatus

  theoremOpen :
    CrossTermNullClassStatus

  downstreamBlocked :
    CrossTermNullClassStatus

  promotionHeld :
    CrossTermNullClassStatus

canonicalCrossTermStatus :
  CrossTermNullClassStage → CrossTermNullClassStatus
canonicalCrossTermStatus admissibleDefectQuotientImported =
  importedBoundary
canonicalCrossTermStatus gluingOperatorImported =
  importedBoundary
canonicalCrossTermStatus additiveInverseVocabulary =
  vocabularyRecorded
canonicalCrossTermStatus nullClassPredicateVocabulary =
  vocabularyRecorded
canonicalCrossTermStatus crossTermExpression =
  vocabularyRecorded
canonicalCrossTermStatus representativeInvariance =
  prerequisiteOpen
canonicalCrossTermStatus nullClassStabilityUnderG =
  prerequisiteOpen
canonicalCrossTermStatus crossTermNullClassTheorem =
  theoremOpen
canonicalCrossTermStatus gluingLinearityModuloNull =
  downstreamBlocked
canonicalCrossTermStatus fourPointCancellationConsumer =
  downstreamBlocked
canonicalCrossTermStatus terminalPromotionGate =
  promotionHeld

data CrossTermNullClassBlocker : Set where
  noBlockerForImportedBoundary :
    CrossTermNullClassBlocker

  noBlockerForVocabulary :
    CrossTermNullClassBlocker

  missingRepresentativeInvarianceOfCrossTerm :
    CrossTermNullClassBlocker

  missingNullClassStabilityUnderG :
    CrossTermNullClassBlocker

  missingCrossTermNullClassProof :
    CrossTermNullClassBlocker

  missingModuloNullToTrueLinearityBridge :
    CrossTermNullClassBlocker

  missingGluingResidualForcesFourPointCancellation :
    CrossTermNullClassBlocker

  noTerminalPromotionAuthority :
    CrossTermNullClassBlocker

canonicalCrossTermBlocker :
  CrossTermNullClassStage → CrossTermNullClassBlocker
canonicalCrossTermBlocker admissibleDefectQuotientImported =
  noBlockerForImportedBoundary
canonicalCrossTermBlocker gluingOperatorImported =
  noBlockerForImportedBoundary
canonicalCrossTermBlocker additiveInverseVocabulary =
  noBlockerForVocabulary
canonicalCrossTermBlocker nullClassPredicateVocabulary =
  noBlockerForVocabulary
canonicalCrossTermBlocker crossTermExpression =
  noBlockerForVocabulary
canonicalCrossTermBlocker representativeInvariance =
  missingRepresentativeInvarianceOfCrossTerm
canonicalCrossTermBlocker nullClassStabilityUnderG =
  missingNullClassStabilityUnderG
canonicalCrossTermBlocker crossTermNullClassTheorem =
  missingCrossTermNullClassProof
canonicalCrossTermBlocker gluingLinearityModuloNull =
  missingModuloNullToTrueLinearityBridge
canonicalCrossTermBlocker fourPointCancellationConsumer =
  missingGluingResidualForcesFourPointCancellation
canonicalCrossTermBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record CrossTermNullClassTargetRow : Set where
  field
    stage :
      CrossTermNullClassStage

    status :
      CrossTermNullClassStatus

    statusIsCanonical :
      status ≡ canonicalCrossTermStatus stage

    blocker :
      CrossTermNullClassBlocker

    blockerIsCanonical :
      blocker ≡ canonicalCrossTermBlocker stage

    obligation :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open CrossTermNullClassTargetRow public

mkCrossTermTargetRow :
  CrossTermNullClassStage →
  String →
  CrossTermNullClassTargetRow
mkCrossTermTargetRow stage obligation =
  record
    { stage =
        stage
    ; status =
        canonicalCrossTermStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalCrossTermBlocker stage
    ; blockerIsCanonical =
        refl
    ; obligation =
        obligation
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalCrossTermTargetRows :
  List CrossTermNullClassTargetRow
canonicalCrossTermTargetRows =
  mkCrossTermTargetRow
    admissibleDefectQuotientImported
    "consume U-1a admissible defect quotient vocabulary"
  ∷ mkCrossTermTargetRow
    gluingOperatorImported
    "consume U-1a gluing operator vocabulary"
  ∷ mkCrossTermTargetRow
    additiveInverseVocabulary
    "record additive inverse vocabulary needed to write G(s1+s2)-Gs1-Gs2"
  ∷ mkCrossTermTargetRow
    nullClassPredicateVocabulary
    "record nullClass predicate on the admissible defect quotient"
  ∷ mkCrossTermTargetRow
    crossTermExpression
    "record crossTerm s1 s2 = G(s1+s2)-Gs1-Gs2 as the next U-1a sub-obligation"
  ∷ mkCrossTermTargetRow
    representativeInvariance
    "prove crossTerm is independent of admissible quotient representatives"
  ∷ mkCrossTermTargetRow
    nullClassStabilityUnderG
    "prove the null class is stable under the gluing operator and quotient operations"
  ∷ mkCrossTermTargetRow
    crossTermNullClassTheorem
    "prove nullClass (crossTerm s1 s2) for admissible defect sections s1 and s2"
  ∷ mkCrossTermTargetRow
    gluingLinearityModuloNull
    "derive G-linearity modulo null class before any true linearity consumer"
  ∷ mkCrossTermTargetRow
    fourPointCancellationConsumer
    "unlock GluingResidualForcesFourPointCancellation only after cross-term nullity and modulo-null linearity"
  ∷ mkCrossTermTargetRow
    terminalPromotionGate
    "hold terminal unification and Clay promotion"
  ∷ []

canonicalCrossTermTargetRowCount : Nat
canonicalCrossTermTargetRowCount =
  listLength canonicalCrossTermTargetRows

canonicalCrossTermTargetRowCountIs11 :
  canonicalCrossTermTargetRowCount ≡ 11
canonicalCrossTermTargetRowCountIs11 =
  refl

------------------------------------------------------------------------
-- Promotion authority is intentionally absent in this boundary.

data CrossTermTerminalPromotionAuthority : Set where

crossTermTerminalPromotionAuthorityImpossible :
  CrossTermTerminalPromotionAuthority →
  ⊥
crossTermTerminalPromotionAuthorityImpossible ()

------------------------------------------------------------------------
-- Canonical fail-closed record.

record UnificationGluingCrossTermNullClassBoundary : Setω where
  field
    gluingLinearityBoundary :
      U1a.GluingOperatorLinearityOnDefectQuotientBoundary

    residualForcesFourPointBoundary :
      Residual.GluingResidualForcesFourPointCancellationBoundary

    importedU1aBoundary :
      Bool

    importedU1aBoundaryIsTrue :
      importedU1aBoundary ≡ true

    importedResidualBoundary :
      Bool

    importedResidualBoundaryIsTrue :
      importedResidualBoundary ≡ true

    targetRows :
      List CrossTermNullClassTargetRow

    targetRowCount :
      Nat

    targetRowCountIs11 :
      targetRowCount ≡ 11

    targetRowCountMatchesRows :
      targetRowCount ≡ listLength targetRows

    additiveInverseVocabularyRecorded :
      Bool

    additiveInverseVocabularyRecordedIsTrue :
      additiveInverseVocabularyRecorded ≡ true

    nullClassPredicateRecorded :
      Bool

    nullClassPredicateRecordedIsTrue :
      nullClassPredicateRecorded ≡ true

    crossTermExpressionRecorded :
      Bool

    crossTermExpressionRecordedIsTrue :
      crossTermExpressionRecorded ≡ true

    representativeInvarianceProved :
      Bool

    representativeInvarianceProvedIsFalse :
      representativeInvarianceProved ≡ false

    nullClassStabilityProved :
      Bool

    nullClassStabilityProvedIsFalse :
      nullClassStabilityProved ≡ false

    crossTermNullClassTheoremProved :
      Bool

    crossTermNullClassTheoremProvedIsFalse :
      crossTermNullClassTheoremProved ≡ false

    gluingLinearityModuloNullProved :
      Bool

    gluingLinearityModuloNullProvedIsFalse :
      gluingLinearityModuloNullProved ≡ false

    fourPointCancellationProved :
      Bool

    fourPointCancellationProvedIsFalse :
      fourPointCancellationProved ≡ false

    parallelogramProved :
      Bool

    parallelogramProvedIsFalse :
      parallelogramProved ≡ false

    quadraticEmergenceProved :
      Bool

    quadraticEmergenceProvedIsFalse :
      quadraticEmergenceProved ≡ false

    terminalUnificationPromotion :
      Bool

    terminalUnificationPromotionIsFalse :
      terminalUnificationPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    promotionAuthorityImpossible :
      CrossTermTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationGluingCrossTermNullClassBoundary public

canonicalUnificationGluingCrossTermNullClassBoundary :
  UnificationGluingCrossTermNullClassBoundary
canonicalUnificationGluingCrossTermNullClassBoundary =
  record
    { gluingLinearityBoundary =
        U1a.canonicalGluingOperatorLinearityOnDefectQuotientBoundary
    ; residualForcesFourPointBoundary =
        Residual.canonicalGluingResidualForcesFourPointCancellationBoundary
    ; importedU1aBoundary =
        true
    ; importedU1aBoundaryIsTrue =
        refl
    ; importedResidualBoundary =
        true
    ; importedResidualBoundaryIsTrue =
        refl
    ; targetRows =
        canonicalCrossTermTargetRows
    ; targetRowCount =
        11
    ; targetRowCountIs11 =
        refl
    ; targetRowCountMatchesRows =
        refl
    ; additiveInverseVocabularyRecorded =
        true
    ; additiveInverseVocabularyRecordedIsTrue =
        refl
    ; nullClassPredicateRecorded =
        true
    ; nullClassPredicateRecordedIsTrue =
        refl
    ; crossTermExpressionRecorded =
        true
    ; crossTermExpressionRecordedIsTrue =
        refl
    ; representativeInvarianceProved =
        false
    ; representativeInvarianceProvedIsFalse =
        refl
    ; nullClassStabilityProved =
        false
    ; nullClassStabilityProvedIsFalse =
        refl
    ; crossTermNullClassTheoremProved =
        false
    ; crossTermNullClassTheoremProvedIsFalse =
        refl
    ; gluingLinearityModuloNullProved =
        false
    ; gluingLinearityModuloNullProvedIsFalse =
        refl
    ; fourPointCancellationProved =
        false
    ; fourPointCancellationProvedIsFalse =
        Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        Residual.canonicalParallelogramLawStillOpen
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        Residual.canonicalQuadraticFormEmergenceStillBlocked
    ; terminalUnificationPromotion =
        false
    ; terminalUnificationPromotionIsFalse =
        Residual.canonicalTerminalUnificationPromotionFalse
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        Residual.canonicalClayPromotionFalse
    ; promotionAuthorityImpossible =
        crossTermTerminalPromotionAuthorityImpossible
    ; notes =
        "Next U-1a sub-obligation isolated: prove the gluing additivity cross-term lies in the null class."
        ∷ "The expression is tracked as G(s1+s2)-Gs1-Gs2, represented with quotient additive inverse vocabulary."
        ∷ "Representative invariance and null-class stability are prerequisites, not proved here."
        ∷ "Four-point cancellation, parallelogram, quadratic emergence, terminal unification, and Clay promotion remain blocked."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalCrossTermBoundaryRowCountIs11 :
  targetRowCount canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ 11
canonicalCrossTermBoundaryRowCountIs11 =
  refl

canonicalCrossTermExpressionRecorded :
  crossTermExpressionRecorded
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ true
canonicalCrossTermExpressionRecorded =
  refl

canonicalCrossTermRepresentativeInvarianceStillOpen :
  representativeInvarianceProved
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermRepresentativeInvarianceStillOpen =
  refl

canonicalCrossTermNullClassStabilityStillOpen :
  nullClassStabilityProved
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermNullClassStabilityStillOpen =
  refl

canonicalCrossTermNullClassTheoremStillOpen :
  crossTermNullClassTheoremProved
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermNullClassTheoremStillOpen =
  refl

canonicalGluingLinearityModuloNullStillOpen :
  gluingLinearityModuloNullProved
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalGluingLinearityModuloNullStillOpen =
  refl

canonicalCrossTermFourPointCancellationStillOpen :
  fourPointCancellationProved
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermFourPointCancellationStillOpen =
  refl

canonicalCrossTermParallelogramStillOpen :
  parallelogramProved canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermParallelogramStillOpen =
  refl

canonicalCrossTermQuadraticEmergenceStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermQuadraticEmergenceStillBlocked =
  refl

canonicalCrossTermTerminalUnificationPromotionFalse :
  terminalUnificationPromotion
    canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermTerminalUnificationPromotionFalse =
  refl

canonicalCrossTermClayPromotionFalse :
  clayPromotion canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ false
canonicalCrossTermClayPromotionFalse =
  refl

canonicalCrossTermClayPromotionImpossible :
  clayPromotion canonicalUnificationGluingCrossTermNullClassBoundary
  ≡ true →
  ⊥
canonicalCrossTermClayPromotionImpossible ()
