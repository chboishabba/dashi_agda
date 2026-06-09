module DASHI.Physics.Closure.UnificationGluingCrossTermLinearityLiftBoundary where

-- Fail-closed child boundary for the U-1a lift:
--
--   crossTerm s1 s2 = G(s1 + s2) - G s1 - G s2
--   crossTerm s1 s2 ∈ nullClass
--   ------------------------------------------------
--   G(s1 + s2) = G s1 + G s2 on the admissible defect quotient
--   modulo null representatives.
--
-- The parent boundary records the cross-term null-class target.  This child
-- records the missing lift surface between nullity and quotient linearity:
-- representative invariance, null-class stability, polarization of the
-- two-homogeneous gluing residual, and downstream four-point cancellation
-- dependency.  It proves no cross-term nullity theorem, no quotient-linearity
-- theorem, no four-point cancellation theorem, no parallelogram theorem, no
-- quadratic emergence theorem, and no terminal or Clay promotion.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary
  as U1a
import DASHI.Physics.Closure.UnificationGluingCrossTermNullClassBoundary
  as CrossTerm
import DASHI.Physics.Closure.UnificationGluingLinearityCompositeBoundary
  as LinearityComposite
import DASHI.Physics.Closure.UnificationCrossTermToFourPointCompositeBoundary
  as CrossTermComposite

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Lift vocabulary.

record AdmissibleDefectQuotientLiftVocabulary : Setω where
  field
    quotientBoundary :
      U1a.AdmissibleDefectQuotientVBoundary

    quotientCarrierName :
      String

    nullClassName :
      String

    representativeRelationName :
      String

    quotientVocabularyImported :
      Bool

    quotientVocabularyImportedIsTrue :
      quotientVocabularyImported ≡ true

    nullClassVocabularyImported :
      Bool

    nullClassVocabularyImportedIsTrue :
      nullClassVocabularyImported ≡ true

open AdmissibleDefectQuotientLiftVocabulary public

record CrossTermLinearityLiftExpression
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    nullClass :
      U1a.DefectQuotientV V → Set

    representativeEquivalent :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      Set

    crossTerm :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V

    quotientLinearityModuloNullStatement :
      String

    quotientLinearityModuloNullStatementIsCanonical :
      quotientLinearityModuloNullStatement
      ≡ "nullClass (crossTerm s1 s2) -> G(s1 +V s2) == G s1 +V G s2 in the quotient modulo null representatives"

    liftExpressionRecorded :
      Bool

    liftExpressionRecordedIsTrue :
      liftExpressionRecorded ≡ true

open CrossTermLinearityLiftExpression public

------------------------------------------------------------------------
-- Lift dependency stages.

data LinearityLiftStage : Set where
  admissibleDefectQuotientImported :
    LinearityLiftStage

  nullClassImported :
    LinearityLiftStage

  crossTermRepresentativeInvariance :
    LinearityLiftStage

  nullClassStableUnderQuotientOperations :
    LinearityLiftStage

  nullClassStableUnderGluingOperator :
    LinearityLiftStage

  crossTermNullityHypothesis :
    LinearityLiftStage

  polarizationCrossTermLift :
    LinearityLiftStage

  quotientLinearityModuloNull :
    LinearityLiftStage

  trueQuotientLinearityConsumer :
    LinearityLiftStage

  fourPointCancellationConsumer :
    LinearityLiftStage

  parallelogramConsumer :
    LinearityLiftStage

  quadraticEmergenceConsumer :
    LinearityLiftStage

  terminalPromotionGate :
    LinearityLiftStage

data LinearityLiftStatus : Set where
  importedBoundary :
    LinearityLiftStatus

  prerequisiteOpen :
    LinearityLiftStatus

  hypothesisOpen :
    LinearityLiftStatus

  liftOpen :
    LinearityLiftStatus

  downstreamBlocked :
    LinearityLiftStatus

  promotionHeld :
    LinearityLiftStatus

canonicalLinearityLiftStatus :
  LinearityLiftStage → LinearityLiftStatus
canonicalLinearityLiftStatus admissibleDefectQuotientImported =
  importedBoundary
canonicalLinearityLiftStatus nullClassImported =
  importedBoundary
canonicalLinearityLiftStatus crossTermRepresentativeInvariance =
  prerequisiteOpen
canonicalLinearityLiftStatus nullClassStableUnderQuotientOperations =
  prerequisiteOpen
canonicalLinearityLiftStatus nullClassStableUnderGluingOperator =
  prerequisiteOpen
canonicalLinearityLiftStatus crossTermNullityHypothesis =
  hypothesisOpen
canonicalLinearityLiftStatus polarizationCrossTermLift =
  liftOpen
canonicalLinearityLiftStatus quotientLinearityModuloNull =
  liftOpen
canonicalLinearityLiftStatus trueQuotientLinearityConsumer =
  downstreamBlocked
canonicalLinearityLiftStatus fourPointCancellationConsumer =
  downstreamBlocked
canonicalLinearityLiftStatus parallelogramConsumer =
  downstreamBlocked
canonicalLinearityLiftStatus quadraticEmergenceConsumer =
  downstreamBlocked
canonicalLinearityLiftStatus terminalPromotionGate =
  promotionHeld

data LinearityLiftBlocker : Set where
  noBlockerForImportedBoundary :
    LinearityLiftBlocker

  missingCrossTermRepresentativeInvariance :
    LinearityLiftBlocker

  missingNullClassOperationStability :
    LinearityLiftBlocker

  missingNullClassGluingStability :
    LinearityLiftBlocker

  missingCrossTermNullityTheorem :
    LinearityLiftBlocker

  missingPolarizationLiftFromTwoHomogeneousResidual :
    LinearityLiftBlocker

  missingModuloNullToQuotientEqualityTransport :
    LinearityLiftBlocker

  missingTrueGluingLinearityConsumer :
    LinearityLiftBlocker

  missingFourPointCancellationConsumer :
    LinearityLiftBlocker

  missingParallelogramConsumer :
    LinearityLiftBlocker

  missingQuadraticEmergenceConsumer :
    LinearityLiftBlocker

  noTerminalPromotionAuthority :
    LinearityLiftBlocker

canonicalLinearityLiftBlocker :
  LinearityLiftStage → LinearityLiftBlocker
canonicalLinearityLiftBlocker admissibleDefectQuotientImported =
  noBlockerForImportedBoundary
canonicalLinearityLiftBlocker nullClassImported =
  noBlockerForImportedBoundary
canonicalLinearityLiftBlocker crossTermRepresentativeInvariance =
  missingCrossTermRepresentativeInvariance
canonicalLinearityLiftBlocker nullClassStableUnderQuotientOperations =
  missingNullClassOperationStability
canonicalLinearityLiftBlocker nullClassStableUnderGluingOperator =
  missingNullClassGluingStability
canonicalLinearityLiftBlocker crossTermNullityHypothesis =
  missingCrossTermNullityTheorem
canonicalLinearityLiftBlocker polarizationCrossTermLift =
  missingPolarizationLiftFromTwoHomogeneousResidual
canonicalLinearityLiftBlocker quotientLinearityModuloNull =
  missingModuloNullToQuotientEqualityTransport
canonicalLinearityLiftBlocker trueQuotientLinearityConsumer =
  missingTrueGluingLinearityConsumer
canonicalLinearityLiftBlocker fourPointCancellationConsumer =
  missingFourPointCancellationConsumer
canonicalLinearityLiftBlocker parallelogramConsumer =
  missingParallelogramConsumer
canonicalLinearityLiftBlocker quadraticEmergenceConsumer =
  missingQuadraticEmergenceConsumer
canonicalLinearityLiftBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record LinearityLiftTargetRow : Set where
  field
    stage :
      LinearityLiftStage

    status :
      LinearityLiftStatus

    statusIsCanonical :
      status ≡ canonicalLinearityLiftStatus stage

    blocker :
      LinearityLiftBlocker

    blockerIsCanonical :
      blocker ≡ canonicalLinearityLiftBlocker stage

    proofContract :
      String

    importedSupport :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open LinearityLiftTargetRow public

mkLinearityLiftTargetRow :
  LinearityLiftStage →
  String →
  String →
  LinearityLiftTargetRow
mkLinearityLiftTargetRow stage proofContract importedSupport =
  record
    { stage =
        stage
    ; status =
        canonicalLinearityLiftStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalLinearityLiftBlocker stage
    ; blockerIsCanonical =
        refl
    ; proofContract =
        proofContract
    ; importedSupport =
        importedSupport
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalLinearityLiftTargetRows :
  List LinearityLiftTargetRow
canonicalLinearityLiftTargetRows =
  mkLinearityLiftTargetRow
    admissibleDefectQuotientImported
    "import admissible defect quotient V, quotient operations, and representative vocabulary"
    "GluingOperatorLinearityOnDefectQuotientBoundary"
  ∷ mkLinearityLiftTargetRow
    nullClassImported
    "import nullClass and crossTerm vocabulary from the cross-term null boundary"
    "UnificationGluingCrossTermNullClassBoundary"
  ∷ mkLinearityLiftTargetRow
    crossTermRepresentativeInvariance
    "prove crossTerm respects admissible quotient representatives in both inputs"
    "parent cross-term boundary keeps representative invariance open"
  ∷ mkLinearityLiftTargetRow
    nullClassStableUnderQuotientOperations
    "prove nullClass is stable under zero, addition, inverse, and representative transport"
    "parent cross-term boundary keeps null-class stability open"
  ∷ mkLinearityLiftTargetRow
    nullClassStableUnderGluingOperator
    "prove nullClass is stable under G so null residuals remain invisible after gluing"
    "parent cross-term boundary keeps null-class stability open"
  ∷ mkLinearityLiftTargetRow
    crossTermNullityHypothesis
    "prove nullClass (crossTerm s1 s2) for admissible defect sections"
    "UnificationGluingCrossTermNullClassBoundary"
  ∷ mkLinearityLiftTargetRow
    polarizationCrossTermLift
    "lift two-homogeneous gluing residuals by polarization and identify the additive cross-term"
    "GluingOperatorLinearityOnDefectQuotientBoundary"
  ∷ mkLinearityLiftTargetRow
    quotientLinearityModuloNull
    "transport cross-term nullity into G(s1+s2)=Gs1+Gs2 modulo null representatives"
    "UnificationGluingLinearityCompositeBoundary"
  ∷ mkLinearityLiftTargetRow
    trueQuotientLinearityConsumer
    "consume modulo-null equality only after representative transport gives true quotient linearity"
    "UnificationGluingLinearityCompositeBoundary"
  ∷ mkLinearityLiftTargetRow
    fourPointCancellationConsumer
    "unlock GluingResidualForcesFourPointCancellation only after quotient linearity"
    "UnificationCrossTermToFourPointCompositeBoundary"
  ∷ mkLinearityLiftTargetRow
    parallelogramConsumer
    "derive parallelogram only after four-point cancellation"
    "UnificationCrossTermToFourPointCompositeBoundary"
  ∷ mkLinearityLiftTargetRow
    quadraticEmergenceConsumer
    "derive quadratic form only after parallelogram law"
    "UnificationCrossTermToFourPointCompositeBoundary"
  ∷ mkLinearityLiftTargetRow
    terminalPromotionGate
    "hold terminal unification and Clay promotion"
    "all imported surfaces keep promotion false"
  ∷ []

canonicalLinearityLiftTargetRowCount : Nat
canonicalLinearityLiftTargetRowCount =
  listLength canonicalLinearityLiftTargetRows

canonicalLinearityLiftTargetRowCountIs13 :
  canonicalLinearityLiftTargetRowCount ≡ 13
canonicalLinearityLiftTargetRowCountIs13 =
  refl

------------------------------------------------------------------------
-- Imported support and fail-closed boundary.

record LinearityLiftImportedSupport : Setω where
  field
    crossTermBoundary :
      CrossTerm.UnificationGluingCrossTermNullClassBoundary

    gluingLinearityComposite :
      LinearityComposite.UnificationGluingLinearityCompositeBoundary

    crossTermToFourPointComposite :
      CrossTermComposite.UnificationCrossTermToFourPointCompositeBoundary

    parentRepresentativeInvarianceStillOpen :
      CrossTerm.representativeInvarianceProved crossTermBoundary ≡ false

    parentNullClassStabilityStillOpen :
      CrossTerm.nullClassStabilityProved crossTermBoundary ≡ false

    parentCrossTermNullityStillOpen :
      CrossTerm.crossTermNullClassTheoremProved crossTermBoundary ≡ false

    parentModuloNullLinearityStillOpen :
      CrossTerm.gluingLinearityModuloNullProved crossTermBoundary ≡ false

    compositeTrueLinearityStillOpen :
      LinearityComposite.gluingOperatorCompatibilityTheoremProved
        gluingLinearityComposite
        ≡ false

    downstreamFourPointStillOpen :
      CrossTermComposite.fourPointCancellationTheoremProved
        crossTermToFourPointComposite
        ≡ false

    downstreamParallelogramStillOpen :
      CrossTermComposite.parallelogramTheoremProved
        crossTermToFourPointComposite
        ≡ false

    downstreamQuadraticStillBlocked :
      CrossTermComposite.quadraticEmergenceTheoremProved
        crossTermToFourPointComposite
        ≡ false

    downstreamTerminalPromotionFalse :
      CrossTermComposite.terminalUnificationPromoted
        crossTermToFourPointComposite
        ≡ false

    downstreamClayPromotionFalse :
      CrossTermComposite.clayPromoted crossTermToFourPointComposite
      ≡ false

open LinearityLiftImportedSupport public

canonicalLinearityLiftImportedSupport :
  LinearityLiftImportedSupport
canonicalLinearityLiftImportedSupport =
  record
    { crossTermBoundary =
        CrossTerm.canonicalUnificationGluingCrossTermNullClassBoundary
    ; gluingLinearityComposite =
        LinearityComposite.canonicalUnificationGluingLinearityCompositeBoundary
    ; crossTermToFourPointComposite =
        CrossTermComposite.canonicalUnificationCrossTermToFourPointCompositeBoundary
    ; parentRepresentativeInvarianceStillOpen =
        CrossTerm.canonicalCrossTermRepresentativeInvarianceStillOpen
    ; parentNullClassStabilityStillOpen =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; parentCrossTermNullityStillOpen =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; parentModuloNullLinearityStillOpen =
        CrossTerm.canonicalGluingLinearityModuloNullStillOpen
    ; compositeTrueLinearityStillOpen =
        LinearityComposite.canonicalCompositeGluingCompatibilityTheoremFalse
    ; downstreamFourPointStillOpen =
        CrossTermComposite.canonicalCrossTermToFourPointCancellationStillOpen
    ; downstreamParallelogramStillOpen =
        CrossTermComposite.canonicalCrossTermToFourPointParallelogramStillOpen
    ; downstreamQuadraticStillBlocked =
        CrossTermComposite.canonicalCrossTermToFourPointQuadraticStillBlocked
    ; downstreamTerminalPromotionFalse =
        CrossTermComposite.canonicalCrossTermToFourPointTerminalPromotionFalse
    ; downstreamClayPromotionFalse =
        CrossTermComposite.canonicalCrossTermToFourPointClayPromotionFalse
    }

data LinearityLiftTerminalPromotionAuthority : Set where

linearityLiftTerminalPromotionAuthorityImpossible :
  LinearityLiftTerminalPromotionAuthority →
  ⊥
linearityLiftTerminalPromotionAuthorityImpossible ()

record UnificationGluingCrossTermLinearityLiftBoundary : Setω where
  field
    importedSupport :
      LinearityLiftImportedSupport

    targetRows :
      List LinearityLiftTargetRow

    targetRowCount :
      Nat

    targetRowCountIs13 :
      targetRowCount ≡ 13

    targetRowCountMatchesRows :
      targetRowCount ≡ listLength targetRows

    admissibleDefectQuotientRecorded :
      Bool

    admissibleDefectQuotientRecordedIsTrue :
      admissibleDefectQuotientRecorded ≡ true

    nullClassRecorded :
      Bool

    nullClassRecordedIsTrue :
      nullClassRecorded ≡ true

    crossTermRepresentativeInvarianceProved :
      Bool

    crossTermRepresentativeInvarianceProvedIsFalse :
      crossTermRepresentativeInvarianceProved ≡ false

    nullClassOperationStabilityProved :
      Bool

    nullClassOperationStabilityProvedIsFalse :
      nullClassOperationStabilityProved ≡ false

    nullClassGluingStabilityProved :
      Bool

    nullClassGluingStabilityProvedIsFalse :
      nullClassGluingStabilityProved ≡ false

    crossTermNullityProved :
      Bool

    crossTermNullityProvedIsFalse :
      crossTermNullityProved ≡ false

    polarizationLiftProved :
      Bool

    polarizationLiftProvedIsFalse :
      polarizationLiftProved ≡ false

    quotientLinearityModuloNullProved :
      Bool

    quotientLinearityModuloNullProvedIsFalse :
      quotientLinearityModuloNullProved ≡ false

    trueQuotientLinearityProved :
      Bool

    trueQuotientLinearityProvedIsFalse :
      trueQuotientLinearityProved ≡ false

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

    allPromotionFlagsFalse :
      Bool

    allPromotionFlagsFalseIsTrue :
      allPromotionFlagsFalse ≡ true

    promotionAuthorityImpossible :
      LinearityLiftTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationGluingCrossTermLinearityLiftBoundary public

canonicalUnificationGluingCrossTermLinearityLiftBoundary :
  UnificationGluingCrossTermLinearityLiftBoundary
canonicalUnificationGluingCrossTermLinearityLiftBoundary =
  record
    { importedSupport =
        canonicalLinearityLiftImportedSupport
    ; targetRows =
        canonicalLinearityLiftTargetRows
    ; targetRowCount =
        13
    ; targetRowCountIs13 =
        refl
    ; targetRowCountMatchesRows =
        refl
    ; admissibleDefectQuotientRecorded =
        true
    ; admissibleDefectQuotientRecordedIsTrue =
        refl
    ; nullClassRecorded =
        true
    ; nullClassRecordedIsTrue =
        refl
    ; crossTermRepresentativeInvarianceProved =
        false
    ; crossTermRepresentativeInvarianceProvedIsFalse =
        CrossTerm.canonicalCrossTermRepresentativeInvarianceStillOpen
    ; nullClassOperationStabilityProved =
        false
    ; nullClassOperationStabilityProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; nullClassGluingStabilityProved =
        false
    ; nullClassGluingStabilityProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; crossTermNullityProved =
        false
    ; crossTermNullityProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; polarizationLiftProved =
        false
    ; polarizationLiftProvedIsFalse =
        refl
    ; quotientLinearityModuloNullProved =
        false
    ; quotientLinearityModuloNullProvedIsFalse =
        CrossTerm.canonicalGluingLinearityModuloNullStillOpen
    ; trueQuotientLinearityProved =
        false
    ; trueQuotientLinearityProvedIsFalse =
        LinearityComposite.canonicalCompositeGluingCompatibilityTheoremFalse
    ; fourPointCancellationProved =
        false
    ; fourPointCancellationProvedIsFalse =
        CrossTermComposite.canonicalCrossTermToFourPointCancellationStillOpen
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        CrossTermComposite.canonicalCrossTermToFourPointParallelogramStillOpen
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        CrossTermComposite.canonicalCrossTermToFourPointQuadraticStillBlocked
    ; terminalUnificationPromotion =
        false
    ; terminalUnificationPromotionIsFalse =
        CrossTermComposite.canonicalCrossTermToFourPointTerminalPromotionFalse
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        CrossTermComposite.canonicalCrossTermToFourPointClayPromotionFalse
    ; allPromotionFlagsFalse =
        true
    ; allPromotionFlagsFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        linearityLiftTerminalPromotionAuthorityImpossible
    ; notes =
        "Child U-1a lift boundary added: cross-term nullity must be representative-invariant before it can imply quotient linearity."
        ∷ "Polarization is recorded as the bridge from two-homogeneous gluing residuals to the additive cross-term, not as a proved theorem."
        ∷ "Modulo-null quotient linearity, true quotient linearity, four-point cancellation, parallelogram, and quadratic emergence remain downstream blocked."
        ∷ "All terminal, unification, and Clay promotion flags remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for consumers.

canonicalLinearityLiftRowCountIs13 :
  targetRowCount canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ 13
canonicalLinearityLiftRowCountIs13 =
  refl

canonicalLinearityLiftRepresentativeInvarianceStillOpen :
  crossTermRepresentativeInvarianceProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftRepresentativeInvarianceStillOpen =
  CrossTerm.canonicalCrossTermRepresentativeInvarianceStillOpen

canonicalLinearityLiftNullClassOperationStabilityStillOpen :
  nullClassOperationStabilityProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftNullClassOperationStabilityStillOpen =
  CrossTerm.canonicalCrossTermNullClassStabilityStillOpen

canonicalLinearityLiftNullClassGluingStabilityStillOpen :
  nullClassGluingStabilityProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftNullClassGluingStabilityStillOpen =
  CrossTerm.canonicalCrossTermNullClassStabilityStillOpen

canonicalLinearityLiftCrossTermNullityStillOpen :
  crossTermNullityProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftCrossTermNullityStillOpen =
  CrossTerm.canonicalCrossTermNullClassTheoremStillOpen

canonicalLinearityLiftPolarizationStillOpen :
  polarizationLiftProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftPolarizationStillOpen =
  refl

canonicalLinearityLiftModuloNullLinearityStillOpen :
  quotientLinearityModuloNullProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftModuloNullLinearityStillOpen =
  CrossTerm.canonicalGluingLinearityModuloNullStillOpen

canonicalLinearityLiftTrueLinearityStillOpen :
  trueQuotientLinearityProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftTrueLinearityStillOpen =
  LinearityComposite.canonicalCompositeGluingCompatibilityTheoremFalse

canonicalLinearityLiftFourPointStillOpen :
  fourPointCancellationProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftFourPointStillOpen =
  CrossTermComposite.canonicalCrossTermToFourPointCancellationStillOpen

canonicalLinearityLiftParallelogramStillOpen :
  parallelogramProved canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftParallelogramStillOpen =
  CrossTermComposite.canonicalCrossTermToFourPointParallelogramStillOpen

canonicalLinearityLiftQuadraticStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftQuadraticStillBlocked =
  CrossTermComposite.canonicalCrossTermToFourPointQuadraticStillBlocked

canonicalLinearityLiftTerminalPromotionFalse :
  terminalUnificationPromotion
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftTerminalPromotionFalse =
  CrossTermComposite.canonicalCrossTermToFourPointTerminalPromotionFalse

canonicalLinearityLiftClayPromotionFalse :
  clayPromotion canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ false
canonicalLinearityLiftClayPromotionFalse =
  CrossTermComposite.canonicalCrossTermToFourPointClayPromotionFalse

canonicalLinearityLiftAllPromotionFlagsFalse :
  allPromotionFlagsFalse
    canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ true
canonicalLinearityLiftAllPromotionFlagsFalse =
  refl

canonicalLinearityLiftClayPromotionImpossible :
  clayPromotion canonicalUnificationGluingCrossTermLinearityLiftBoundary
  ≡ true →
  ⊥
canonicalLinearityLiftClayPromotionImpossible ()
