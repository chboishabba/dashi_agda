module DASHI.Physics.Closure.UnificationNullClassStabilityBoundary where

-- Fail-closed child boundary for the U-1a null-class stability surface.
--
-- Parent surfaces record that the additive cross-term
--
--   G(s1 + s2) - G s1 - G s2
--
-- must lie in the null class before gluing linearity can be lifted to the
-- admissible defect quotient.  This child isolates the algebraic stability
-- obligations on that null class:
--
--   representative invariance
--   zero/addition/inverse/scalar closure
--   stability under the gluing operator G
--   transport from null predicate to quotient equality
--   consumption by the cross-term-to-linearity lift
--
-- It proves no null-class stability theorem, no cross-term nullity theorem,
-- no quotient-linearity theorem, no four-point cancellation theorem, no
-- parallelogram theorem, no quadratic-emergence theorem, and no terminal or
-- Clay promotion.

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
import DASHI.Physics.Closure.UnificationGluingCrossTermLinearityLiftBoundary
  as Lift
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
-- Null-class operation vocabulary.

record NullClassOperationVocabulary
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    nullClass :
      U1a.DefectQuotientV V → Set

    representativeEquivalent :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      Set

    -V_ :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V

    crossTerm :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V

    nullPredicateName :
      String

    nullPredicateNameIsCanonical :
      nullPredicateName
      ≡ "nullClass : DefectQuotientV -> Set"

    representativeRelationName :
      String

    representativeRelationNameIsCanonical :
      representativeRelationName
      ≡ "representativeEquivalent : DefectQuotientV -> DefectQuotientV -> Set"

    operationVocabularyRecorded :
      Bool

    operationVocabularyRecordedIsTrue :
      operationVocabularyRecorded ≡ true

open NullClassOperationVocabulary public

record NullClassStabilityObligations
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V)
  (vocabulary : NullClassOperationVocabulary V G-boundary) : Setω where
  field
    representativeInvarianceObligation :
      String

    zeroClosureObligation :
      String

    additionClosureObligation :
      String

    inverseClosureObligation :
      String

    scalarClosureObligation :
      String

    gluingStabilityObligation :
      String

    nullPredicateToQuotientEqualityTransportObligation :
      String

    crossTermNullityToModuloLinearityObligation :
      String

    nullClassStabilityTheoremProved :
      Bool

    nullClassStabilityTheoremProvedIsFalse :
      nullClassStabilityTheoremProved ≡ false

open NullClassStabilityObligations public

------------------------------------------------------------------------
-- Stability stages, statuses, blockers.

data NullClassStabilityStage : Set where
  parentCrossTermBoundaryImported :
    NullClassStabilityStage

  parentLinearityLiftImported :
    NullClassStabilityStage

  nullRepresentativeRelation :
    NullClassStabilityStage

  nullZeroClosure :
    NullClassStabilityStage

  nullAdditionClosure :
    NullClassStabilityStage

  nullInverseClosure :
    NullClassStabilityStage

  nullScalarClosure :
    NullClassStabilityStage

  nullRepresentativeInvariance :
    NullClassStabilityStage

  nullGluingOperatorStability :
    NullClassStabilityStage

  nullPredicateToQuotientEqualityTransport :
    NullClassStabilityStage

  crossTermNullityToModuloLinearity :
    NullClassStabilityStage

  trueQuotientLinearityConsumer :
    NullClassStabilityStage

  fourPointCancellationConsumer :
    NullClassStabilityStage

  parallelogramConsumer :
    NullClassStabilityStage

  quadraticEmergenceConsumer :
    NullClassStabilityStage

  terminalPromotionGate :
    NullClassStabilityStage

data NullClassStabilityStatus : Set where
  importedBoundary :
    NullClassStabilityStatus

  vocabularyRecorded :
    NullClassStabilityStatus

  stabilityOpen :
    NullClassStabilityStatus

  transportOpen :
    NullClassStabilityStatus

  downstreamBlocked :
    NullClassStabilityStatus

  promotionHeld :
    NullClassStabilityStatus

canonicalNullClassStabilityStatus :
  NullClassStabilityStage → NullClassStabilityStatus
canonicalNullClassStabilityStatus parentCrossTermBoundaryImported =
  importedBoundary
canonicalNullClassStabilityStatus parentLinearityLiftImported =
  importedBoundary
canonicalNullClassStabilityStatus nullRepresentativeRelation =
  vocabularyRecorded
canonicalNullClassStabilityStatus nullZeroClosure =
  stabilityOpen
canonicalNullClassStabilityStatus nullAdditionClosure =
  stabilityOpen
canonicalNullClassStabilityStatus nullInverseClosure =
  stabilityOpen
canonicalNullClassStabilityStatus nullScalarClosure =
  stabilityOpen
canonicalNullClassStabilityStatus nullRepresentativeInvariance =
  stabilityOpen
canonicalNullClassStabilityStatus nullGluingOperatorStability =
  stabilityOpen
canonicalNullClassStabilityStatus nullPredicateToQuotientEqualityTransport =
  transportOpen
canonicalNullClassStabilityStatus crossTermNullityToModuloLinearity =
  transportOpen
canonicalNullClassStabilityStatus trueQuotientLinearityConsumer =
  downstreamBlocked
canonicalNullClassStabilityStatus fourPointCancellationConsumer =
  downstreamBlocked
canonicalNullClassStabilityStatus parallelogramConsumer =
  downstreamBlocked
canonicalNullClassStabilityStatus quadraticEmergenceConsumer =
  downstreamBlocked
canonicalNullClassStabilityStatus terminalPromotionGate =
  promotionHeld

data NullClassStabilityBlocker : Set where
  noBlockerForImportedBoundary :
    NullClassStabilityBlocker

  missingNullRepresentativeRelation :
    NullClassStabilityBlocker

  missingNullZeroStability :
    NullClassStabilityBlocker

  missingNullAdditionStability :
    NullClassStabilityBlocker

  missingNullInverseStability :
    NullClassStabilityBlocker

  missingNullScalarStability :
    NullClassStabilityBlocker

  missingRepresentativeInvariance :
    NullClassStabilityBlocker

  missingGStability :
    NullClassStabilityBlocker

  missingTransportFromNullPredicateToQuotientEquality :
    NullClassStabilityBlocker

  missingTransportFromCrossTermNullityToModuloNullLinearity :
    NullClassStabilityBlocker

  missingTrueQuotientLinearityConsumer :
    NullClassStabilityBlocker

  missingFourPointCancellationConsumer :
    NullClassStabilityBlocker

  missingParallelogramConsumer :
    NullClassStabilityBlocker

  missingQuadraticEmergenceConsumer :
    NullClassStabilityBlocker

  noTerminalPromotionAuthority :
    NullClassStabilityBlocker

canonicalNullClassStabilityBlocker :
  NullClassStabilityStage → NullClassStabilityBlocker
canonicalNullClassStabilityBlocker parentCrossTermBoundaryImported =
  noBlockerForImportedBoundary
canonicalNullClassStabilityBlocker parentLinearityLiftImported =
  noBlockerForImportedBoundary
canonicalNullClassStabilityBlocker nullRepresentativeRelation =
  missingNullRepresentativeRelation
canonicalNullClassStabilityBlocker nullZeroClosure =
  missingNullZeroStability
canonicalNullClassStabilityBlocker nullAdditionClosure =
  missingNullAdditionStability
canonicalNullClassStabilityBlocker nullInverseClosure =
  missingNullInverseStability
canonicalNullClassStabilityBlocker nullScalarClosure =
  missingNullScalarStability
canonicalNullClassStabilityBlocker nullRepresentativeInvariance =
  missingRepresentativeInvariance
canonicalNullClassStabilityBlocker nullGluingOperatorStability =
  missingGStability
canonicalNullClassStabilityBlocker nullPredicateToQuotientEqualityTransport =
  missingTransportFromNullPredicateToQuotientEquality
canonicalNullClassStabilityBlocker crossTermNullityToModuloLinearity =
  missingTransportFromCrossTermNullityToModuloNullLinearity
canonicalNullClassStabilityBlocker trueQuotientLinearityConsumer =
  missingTrueQuotientLinearityConsumer
canonicalNullClassStabilityBlocker fourPointCancellationConsumer =
  missingFourPointCancellationConsumer
canonicalNullClassStabilityBlocker parallelogramConsumer =
  missingParallelogramConsumer
canonicalNullClassStabilityBlocker quadraticEmergenceConsumer =
  missingQuadraticEmergenceConsumer
canonicalNullClassStabilityBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record NullClassStabilityTargetRow : Set where
  field
    stage :
      NullClassStabilityStage

    status :
      NullClassStabilityStatus

    statusIsCanonical :
      status ≡ canonicalNullClassStabilityStatus stage

    blocker :
      NullClassStabilityBlocker

    blockerIsCanonical :
      blocker ≡ canonicalNullClassStabilityBlocker stage

    proofContract :
      String

    consumer :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open NullClassStabilityTargetRow public

mkNullClassStabilityTargetRow :
  NullClassStabilityStage →
  String →
  String →
  NullClassStabilityTargetRow
mkNullClassStabilityTargetRow stage proofContract consumer =
  record
    { stage =
        stage
    ; status =
        canonicalNullClassStabilityStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalNullClassStabilityBlocker stage
    ; blockerIsCanonical =
        refl
    ; proofContract =
        proofContract
    ; consumer =
        consumer
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalNullClassStabilityTargetRows :
  List NullClassStabilityTargetRow
canonicalNullClassStabilityTargetRows =
  mkNullClassStabilityTargetRow
    parentCrossTermBoundaryImported
    "import cross-term null-class parent boundary and keep its theorem flags false"
    "UnificationGluingCrossTermNullClassBoundary"
  ∷ mkNullClassStabilityTargetRow
    parentLinearityLiftImported
    "import cross-term-to-linearity lift boundary and consume its open stability fields"
    "UnificationGluingCrossTermLinearityLiftBoundary"
  ∷ mkNullClassStabilityTargetRow
    nullRepresentativeRelation
    "define the representative relation identifying null residual representatives"
    "quotient equality transport"
  ∷ mkNullClassStabilityTargetRow
    nullZeroClosure
    "prove zeroV lies in the null class"
    "operation stability"
  ∷ mkNullClassStabilityTargetRow
    nullAdditionClosure
    "prove nullClass x and nullClass y imply nullClass (x +V y)"
    "operation stability"
  ∷ mkNullClassStabilityTargetRow
    nullInverseClosure
    "prove nullClass x implies nullClass (-V x)"
    "operation stability"
  ∷ mkNullClassStabilityTargetRow
    nullScalarClosure
    "prove nullClass x implies nullClass (a ·V x)"
    "operation stability"
  ∷ mkNullClassStabilityTargetRow
    nullRepresentativeInvariance
    "prove representativeEquivalent x y transports nullClass x to nullClass y"
    "representative-invariant quotient operations"
  ∷ mkNullClassStabilityTargetRow
    nullGluingOperatorStability
    "prove nullClass x implies nullClass (G x)"
    "G-stability required by modulo-null linearity"
  ∷ mkNullClassStabilityTargetRow
    nullPredicateToQuotientEqualityTransport
    "prove nullClass x transports to x == zero in the admissible quotient modulo null representatives"
    "quotient equality transport"
  ∷ mkNullClassStabilityTargetRow
    crossTermNullityToModuloLinearity
    "transport nullClass (crossTerm s1 s2) into G(s1+s2)=Gs1+Gs2 modulo null"
    "UnificationGluingCrossTermLinearityLiftBoundary"
  ∷ mkNullClassStabilityTargetRow
    trueQuotientLinearityConsumer
    "unlock true quotient linearity only after modulo-null transport and representative invariance"
    "GluingOperatorLinearityOnDefectQuotientBoundary"
  ∷ mkNullClassStabilityTargetRow
    fourPointCancellationConsumer
    "consume quotient linearity in GluingResidualForcesFourPointCancellation"
    "UnificationCrossTermToFourPointCompositeBoundary"
  ∷ mkNullClassStabilityTargetRow
    parallelogramConsumer
    "derive parallelogram only after four-point cancellation"
    "UnificationCrossTermToFourPointCompositeBoundary"
  ∷ mkNullClassStabilityTargetRow
    quadraticEmergenceConsumer
    "derive quadratic emergence only after the parallelogram law"
    "UnificationCrossTermToFourPointCompositeBoundary"
  ∷ mkNullClassStabilityTargetRow
    terminalPromotionGate
    "hold terminal unification and Clay promotion"
    "all imported promotion gates"
  ∷ []

canonicalNullClassStabilityTargetRowCount : Nat
canonicalNullClassStabilityTargetRowCount =
  listLength canonicalNullClassStabilityTargetRows

canonicalNullClassStabilityTargetRowCountIs16 :
  canonicalNullClassStabilityTargetRowCount ≡ 16
canonicalNullClassStabilityTargetRowCountIs16 =
  refl

------------------------------------------------------------------------
-- Imported support and fail-closed guard surface.

record NullClassStabilityImportedSupport : Setω where
  field
    crossTermBoundary :
      CrossTerm.UnificationGluingCrossTermNullClassBoundary

    linearityLiftBoundary :
      Lift.UnificationGluingCrossTermLinearityLiftBoundary

    crossTermToFourPointComposite :
      CrossTermComposite.UnificationCrossTermToFourPointCompositeBoundary

    parentRepresentativeInvarianceStillOpen :
      CrossTerm.representativeInvarianceProved crossTermBoundary ≡ false

    parentNullClassStabilityStillOpen :
      CrossTerm.nullClassStabilityProved crossTermBoundary ≡ false

    parentCrossTermNullityStillOpen :
      CrossTerm.crossTermNullClassTheoremProved crossTermBoundary ≡ false

    liftOperationStabilityStillOpen :
      Lift.nullClassOperationStabilityProved linearityLiftBoundary ≡ false

    liftGluingStabilityStillOpen :
      Lift.nullClassGluingStabilityProved linearityLiftBoundary ≡ false

    liftModuloNullLinearityStillOpen :
      Lift.quotientLinearityModuloNullProved linearityLiftBoundary ≡ false

    liftTrueLinearityStillOpen :
      Lift.trueQuotientLinearityProved linearityLiftBoundary ≡ false

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

open NullClassStabilityImportedSupport public

canonicalNullClassStabilityImportedSupport :
  NullClassStabilityImportedSupport
canonicalNullClassStabilityImportedSupport =
  record
    { crossTermBoundary =
        CrossTerm.canonicalUnificationGluingCrossTermNullClassBoundary
    ; linearityLiftBoundary =
        Lift.canonicalUnificationGluingCrossTermLinearityLiftBoundary
    ; crossTermToFourPointComposite =
        CrossTermComposite.canonicalUnificationCrossTermToFourPointCompositeBoundary
    ; parentRepresentativeInvarianceStillOpen =
        CrossTerm.canonicalCrossTermRepresentativeInvarianceStillOpen
    ; parentNullClassStabilityStillOpen =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; parentCrossTermNullityStillOpen =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; liftOperationStabilityStillOpen =
        Lift.canonicalLinearityLiftNullClassOperationStabilityStillOpen
    ; liftGluingStabilityStillOpen =
        Lift.canonicalLinearityLiftNullClassGluingStabilityStillOpen
    ; liftModuloNullLinearityStillOpen =
        Lift.canonicalLinearityLiftModuloNullLinearityStillOpen
    ; liftTrueLinearityStillOpen =
        Lift.canonicalLinearityLiftTrueLinearityStillOpen
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

data NullClassStabilityTerminalPromotionAuthority : Set where

nullClassStabilityTerminalPromotionAuthorityImpossible :
  NullClassStabilityTerminalPromotionAuthority →
  ⊥
nullClassStabilityTerminalPromotionAuthorityImpossible ()

record UnificationNullClassStabilityBoundary : Setω where
  field
    importedSupport :
      NullClassStabilityImportedSupport

    targetRows :
      List NullClassStabilityTargetRow

    targetRowCount :
      Nat

    targetRowCountIs16 :
      targetRowCount ≡ 16

    targetRowCountMatchesRows :
      targetRowCount ≡ listLength targetRows

    nullRepresentativeRelationDefined :
      Bool

    nullRepresentativeRelationDefinedIsFalse :
      nullRepresentativeRelationDefined ≡ false

    zeroClosureProved :
      Bool

    zeroClosureProvedIsFalse :
      zeroClosureProved ≡ false

    additionClosureProved :
      Bool

    additionClosureProvedIsFalse :
      additionClosureProved ≡ false

    inverseClosureProved :
      Bool

    inverseClosureProvedIsFalse :
      inverseClosureProved ≡ false

    scalarClosureProved :
      Bool

    scalarClosureProvedIsFalse :
      scalarClosureProved ≡ false

    representativeInvarianceProved :
      Bool

    representativeInvarianceProvedIsFalse :
      representativeInvarianceProved ≡ false

    gluingOperatorStabilityProved :
      Bool

    gluingOperatorStabilityProvedIsFalse :
      gluingOperatorStabilityProved ≡ false

    nullPredicateToQuotientEqualityTransportProved :
      Bool

    nullPredicateToQuotientEqualityTransportProvedIsFalse :
      nullPredicateToQuotientEqualityTransportProved ≡ false

    crossTermNullityToModuloLinearityProved :
      Bool

    crossTermNullityToModuloLinearityProvedIsFalse :
      crossTermNullityToModuloLinearityProved ≡ false

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
      NullClassStabilityTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationNullClassStabilityBoundary public

canonicalUnificationNullClassStabilityBoundary :
  UnificationNullClassStabilityBoundary
canonicalUnificationNullClassStabilityBoundary =
  record
    { importedSupport =
        canonicalNullClassStabilityImportedSupport
    ; targetRows =
        canonicalNullClassStabilityTargetRows
    ; targetRowCount =
        16
    ; targetRowCountIs16 =
        refl
    ; targetRowCountMatchesRows =
        refl
    ; nullRepresentativeRelationDefined =
        false
    ; nullRepresentativeRelationDefinedIsFalse =
        refl
    ; zeroClosureProved =
        false
    ; zeroClosureProvedIsFalse =
        refl
    ; additionClosureProved =
        false
    ; additionClosureProvedIsFalse =
        refl
    ; inverseClosureProved =
        false
    ; inverseClosureProvedIsFalse =
        refl
    ; scalarClosureProved =
        false
    ; scalarClosureProvedIsFalse =
        refl
    ; representativeInvarianceProved =
        false
    ; representativeInvarianceProvedIsFalse =
        refl
    ; gluingOperatorStabilityProved =
        false
    ; gluingOperatorStabilityProvedIsFalse =
        refl
    ; nullPredicateToQuotientEqualityTransportProved =
        false
    ; nullPredicateToQuotientEqualityTransportProvedIsFalse =
        refl
    ; crossTermNullityToModuloLinearityProved =
        false
    ; crossTermNullityToModuloLinearityProvedIsFalse =
        refl
    ; trueQuotientLinearityProved =
        false
    ; trueQuotientLinearityProvedIsFalse =
        refl
    ; fourPointCancellationProved =
        false
    ; fourPointCancellationProvedIsFalse =
        refl
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        refl
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        refl
    ; terminalUnificationPromotion =
        false
    ; terminalUnificationPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; allPromotionFlagsFalse =
        true
    ; allPromotionFlagsFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        nullClassStabilityTerminalPromotionAuthorityImpossible
    ; notes =
        "child boundary for null-class operation and G-stability"
      ∷ "explicit blockers: representative relation, operation stability, G-stability, null-to-equality transport"
      ∷ "cross-term nullity can imply modulo-null linearity only after these obligations are proved"
      ∷ "all unification and Clay promotion flags remain false"
      ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalNullClassRepresentativeRelationStillMissing :
  nullRepresentativeRelationDefined
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassRepresentativeRelationStillMissing =
  refl

canonicalNullClassAdditionClosureStillOpen :
  additionClosureProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassAdditionClosureStillOpen =
  refl

canonicalNullClassScalarClosureStillOpen :
  scalarClosureProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassScalarClosureStillOpen =
  refl

canonicalNullClassRepresentativeInvarianceStillOpen :
  representativeInvarianceProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassRepresentativeInvarianceStillOpen =
  refl

canonicalNullClassGluingStabilityStillOpen :
  gluingOperatorStabilityProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassGluingStabilityStillOpen =
  refl

canonicalNullClassTransportToQuotientEqualityStillOpen :
  nullPredicateToQuotientEqualityTransportProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassTransportToQuotientEqualityStillOpen =
  refl

canonicalNullClassCrossTermToModuloLinearityStillOpen :
  crossTermNullityToModuloLinearityProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassCrossTermToModuloLinearityStillOpen =
  refl

canonicalNullClassTrueQuotientLinearityStillOpen :
  trueQuotientLinearityProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassTrueQuotientLinearityStillOpen =
  refl

canonicalNullClassFourPointCancellationStillOpen :
  fourPointCancellationProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassFourPointCancellationStillOpen =
  refl

canonicalNullClassParallelogramStillOpen :
  parallelogramProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassParallelogramStillOpen =
  refl

canonicalNullClassQuadraticEmergenceStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassQuadraticEmergenceStillBlocked =
  refl

canonicalNullClassTerminalPromotionFalse :
  terminalUnificationPromotion
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassTerminalPromotionFalse =
  refl

canonicalNullClassClayPromotionFalse :
  clayPromotion
    canonicalUnificationNullClassStabilityBoundary
  ≡ false
canonicalNullClassClayPromotionFalse =
  refl
