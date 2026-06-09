module DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary where

-- Boundary for the actual U-1a cross-term nullity theorem target.
--
-- Target:
--
--   G(s1 + s2) - G(s1) - G(s2) lies in the null class.
--
-- This file records the theorem shape that downstream U-1a consumers need,
-- while consuming the existing fail-closed child surfaces for cross-term
-- null class, null stability, null-to-quotient equality transport, and
-- modulo-null gluing linearity.  It does not prove the theorem and does not
-- promote four-point cancellation, parallelogram, quadratic emergence, or
-- terminal unification.

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
import DASHI.Physics.Closure.UnificationNullClassStabilityBoundary
  as NullStability
import DASHI.Physics.Closure.UnificationNullToQuotientEqualityTransportBoundary
  as NullTransport
import DASHI.Physics.Closure.UnificationGluingModuloNullLinearityCompositeBoundary
  as ModuloNull

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- The actual theorem target.

actualU1aCrossTerm :
  (V : U1a.AdmissibleDefectQuotientVBoundary) →
  U1a.GluingOperatorGBoundary V →
  (U1a.DefectQuotientV V → U1a.DefectQuotientV V) →
  U1a.DefectQuotientV V →
  U1a.DefectQuotientV V →
  U1a.DefectQuotientV V
actualU1aCrossTerm V G-boundary -V_ s1 s2 =
  U1a._+V_ V
    (U1a._+V_ V
      (U1a.G G-boundary (U1a._+V_ V s1 s2))
      (-V_ (U1a.G G-boundary s1)))
    (-V_ (U1a.G G-boundary s2))

record U1aCrossTermNullityTheoremTarget
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    -V_ :
      U1a.DefectQuotientV V → U1a.DefectQuotientV V

    nullClass :
      U1a.DefectQuotientV V → Set

    theoremTarget :
      (s1 s2 : U1a.DefectQuotientV V) →
      nullClass (actualU1aCrossTerm V G-boundary -V_ s1 s2)

    theoremTargetText :
      String

    theoremTargetTextIsCanonical :
      theoremTargetText
      ≡ "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"

open U1aCrossTermNullityTheoremTarget public

record U1aCrossTermNullityRepresentativeInvarianceObligation
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    representativeEquivalent :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      Set

    nullClass :
      U1a.DefectQuotientV V → Set

    representativeInvarianceTarget :
      (x y : U1a.DefectQuotientV V) →
      representativeEquivalent x y →
      nullClass x →
      nullClass y

    gluingRepresentativeInvarianceTarget :
      (x y : U1a.DefectQuotientV V) →
      representativeEquivalent x y →
      representativeEquivalent
        (U1a.G G-boundary x)
        (U1a.G G-boundary y)

open U1aCrossTermNullityRepresentativeInvarianceObligation public

------------------------------------------------------------------------
-- Imported support.

record CrossTermNullityTheoremImportedSupport : Setω where
  field
    crossTermNullClassBoundary :
      CrossTerm.UnificationGluingCrossTermNullClassBoundary

    nullClassStabilityBoundary :
      NullStability.UnificationNullClassStabilityBoundary

    nullToQuotientTransportBoundary :
      NullTransport.UnificationNullToQuotientEqualityTransportBoundary

    moduloNullLinearityCompositeBoundary :
      ModuloNull.UnificationGluingModuloNullLinearityCompositeBoundary

    crossTermExpressionRecorded :
      CrossTerm.crossTermExpressionRecorded crossTermNullClassBoundary
      ≡ true

    crossTermRepresentativeInvarianceStillOpen :
      CrossTerm.representativeInvarianceProved crossTermNullClassBoundary
      ≡ false

    crossTermNullStabilityStillOpen :
      CrossTerm.nullClassStabilityProved crossTermNullClassBoundary
      ≡ false

    parentCrossTermNullityStillOpen :
      CrossTerm.crossTermNullClassTheoremProved crossTermNullClassBoundary
      ≡ false

    stabilityRepresentativeInvarianceStillOpen :
      NullStability.representativeInvarianceProved
        nullClassStabilityBoundary
        ≡ false

    stabilityGluingStillOpen :
      NullStability.gluingOperatorStabilityProved
        nullClassStabilityBoundary
        ≡ false

    stabilityNullToQuotientStillOpen :
      NullStability.nullPredicateToQuotientEqualityTransportProved
        nullClassStabilityBoundary
        ≡ false

    transportNullToZeroStillOpen :
      NullTransport.nullToZeroBridgeProved
        nullToQuotientTransportBoundary
        ≡ false

    transportRepresentativeInvarianceStillOpen :
      NullTransport.representativeInvarianceProved
        nullToQuotientTransportBoundary
        ≡ false

    transportCrossTermToModuloLinearityStillOpen :
      NullTransport.crossTermNullToModuloLinearityProved
        nullToQuotientTransportBoundary
        ≡ false

    moduloRepresentativeInvarianceStillOpen :
      ModuloNull.representativeInvarianceProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloCrossTermNullTransportStillOpen :
      ModuloNull.crossTermNullTransportProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloQuotientEqualityStillOpen :
      ModuloNull.quotientEqualityProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloNullGluingLinearityStillOpen :
      ModuloNull.moduloNullGluingLinearityProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloFourPointConsumerStillOpen :
      ModuloNull.actualFourPointCancellationProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloParallelogramStillOpen :
      ModuloNull.parallelogramProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloQuadraticStillBlocked :
      ModuloNull.quadraticEmergenceProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloTerminalPromotionFalse :
      ModuloNull.terminalUnificationPromotion
        moduloNullLinearityCompositeBoundary
        ≡ false

open CrossTermNullityTheoremImportedSupport public

canonicalCrossTermNullityTheoremImportedSupport :
  CrossTermNullityTheoremImportedSupport
canonicalCrossTermNullityTheoremImportedSupport =
  record
    { crossTermNullClassBoundary =
        CrossTerm.canonicalUnificationGluingCrossTermNullClassBoundary
    ; nullClassStabilityBoundary =
        NullStability.canonicalUnificationNullClassStabilityBoundary
    ; nullToQuotientTransportBoundary =
        NullTransport.canonicalUnificationNullToQuotientEqualityTransportBoundary
    ; moduloNullLinearityCompositeBoundary =
        ModuloNull.canonicalUnificationGluingModuloNullLinearityCompositeBoundary
    ; crossTermExpressionRecorded =
        CrossTerm.canonicalCrossTermExpressionRecorded
    ; crossTermRepresentativeInvarianceStillOpen =
        CrossTerm.canonicalCrossTermRepresentativeInvarianceStillOpen
    ; crossTermNullStabilityStillOpen =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; parentCrossTermNullityStillOpen =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; stabilityRepresentativeInvarianceStillOpen =
        NullStability.canonicalNullClassRepresentativeInvarianceStillOpen
    ; stabilityGluingStillOpen =
        NullStability.canonicalNullClassGluingStabilityStillOpen
    ; stabilityNullToQuotientStillOpen =
        NullStability.canonicalNullClassTransportToQuotientEqualityStillOpen
    ; transportNullToZeroStillOpen =
        NullTransport.canonicalNullToZeroBridgeStillFalse
    ; transportRepresentativeInvarianceStillOpen =
        NullTransport.canonicalRepresentativeInvarianceStillFalse
    ; transportCrossTermToModuloLinearityStillOpen =
        NullTransport.canonicalCrossTermNullToModuloLinearityStillFalse
    ; moduloRepresentativeInvarianceStillOpen =
        ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen
    ; moduloCrossTermNullTransportStillOpen =
        ModuloNull.canonicalModuloNullCrossTermNullTransportStillOpen
    ; moduloQuotientEqualityStillOpen =
        ModuloNull.canonicalModuloNullQuotientEqualityStillOpen
    ; moduloNullGluingLinearityStillOpen =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; moduloFourPointConsumerStillOpen =
        ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen
    ; moduloParallelogramStillOpen =
        ModuloNull.canonicalModuloNullParallelogramStillOpen
    ; moduloQuadraticStillBlocked =
        ModuloNull.canonicalModuloNullQuadraticStillBlocked
    ; moduloTerminalPromotionFalse =
        ModuloNull.canonicalModuloNullTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Target rows.

data CrossTermNullityTheoremStage : Set where
  parentCrossTermBoundaryImported :
    CrossTermNullityTheoremStage

  nullStabilityBoundaryImported :
    CrossTermNullityTheoremStage

  nullTransportBoundaryImported :
    CrossTermNullityTheoremStage

  moduloNullCompositeImported :
    CrossTermNullityTheoremStage

  actualTheoremTargetRecordedStage :
    CrossTermNullityTheoremStage

  representativeInvarianceConsumer :
    CrossTermNullityTheoremStage

  nullStabilityConsumer :
    CrossTermNullityTheoremStage

  quotientTransportConsumer :
    CrossTermNullityTheoremStage

  moduloNullLinearityConsumer :
    CrossTermNullityTheoremStage

  fourPointConsumer :
    CrossTermNullityTheoremStage

  parallelogramConsumer :
    CrossTermNullityTheoremStage

  quadraticConsumer :
    CrossTermNullityTheoremStage

  terminalPromotionGate :
    CrossTermNullityTheoremStage

data CrossTermNullityTheoremStatus : Set where
  importedBoundary :
    CrossTermNullityTheoremStatus

  targetRecorded :
    CrossTermNullityTheoremStatus

  prerequisiteOpen :
    CrossTermNullityTheoremStatus

  theoremOpen :
    CrossTermNullityTheoremStatus

  downstreamBlocked :
    CrossTermNullityTheoremStatus

  promotionHeld :
    CrossTermNullityTheoremStatus

canonicalCrossTermNullityTheoremStatus :
  CrossTermNullityTheoremStage → CrossTermNullityTheoremStatus
canonicalCrossTermNullityTheoremStatus parentCrossTermBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus nullStabilityBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus nullTransportBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus moduloNullCompositeImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus actualTheoremTargetRecordedStage =
  targetRecorded
canonicalCrossTermNullityTheoremStatus representativeInvarianceConsumer =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus nullStabilityConsumer =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus quotientTransportConsumer =
  theoremOpen
canonicalCrossTermNullityTheoremStatus moduloNullLinearityConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus fourPointConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus parallelogramConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus quadraticConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus terminalPromotionGate =
  promotionHeld

data CrossTermNullityTheoremBlocker : Set where
  noBlockerForImportedBoundary :
    CrossTermNullityTheoremBlocker

  noBlockerForRecordedTarget :
    CrossTermNullityTheoremBlocker

  missingRepresentativeInvariance :
    CrossTermNullityTheoremBlocker

  missingNullClassStability :
    CrossTermNullityTheoremBlocker

  missingNullToQuotientTransport :
    CrossTermNullityTheoremBlocker

  missingModuloNullLinearityConsumer :
    CrossTermNullityTheoremBlocker

  missingFourPointConsumer :
    CrossTermNullityTheoremBlocker

  missingParallelogramConsumer :
    CrossTermNullityTheoremBlocker

  missingQuadraticConsumer :
    CrossTermNullityTheoremBlocker

  noTerminalPromotionAuthority :
    CrossTermNullityTheoremBlocker

canonicalCrossTermNullityTheoremBlocker :
  CrossTermNullityTheoremStage → CrossTermNullityTheoremBlocker
canonicalCrossTermNullityTheoremBlocker parentCrossTermBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker nullStabilityBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker nullTransportBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker moduloNullCompositeImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker actualTheoremTargetRecordedStage =
  noBlockerForRecordedTarget
canonicalCrossTermNullityTheoremBlocker representativeInvarianceConsumer =
  missingRepresentativeInvariance
canonicalCrossTermNullityTheoremBlocker nullStabilityConsumer =
  missingNullClassStability
canonicalCrossTermNullityTheoremBlocker quotientTransportConsumer =
  missingNullToQuotientTransport
canonicalCrossTermNullityTheoremBlocker moduloNullLinearityConsumer =
  missingModuloNullLinearityConsumer
canonicalCrossTermNullityTheoremBlocker fourPointConsumer =
  missingFourPointConsumer
canonicalCrossTermNullityTheoremBlocker parallelogramConsumer =
  missingParallelogramConsumer
canonicalCrossTermNullityTheoremBlocker quadraticConsumer =
  missingQuadraticConsumer
canonicalCrossTermNullityTheoremBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record CrossTermNullityTheoremRow : Set where
  field
    stage :
      CrossTermNullityTheoremStage

    status :
      CrossTermNullityTheoremStatus

    statusIsCanonical :
      status ≡ canonicalCrossTermNullityTheoremStatus stage

    blocker :
      CrossTermNullityTheoremBlocker

    blockerIsCanonical :
      blocker ≡ canonicalCrossTermNullityTheoremBlocker stage

    targetOrConsumer :
      String

    importedSurface :
      String

    provedOrPromotedHere :
      Bool

    provedOrPromotedHereIsFalse :
      provedOrPromotedHere ≡ false

open CrossTermNullityTheoremRow public

mkCrossTermNullityTheoremRow :
  CrossTermNullityTheoremStage →
  String →
  String →
  CrossTermNullityTheoremRow
mkCrossTermNullityTheoremRow stage targetOrConsumer importedSurface =
  record
    { stage =
        stage
    ; status =
        canonicalCrossTermNullityTheoremStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalCrossTermNullityTheoremBlocker stage
    ; blockerIsCanonical =
        refl
    ; targetOrConsumer =
        targetOrConsumer
    ; importedSurface =
        importedSurface
    ; provedOrPromotedHere =
        false
    ; provedOrPromotedHereIsFalse =
        refl
    }

canonicalCrossTermNullityTheoremRows :
  List CrossTermNullityTheoremRow
canonicalCrossTermNullityTheoremRows =
  mkCrossTermNullityTheoremRow
    parentCrossTermBoundaryImported
    "consume recorded expression G(s1+s2)-G(s1)-G(s2)"
    "UnificationGluingCrossTermNullClassBoundary"
  ∷ mkCrossTermNullityTheoremRow
    nullStabilityBoundaryImported
    "consume null-class operation and G-stability blockers"
    "UnificationNullClassStabilityBoundary"
  ∷ mkCrossTermNullityTheoremRow
    nullTransportBoundaryImported
    "consume null predicate to quotient equality transport blockers"
    "UnificationNullToQuotientEqualityTransportBoundary"
  ∷ mkCrossTermNullityTheoremRow
    moduloNullCompositeImported
    "consume representative invariance, cross-term transport, quotient equality, and modulo-null route"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    actualTheoremTargetRecordedStage
    "actual target: forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"
    "U1aCrossTermNullityTheoremTarget"
  ∷ mkCrossTermNullityTheoremRow
    representativeInvarianceConsumer
    "representatives must not change cross-term nullity"
    "NullStability, NullTransport, ModuloNull"
  ∷ mkCrossTermNullityTheoremRow
    nullStabilityConsumer
    "null class must be stable under quotient operations and G"
    "UnificationNullClassStabilityBoundary"
  ∷ mkCrossTermNullityTheoremRow
    quotientTransportConsumer
    "null cross-term must transport to quotient equality with zero"
    "UnificationNullToQuotientEqualityTransportBoundary"
  ∷ mkCrossTermNullityTheoremRow
    moduloNullLinearityConsumer
    "cross-term nullity must feed modulo-null gluing linearity"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    fourPointConsumer
    "four-point cancellation consumes the modulo-null route only after the theorem is supplied"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    parallelogramConsumer
    "parallelogram remains downstream of actual four-point cancellation"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    quadraticConsumer
    "quadratic emergence remains downstream of parallelogram"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    terminalPromotionGate
    "terminal unification promotion remains held"
    "all imported promotion gates"
  ∷ []

canonicalCrossTermNullityTheoremRowCount : Nat
canonicalCrossTermNullityTheoremRowCount =
  listLength canonicalCrossTermNullityTheoremRows

canonicalCrossTermNullityTheoremRowCountIs13 :
  canonicalCrossTermNullityTheoremRowCount ≡ 13
canonicalCrossTermNullityTheoremRowCountIs13 =
  refl

------------------------------------------------------------------------
-- Boundary.

data CrossTermNullityTerminalPromotionAuthority : Set where

crossTermNullityTerminalPromotionAuthorityImpossible :
  CrossTermNullityTerminalPromotionAuthority →
  ⊥
crossTermNullityTerminalPromotionAuthorityImpossible ()

record UnificationCrossTermNullityTheoremBoundary : Setω where
  field
    importedSupport :
      CrossTermNullityTheoremImportedSupport

    theoremRows :
      List CrossTermNullityTheoremRow

    theoremRowCount :
      Nat

    theoremRowCountIs13 :
      theoremRowCount ≡ 13

    theoremRowCountMatchesRows :
      theoremRowCount ≡ listLength theoremRows

    actualTheoremTargetRecorded :
      Bool

    actualTheoremTargetRecordedIsTrue :
      actualTheoremTargetRecorded ≡ true

    theoremTargetText :
      String

    theoremTargetTextIsCanonical :
      theoremTargetText
      ≡ "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"

    representativeInvarianceRecorded :
      Bool

    representativeInvarianceRecordedIsTrue :
      representativeInvarianceRecorded ≡ true

    nullStabilityRecorded :
      Bool

    nullStabilityRecordedIsTrue :
      nullStabilityRecorded ≡ true

    quotientTransportRecorded :
      Bool

    quotientTransportRecordedIsTrue :
      quotientTransportRecorded ≡ true

    moduloNullLinearityConsumerRecorded :
      Bool

    moduloNullLinearityConsumerRecordedIsTrue :
      moduloNullLinearityConsumerRecorded ≡ true

    fourPointConsumerRecorded :
      Bool

    fourPointConsumerRecordedIsTrue :
      fourPointConsumerRecorded ≡ true

    representativeInvarianceProved :
      Bool

    representativeInvarianceProvedIsFalse :
      representativeInvarianceProved ≡ false

    nullStabilityProved :
      Bool

    nullStabilityProvedIsFalse :
      nullStabilityProved ≡ false

    quotientTransportProved :
      Bool

    quotientTransportProvedIsFalse :
      quotientTransportProved ≡ false

    crossTermNullityTheoremProved :
      Bool

    crossTermNullityTheoremProvedIsFalse :
      crossTermNullityTheoremProved ≡ false

    moduloNullLinearityProved :
      Bool

    moduloNullLinearityProvedIsFalse :
      moduloNullLinearityProved ≡ false

    fourPointConsumerProved :
      Bool

    fourPointConsumerProvedIsFalse :
      fourPointConsumerProved ≡ false

    parallelogramProved :
      Bool

    parallelogramProvedIsFalse :
      parallelogramProved ≡ false

    quadraticEmergenceProved :
      Bool

    quadraticEmergenceProvedIsFalse :
      quadraticEmergenceProved ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse :
      Bool

    allTheoremFourPointParallelogramQuadraticTerminalFlagsFalseIsTrue :
      allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse ≡ true

    promotionAuthorityImpossible :
      CrossTermNullityTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationCrossTermNullityTheoremBoundary public

canonicalUnificationCrossTermNullityTheoremBoundary :
  UnificationCrossTermNullityTheoremBoundary
canonicalUnificationCrossTermNullityTheoremBoundary =
  record
    { importedSupport =
        canonicalCrossTermNullityTheoremImportedSupport
    ; theoremRows =
        canonicalCrossTermNullityTheoremRows
    ; theoremRowCount =
        13
    ; theoremRowCountIs13 =
        refl
    ; theoremRowCountMatchesRows =
        refl
    ; actualTheoremTargetRecorded =
        true
    ; actualTheoremTargetRecordedIsTrue =
        refl
    ; theoremTargetText =
        "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"
    ; theoremTargetTextIsCanonical =
        refl
    ; representativeInvarianceRecorded =
        true
    ; representativeInvarianceRecordedIsTrue =
        refl
    ; nullStabilityRecorded =
        true
    ; nullStabilityRecordedIsTrue =
        refl
    ; quotientTransportRecorded =
        true
    ; quotientTransportRecordedIsTrue =
        refl
    ; moduloNullLinearityConsumerRecorded =
        true
    ; moduloNullLinearityConsumerRecordedIsTrue =
        refl
    ; fourPointConsumerRecorded =
        true
    ; fourPointConsumerRecordedIsTrue =
        refl
    ; representativeInvarianceProved =
        false
    ; representativeInvarianceProvedIsFalse =
        ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen
    ; nullStabilityProved =
        false
    ; nullStabilityProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; quotientTransportProved =
        false
    ; quotientTransportProvedIsFalse =
        NullTransport.canonicalNullToZeroBridgeStillFalse
    ; crossTermNullityTheoremProved =
        false
    ; crossTermNullityTheoremProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; moduloNullLinearityProved =
        false
    ; moduloNullLinearityProvedIsFalse =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; fourPointConsumerProved =
        false
    ; fourPointConsumerProvedIsFalse =
        ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        ModuloNull.canonicalModuloNullParallelogramStillOpen
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        ModuloNull.canonicalModuloNullQuadraticStillBlocked
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        ModuloNull.canonicalModuloNullTerminalPromotionFalse
    ; allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse =
        true
    ; allTheoremFourPointParallelogramQuadraticTerminalFlagsFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        crossTermNullityTerminalPromotionAuthorityImpossible
    ; notes =
        "Actual U-1a theorem target is recorded as nullClass (G(s1+s2)-G(s1)-G(s2))."
      ∷ "Representative invariance, null stability, quotient transport, and modulo-null linearity are consumed from existing fail-closed boundaries."
      ∷ "The four-point route is recorded as a consumer only."
      ∷ "Theorem, four-point, parallelogram, quadratic, and terminal promotion flags remain false."
      ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalCrossTermNullityTheoremRowsCountIs13 :
  theoremRowCount canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ 13
canonicalCrossTermNullityTheoremRowsCountIs13 =
  refl

canonicalCrossTermNullityActualTargetRecorded :
  actualTheoremTargetRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityActualTargetRecorded =
  refl

canonicalCrossTermNullityRepresentativeInvarianceRecorded :
  representativeInvarianceRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityRepresentativeInvarianceRecorded =
  refl

canonicalCrossTermNullityNullStabilityRecorded :
  nullStabilityRecorded canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityNullStabilityRecorded =
  refl

canonicalCrossTermNullityQuotientTransportRecorded :
  quotientTransportRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityQuotientTransportRecorded =
  refl

canonicalCrossTermNullityModuloNullLinearityConsumerRecorded :
  moduloNullLinearityConsumerRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityModuloNullLinearityConsumerRecorded =
  refl

canonicalCrossTermNullityFourPointConsumerRecorded :
  fourPointConsumerRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityFourPointConsumerRecorded =
  refl

canonicalCrossTermNullityRepresentativeInvarianceStillOpen :
  representativeInvarianceProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityRepresentativeInvarianceStillOpen =
  ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen

canonicalCrossTermNullityNullStabilityStillOpen :
  nullStabilityProved canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityNullStabilityStillOpen =
  CrossTerm.canonicalCrossTermNullClassStabilityStillOpen

canonicalCrossTermNullityQuotientTransportStillOpen :
  quotientTransportProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityQuotientTransportStillOpen =
  NullTransport.canonicalNullToZeroBridgeStillFalse

canonicalCrossTermNullityTheoremStillOpen :
  crossTermNullityTheoremProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityTheoremStillOpen =
  CrossTerm.canonicalCrossTermNullClassTheoremStillOpen

canonicalCrossTermNullityModuloNullLinearityStillOpen :
  moduloNullLinearityProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityModuloNullLinearityStillOpen =
  ModuloNull.canonicalModuloNullGluingLinearityStillOpen

canonicalCrossTermNullityFourPointConsumerStillOpen :
  fourPointConsumerProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityFourPointConsumerStillOpen =
  ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen

canonicalCrossTermNullityParallelogramStillOpen :
  parallelogramProved canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityParallelogramStillOpen =
  ModuloNull.canonicalModuloNullParallelogramStillOpen

canonicalCrossTermNullityQuadraticStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityQuadraticStillBlocked =
  ModuloNull.canonicalModuloNullQuadraticStillBlocked

canonicalCrossTermNullityTerminalPromotionFalse :
  terminalPromotion canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityTerminalPromotionFalse =
  ModuloNull.canonicalModuloNullTerminalPromotionFalse

canonicalCrossTermNullityTheoremPromotionBundleFalse :
  allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityTheoremPromotionBundleFalse =
  refl
