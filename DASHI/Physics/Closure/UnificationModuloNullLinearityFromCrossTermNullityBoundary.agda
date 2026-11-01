module DASHI.Physics.Closure.UnificationModuloNullLinearityFromCrossTermNullityBoundary where

-- Boundary composite:
--
--   UnificationCrossTermNullityTheoremBoundary
--   + UnificationGluingModuloNullLinearityCompositeBoundary
--   + UnificationFourPointCancellationFromCrossTermNullityBoundary
--   -> modulo-null linearity route
--   -> four-point cancellation route.
--
-- This surface records the exact U-1a ladder requested by the unification
-- lane:
--
--   cross-term nullity
--   -> null-to-quotient transport
--   -> modulo-null gluing linearity
--   -> additive/polarization four-point consumer.
--
-- It is deliberately fail-closed.  The imported boundaries record the
-- sockets and canonical route, but none of the actual cross-term nullity,
-- modulo-null linearity, four-point cancellation, parallelogram, quadratic
-- emergence, terminal unification, or Clay promotion theorems are proved
-- here.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary
  as CrossTerm
import DASHI.Physics.Closure.UnificationGluingModuloNullLinearityCompositeBoundary
  as ModuloNull
import DASHI.Physics.Closure.UnificationFourPointCancellationFromCrossTermNullityBoundary
  as FourPoint

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support.

record ModuloNullFromCrossTermImportedSupport : Setω where
  field
    crossTermNullityBoundary :
      CrossTerm.UnificationCrossTermNullityTheoremBoundary

    moduloNullLinearityBoundary :
      ModuloNull.UnificationGluingModuloNullLinearityCompositeBoundary

    fourPointCancellationRouteBoundary :
      FourPoint.UnificationFourPointCancellationFromCrossTermNullityBoundary

    crossTermActualTargetRecorded :
      CrossTerm.actualTheoremTargetRecorded crossTermNullityBoundary
      ≡ true

    crossTermModuloConsumerRecorded :
      CrossTerm.moduloNullLinearityConsumerRecorded
        crossTermNullityBoundary
      ≡ true

    crossTermFourPointConsumerRecorded :
      CrossTerm.fourPointConsumerRecorded crossTermNullityBoundary
      ≡ true

    crossTermTheoremStillOpen :
      CrossTerm.crossTermNullityTheoremProved crossTermNullityBoundary
      ≡ false

    crossTermModuloLinearityStillOpen :
      CrossTerm.moduloNullLinearityProved crossTermNullityBoundary
      ≡ false

    crossTermFourPointStillOpen :
      CrossTerm.fourPointConsumerProved crossTermNullityBoundary
      ≡ false

    crossTermTerminalPromotionFalse :
      CrossTerm.terminalPromotion crossTermNullityBoundary
      ≡ false

    moduloCrossTermTransportRecorded :
      ModuloNull.crossTermNullTransportRecorded
        moduloNullLinearityBoundary
      ≡ true

    moduloQuotientEqualityRecorded :
      ModuloNull.quotientEqualityRecorded moduloNullLinearityBoundary
      ≡ true

    moduloFourPointRouteRecorded :
      ModuloNull.fourPointCancellationRouteRecorded
        moduloNullLinearityBoundary
      ≡ true

    moduloCrossTermTransportStillOpen :
      ModuloNull.crossTermNullTransportProved
        moduloNullLinearityBoundary
      ≡ false

    moduloNullLinearityStillOpen :
      ModuloNull.moduloNullGluingLinearityProved
        moduloNullLinearityBoundary
      ≡ false

    moduloActualFourPointStillOpen :
      ModuloNull.actualFourPointCancellationProved
        moduloNullLinearityBoundary
      ≡ false

    moduloTerminalPromotionFalse :
      ModuloNull.terminalUnificationPromotion moduloNullLinearityBoundary
      ≡ false

    fourPointModuloRouteRecorded :
      FourPoint.moduloNullLinearityRouteRecorded
        fourPointCancellationRouteBoundary
      ≡ true

    fourPointPolarizationResidualRecorded :
      FourPoint.polarizationFourPointResidualRecorded
        fourPointCancellationRouteBoundary
      ≡ true

    fourPointParallelogramConsumerRecorded :
      FourPoint.parallelogramConsumerRecorded
        fourPointCancellationRouteBoundary
      ≡ true

    fourPointModuloLinearityStillOpen :
      FourPoint.moduloNullLinearityProved
        fourPointCancellationRouteBoundary
      ≡ false

    fourPointCancellationStillOpen :
      FourPoint.fourPointCancellationProved
        fourPointCancellationRouteBoundary
      ≡ false

    fourPointParallelogramStillOpen :
      FourPoint.parallelogramProved fourPointCancellationRouteBoundary
      ≡ false

    fourPointQuadraticStillBlocked :
      FourPoint.quadraticEmergenceProved
        fourPointCancellationRouteBoundary
      ≡ false

    fourPointTerminalPromotionFalse :
      FourPoint.terminalUnificationPromotion
        fourPointCancellationRouteBoundary
      ≡ false

open ModuloNullFromCrossTermImportedSupport public

canonicalModuloNullFromCrossTermImportedSupport :
  ModuloNullFromCrossTermImportedSupport
canonicalModuloNullFromCrossTermImportedSupport =
  record
    { crossTermNullityBoundary =
        CrossTerm.canonicalUnificationCrossTermNullityTheoremBoundary
    ; moduloNullLinearityBoundary =
        ModuloNull.canonicalUnificationGluingModuloNullLinearityCompositeBoundary
    ; fourPointCancellationRouteBoundary =
        FourPoint.canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
    ; crossTermActualTargetRecorded =
        CrossTerm.canonicalCrossTermNullityActualTargetRecorded
    ; crossTermModuloConsumerRecorded =
        CrossTerm.canonicalCrossTermNullityModuloNullLinearityConsumerRecorded
    ; crossTermFourPointConsumerRecorded =
        CrossTerm.canonicalCrossTermNullityFourPointConsumerRecorded
    ; crossTermTheoremStillOpen =
        CrossTerm.canonicalCrossTermNullityTheoremStillOpen
    ; crossTermModuloLinearityStillOpen =
        CrossTerm.canonicalCrossTermNullityModuloNullLinearityStillOpen
    ; crossTermFourPointStillOpen =
        CrossTerm.canonicalCrossTermNullityFourPointConsumerStillOpen
    ; crossTermTerminalPromotionFalse =
        CrossTerm.canonicalCrossTermNullityTerminalPromotionFalse
    ; moduloCrossTermTransportRecorded =
        ModuloNull.canonicalModuloNullCrossTermNullTransportRecorded
    ; moduloQuotientEqualityRecorded =
        ModuloNull.canonicalModuloNullQuotientEqualityRecorded
    ; moduloFourPointRouteRecorded =
        ModuloNull.canonicalModuloNullFourPointRouteRecorded
    ; moduloCrossTermTransportStillOpen =
        ModuloNull.canonicalModuloNullCrossTermNullTransportStillOpen
    ; moduloNullLinearityStillOpen =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; moduloActualFourPointStillOpen =
        ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen
    ; moduloTerminalPromotionFalse =
        ModuloNull.canonicalModuloNullTerminalPromotionFalse
    ; fourPointModuloRouteRecorded =
        FourPoint.canonicalModuloNullLinearityRouteRecorded
    ; fourPointPolarizationResidualRecorded =
        FourPoint.canonicalPolarizationFourPointResidualRecorded
    ; fourPointParallelogramConsumerRecorded =
        FourPoint.canonicalParallelogramConsumerRecorded
    ; fourPointModuloLinearityStillOpen =
        FourPoint.canonicalRouteModuloNullLinearityStillOpen
    ; fourPointCancellationStillOpen =
        FourPoint.canonicalRouteFourPointCancellationStillOpen
    ; fourPointParallelogramStillOpen =
        FourPoint.canonicalRouteParallelogramStillOpen
    ; fourPointQuadraticStillBlocked =
        FourPoint.canonicalRouteQuadraticStillBlocked
    ; fourPointTerminalPromotionFalse =
        FourPoint.canonicalRouteTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Composite ladder.

data ModuloNullFromCrossTermStage : Set where
  crossTermTargetImported :
    ModuloNullFromCrossTermStage

  crossTermNullityTheoremInput :
    ModuloNullFromCrossTermStage

  nullToQuotientTransportInput :
    ModuloNullFromCrossTermStage

  moduloNullLinearityTransport :
    ModuloNullFromCrossTermStage

  moduloNullLinearityRoute :
    ModuloNullFromCrossTermStage

  additiveFunctionalConsumer :
    ModuloNullFromCrossTermStage

  polarizationFourPointConsumer :
    ModuloNullFromCrossTermStage

  fourPointCancellationRoute :
    ModuloNullFromCrossTermStage

  actualFourPointCancellation :
    ModuloNullFromCrossTermStage

  parallelogramConsumer :
    ModuloNullFromCrossTermStage

  quadraticEmergenceConsumer :
    ModuloNullFromCrossTermStage

  terminalPromotionGate :
    ModuloNullFromCrossTermStage

data ModuloNullFromCrossTermStatus : Set where
  importedBoundary :
    ModuloNullFromCrossTermStatus

  targetRecorded :
    ModuloNullFromCrossTermStatus

  theoremOpen :
    ModuloNullFromCrossTermStatus

  transportOpen :
    ModuloNullFromCrossTermStatus

  routeRecorded :
    ModuloNullFromCrossTermStatus

  consumerRecorded :
    ModuloNullFromCrossTermStatus

  downstreamBlocked :
    ModuloNullFromCrossTermStatus

  promotionHeld :
    ModuloNullFromCrossTermStatus

canonicalModuloNullFromCrossTermStatus :
  ModuloNullFromCrossTermStage → ModuloNullFromCrossTermStatus
canonicalModuloNullFromCrossTermStatus crossTermTargetImported =
  importedBoundary
canonicalModuloNullFromCrossTermStatus crossTermNullityTheoremInput =
  theoremOpen
canonicalModuloNullFromCrossTermStatus nullToQuotientTransportInput =
  transportOpen
canonicalModuloNullFromCrossTermStatus moduloNullLinearityTransport =
  transportOpen
canonicalModuloNullFromCrossTermStatus moduloNullLinearityRoute =
  routeRecorded
canonicalModuloNullFromCrossTermStatus additiveFunctionalConsumer =
  consumerRecorded
canonicalModuloNullFromCrossTermStatus polarizationFourPointConsumer =
  consumerRecorded
canonicalModuloNullFromCrossTermStatus fourPointCancellationRoute =
  routeRecorded
canonicalModuloNullFromCrossTermStatus actualFourPointCancellation =
  theoremOpen
canonicalModuloNullFromCrossTermStatus parallelogramConsumer =
  downstreamBlocked
canonicalModuloNullFromCrossTermStatus quadraticEmergenceConsumer =
  downstreamBlocked
canonicalModuloNullFromCrossTermStatus terminalPromotionGate =
  promotionHeld

data ModuloNullFromCrossTermBlocker : Set where
  noBlockerForImportedBoundary :
    ModuloNullFromCrossTermBlocker

  missingActualCrossTermNullity :
    ModuloNullFromCrossTermBlocker

  missingNullToQuotientTransport :
    ModuloNullFromCrossTermBlocker

  missingCrossTermNullTransport :
    ModuloNullFromCrossTermBlocker

  noBlockerForRecordedRoute :
    ModuloNullFromCrossTermBlocker

  noBlockerForRecordedConsumer :
    ModuloNullFromCrossTermBlocker

  missingActualFourPointCancellation :
    ModuloNullFromCrossTermBlocker

  missingParallelogramConsumer :
    ModuloNullFromCrossTermBlocker

  missingQuadraticEmergenceConsumer :
    ModuloNullFromCrossTermBlocker

  noTerminalPromotionAuthority :
    ModuloNullFromCrossTermBlocker

canonicalModuloNullFromCrossTermBlocker :
  ModuloNullFromCrossTermStage → ModuloNullFromCrossTermBlocker
canonicalModuloNullFromCrossTermBlocker crossTermTargetImported =
  noBlockerForImportedBoundary
canonicalModuloNullFromCrossTermBlocker crossTermNullityTheoremInput =
  missingActualCrossTermNullity
canonicalModuloNullFromCrossTermBlocker nullToQuotientTransportInput =
  missingNullToQuotientTransport
canonicalModuloNullFromCrossTermBlocker moduloNullLinearityTransport =
  missingCrossTermNullTransport
canonicalModuloNullFromCrossTermBlocker moduloNullLinearityRoute =
  noBlockerForRecordedRoute
canonicalModuloNullFromCrossTermBlocker additiveFunctionalConsumer =
  noBlockerForRecordedConsumer
canonicalModuloNullFromCrossTermBlocker polarizationFourPointConsumer =
  noBlockerForRecordedConsumer
canonicalModuloNullFromCrossTermBlocker fourPointCancellationRoute =
  noBlockerForRecordedRoute
canonicalModuloNullFromCrossTermBlocker actualFourPointCancellation =
  missingActualFourPointCancellation
canonicalModuloNullFromCrossTermBlocker parallelogramConsumer =
  missingParallelogramConsumer
canonicalModuloNullFromCrossTermBlocker quadraticEmergenceConsumer =
  missingQuadraticEmergenceConsumer
canonicalModuloNullFromCrossTermBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record ModuloNullFromCrossTermRow : Set where
  field
    stage :
      ModuloNullFromCrossTermStage

    status :
      ModuloNullFromCrossTermStatus

    statusIsCanonical :
      status ≡ canonicalModuloNullFromCrossTermStatus stage

    blocker :
      ModuloNullFromCrossTermBlocker

    blockerIsCanonical :
      blocker ≡ canonicalModuloNullFromCrossTermBlocker stage

    promotionContract :
      String

    importedSurface :
      String

    provedOrPromotedHere :
      Bool

    provedOrPromotedHereIsFalse :
      provedOrPromotedHere ≡ false

open ModuloNullFromCrossTermRow public

mkModuloNullFromCrossTermRow :
  ModuloNullFromCrossTermStage →
  String →
  String →
  ModuloNullFromCrossTermRow
mkModuloNullFromCrossTermRow stage promotionContract importedSurface =
  record
    { stage =
        stage
    ; status =
        canonicalModuloNullFromCrossTermStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalModuloNullFromCrossTermBlocker stage
    ; blockerIsCanonical =
        refl
    ; promotionContract =
        promotionContract
    ; importedSurface =
        importedSurface
    ; provedOrPromotedHere =
        false
    ; provedOrPromotedHereIsFalse =
        refl
    }

canonicalModuloNullFromCrossTermRows :
  List ModuloNullFromCrossTermRow
canonicalModuloNullFromCrossTermRows =
  mkModuloNullFromCrossTermRow
    crossTermTargetImported
    "import the canonical U-1a target nullClass (G(s1+s2)-G(s1)-G(s2))"
    "UnificationCrossTermNullityTheoremBoundary"
  ∷ mkModuloNullFromCrossTermRow
    crossTermNullityTheoremInput
    "actual cross-term nullity is the theorem input required before modulo-null linearity can be promoted"
    "CrossTerm.crossTermNullityTheoremProved"
  ∷ mkModuloNullFromCrossTermRow
    nullToQuotientTransportInput
    "null cross-term must transport to quotient equality with the null representative"
    "CrossTerm quotient transport and ModuloNull quotient equality guards"
  ∷ mkModuloNullFromCrossTermRow
    moduloNullLinearityTransport
    "cross-term nullity must feed the modulo-null gluing-linearity transport surface"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkModuloNullFromCrossTermRow
    moduloNullLinearityRoute
    "record G(s1+s2)=G(s1)+G(s2) modulo null once cross-term transport is supplied"
    "ModuloNull.moduloNullGluingLinearity route"
  ∷ mkModuloNullFromCrossTermRow
    additiveFunctionalConsumer
    "additive test functionals consume modulo-null linearity through T(x+y)-T(x)-T(y)"
    "UnificationFourPointCancellationFromCrossTermNullityBoundary"
  ∷ mkModuloNullFromCrossTermRow
    polarizationFourPointConsumer
    "polarization records Q(x+y)+Q(x-y)-2Q(x)-2Q(y) as the four-point residual"
    "FourPoint.polarizationFourPointResidualRecorded"
  ∷ mkModuloNullFromCrossTermRow
    fourPointCancellationRoute
    "route modulo-null linearity to the four-point cancellation theorem target without proving it"
    "FourPoint.moduloNullLinearityRouteRecorded"
  ∷ mkModuloNullFromCrossTermRow
    actualFourPointCancellation
    "actual four-point cancellation remains the downstream U-1 theorem output"
    "FourPoint.fourPointCancellationProved"
  ∷ mkModuloNullFromCrossTermRow
    parallelogramConsumer
    "parallelogram consumes actual four-point cancellation only after U-1 is proved"
    "FourPoint.parallelogramProved"
  ∷ mkModuloNullFromCrossTermRow
    quadraticEmergenceConsumer
    "quadratic emergence waits for the parallelogram/Jordan-von-Neumann chain"
    "FourPoint.quadraticEmergenceProved"
  ∷ mkModuloNullFromCrossTermRow
    terminalPromotionGate
    "terminal unification and Clay promotion remain held"
    "all imported terminal gates"
  ∷ []

canonicalModuloNullFromCrossTermRowCount : Nat
canonicalModuloNullFromCrossTermRowCount =
  listLength canonicalModuloNullFromCrossTermRows

canonicalModuloNullFromCrossTermRowCountIs12 :
  canonicalModuloNullFromCrossTermRowCount ≡ 12
canonicalModuloNullFromCrossTermRowCountIs12 =
  refl

------------------------------------------------------------------------
-- Boundary.

data ModuloNullFromCrossTermTerminalPromotionAuthority : Set where

moduloNullFromCrossTermTerminalPromotionAuthorityImpossible :
  ModuloNullFromCrossTermTerminalPromotionAuthority →
  ⊥
moduloNullFromCrossTermTerminalPromotionAuthorityImpossible ()

record UnificationModuloNullLinearityFromCrossTermNullityBoundary :
  Setω where
  field
    importedSupport :
      ModuloNullFromCrossTermImportedSupport

    promotionRows :
      List ModuloNullFromCrossTermRow

    promotionRowCount :
      Nat

    promotionRowCountIs12 :
      promotionRowCount ≡ 12

    promotionRowCountMatchesRows :
      promotionRowCount ≡ listLength promotionRows

    crossTermNullityTargetRecorded :
      Bool

    crossTermNullityTargetRecordedIsTrue :
      crossTermNullityTargetRecorded ≡ true

    crossTermToModuloNullLinearityRouteRecorded :
      Bool

    crossTermToModuloNullLinearityRouteRecordedIsTrue :
      crossTermToModuloNullLinearityRouteRecorded ≡ true

    moduloNullLinearityToFourPointRouteRecorded :
      Bool

    moduloNullLinearityToFourPointRouteRecordedIsTrue :
      moduloNullLinearityToFourPointRouteRecorded ≡ true

    additiveAndPolarizationConsumersRecorded :
      Bool

    additiveAndPolarizationConsumersRecordedIsTrue :
      additiveAndPolarizationConsumersRecorded ≡ true

    crossTermNullityTheoremProved :
      Bool

    crossTermNullityTheoremProvedIsFalse :
      crossTermNullityTheoremProved ≡ false

    moduloNullLinearityProved :
      Bool

    moduloNullLinearityProvedIsFalse :
      moduloNullLinearityProved ≡ false

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

    allUnificationPromotionFlagsFalse :
      Bool

    allUnificationPromotionFlagsFalseIsTrue :
      allUnificationPromotionFlagsFalse ≡ true

    promotionAuthorityImpossible :
      ModuloNullFromCrossTermTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationModuloNullLinearityFromCrossTermNullityBoundary public

canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary :
  UnificationModuloNullLinearityFromCrossTermNullityBoundary
canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary =
  record
    { importedSupport =
        canonicalModuloNullFromCrossTermImportedSupport
    ; promotionRows =
        canonicalModuloNullFromCrossTermRows
    ; promotionRowCount =
        12
    ; promotionRowCountIs12 =
        refl
    ; promotionRowCountMatchesRows =
        refl
    ; crossTermNullityTargetRecorded =
        true
    ; crossTermNullityTargetRecordedIsTrue =
        CrossTerm.canonicalCrossTermNullityActualTargetRecorded
    ; crossTermToModuloNullLinearityRouteRecorded =
        true
    ; crossTermToModuloNullLinearityRouteRecordedIsTrue =
        CrossTerm.canonicalCrossTermNullityModuloNullLinearityConsumerRecorded
    ; moduloNullLinearityToFourPointRouteRecorded =
        true
    ; moduloNullLinearityToFourPointRouteRecordedIsTrue =
        FourPoint.canonicalModuloNullLinearityRouteRecorded
    ; additiveAndPolarizationConsumersRecorded =
        true
    ; additiveAndPolarizationConsumersRecordedIsTrue =
        refl
    ; crossTermNullityTheoremProved =
        false
    ; crossTermNullityTheoremProvedIsFalse =
        CrossTerm.canonicalCrossTermNullityTheoremStillOpen
    ; moduloNullLinearityProved =
        false
    ; moduloNullLinearityProvedIsFalse =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; fourPointCancellationProved =
        false
    ; fourPointCancellationProvedIsFalse =
        FourPoint.canonicalRouteFourPointCancellationStillOpen
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        FourPoint.canonicalRouteParallelogramStillOpen
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        FourPoint.canonicalRouteQuadraticStillBlocked
    ; terminalUnificationPromotion =
        false
    ; terminalUnificationPromotionIsFalse =
        FourPoint.canonicalRouteTerminalPromotionFalse
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        ModuloNull.canonicalModuloNullClayPromotionFalse
    ; allUnificationPromotionFlagsFalse =
        true
    ; allUnificationPromotionFlagsFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        moduloNullFromCrossTermTerminalPromotionAuthorityImpossible
    ; notes =
        "This composite records the precise ladder from U-1a cross-term nullity to modulo-null gluing linearity."
      ∷ "Modulo-null linearity then routes through additive and polarization consumers toward four-point cancellation."
      ∷ "The route is substantive dependency wiring only: actual cross-term nullity, modulo-null linearity, and four-point cancellation remain open."
      ∷ "Parallelogram, quadratic emergence, terminal unification, and Clay promotion remain false."
      ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalModuloNullFromCrossTermRowsCountIs12 :
  promotionRowCount
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ 12
canonicalModuloNullFromCrossTermRowsCountIs12 =
  refl

canonicalModuloNullFromCrossTermTargetRecorded :
  crossTermNullityTargetRecorded
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ true
canonicalModuloNullFromCrossTermTargetRecorded =
  CrossTerm.canonicalCrossTermNullityActualTargetRecorded

canonicalModuloNullFromCrossTermRouteRecorded :
  crossTermToModuloNullLinearityRouteRecorded
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ true
canonicalModuloNullFromCrossTermRouteRecorded =
  CrossTerm.canonicalCrossTermNullityModuloNullLinearityConsumerRecorded

canonicalModuloNullFromCrossTermFourPointRouteRecorded :
  moduloNullLinearityToFourPointRouteRecorded
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ true
canonicalModuloNullFromCrossTermFourPointRouteRecorded =
  FourPoint.canonicalModuloNullLinearityRouteRecorded

canonicalModuloNullFromCrossTermConsumersRecorded :
  additiveAndPolarizationConsumersRecorded
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ true
canonicalModuloNullFromCrossTermConsumersRecorded =
  refl

canonicalModuloNullFromCrossTermNullityStillOpen :
  crossTermNullityTheoremProved
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermNullityStillOpen =
  CrossTerm.canonicalCrossTermNullityTheoremStillOpen

canonicalModuloNullFromCrossTermLinearityStillOpen :
  moduloNullLinearityProved
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermLinearityStillOpen =
  ModuloNull.canonicalModuloNullGluingLinearityStillOpen

canonicalModuloNullFromCrossTermFourPointStillOpen :
  fourPointCancellationProved
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermFourPointStillOpen =
  FourPoint.canonicalRouteFourPointCancellationStillOpen

canonicalModuloNullFromCrossTermParallelogramStillOpen :
  parallelogramProved
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermParallelogramStillOpen =
  FourPoint.canonicalRouteParallelogramStillOpen

canonicalModuloNullFromCrossTermQuadraticStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermQuadraticStillBlocked =
  FourPoint.canonicalRouteQuadraticStillBlocked

canonicalModuloNullFromCrossTermTerminalPromotionFalse :
  terminalUnificationPromotion
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermTerminalPromotionFalse =
  FourPoint.canonicalRouteTerminalPromotionFalse

canonicalModuloNullFromCrossTermClayPromotionFalse :
  clayPromotion
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ false
canonicalModuloNullFromCrossTermClayPromotionFalse =
  ModuloNull.canonicalModuloNullClayPromotionFalse

canonicalModuloNullFromCrossTermAllPromotionFlagsFalse :
  allUnificationPromotionFlagsFalse
    canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
  ≡ true
canonicalModuloNullFromCrossTermAllPromotionFlagsFalse =
  refl
