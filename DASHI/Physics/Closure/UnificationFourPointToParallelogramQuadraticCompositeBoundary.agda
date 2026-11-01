module DASHI.Physics.Closure.UnificationFourPointToParallelogramQuadraticCompositeBoundary where

-- Fail-closed composite boundary:
--
--   modulo-null linearity from cross-term nullity
--   + four-point cancellation route
--   + gluing residual forces four-point cancellation
--   + defect four-point/parallelogram law
--   -> four-point cancellation
--   -> parallelogram law
--   -> quadratic emergence handoff.
--
-- This module deliberately composes existing receipt surfaces only.  It does
-- not prove cross-term nullity, modulo-null linearity, gluing residual
-- cancellation, four-point cancellation, the parallelogram law, quadratic
-- emergence, terminal unification, or Clay promotion.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.UnificationModuloNullLinearityFromCrossTermNullityBoundary
  as ModuloNullRoute
import DASHI.Physics.Closure.UnificationFourPointCancellationFromCrossTermNullityBoundary
  as FourPointRoute
import DASHI.Physics.Closure.DefectFourPointParallelogramLawBoundary
  as Parallelogram
import DASHI.Physics.Closure.GluingResidualForcesFourPointCancellationBoundary
  as Residual

------------------------------------------------------------------------
-- Local utility.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support.

record FourPointToParallelogramQuadraticImportedSupport : Setω where
  field
    moduloNullLinearityFromCrossTermBoundary :
      ModuloNullRoute.UnificationModuloNullLinearityFromCrossTermNullityBoundary

    fourPointCancellationFromCrossTermBoundary :
      FourPointRoute.UnificationFourPointCancellationFromCrossTermNullityBoundary

    defectFourPointParallelogramBoundary :
      Parallelogram.DefectFourPointParallelogramLawBoundary

    gluingResidualFourPointBoundary :
      Residual.GluingResidualForcesFourPointCancellationBoundary

    moduloNullRouteRecorded :
      ModuloNullRoute.moduloNullLinearityToFourPointRouteRecorded
        moduloNullLinearityFromCrossTermBoundary
      ≡ true

    moduloNullConsumersRecorded :
      ModuloNullRoute.additiveAndPolarizationConsumersRecorded
        moduloNullLinearityFromCrossTermBoundary
      ≡ true

    moduloNullCrossTermStillOpen :
      ModuloNullRoute.crossTermNullityTheoremProved
        moduloNullLinearityFromCrossTermBoundary
      ≡ false

    moduloNullLinearityStillOpen :
      ModuloNullRoute.moduloNullLinearityProved
        moduloNullLinearityFromCrossTermBoundary
      ≡ false

    moduloNullFourPointStillOpen :
      ModuloNullRoute.fourPointCancellationProved
        moduloNullLinearityFromCrossTermBoundary
      ≡ false

    moduloNullParallelogramStillOpen :
      ModuloNullRoute.parallelogramProved
        moduloNullLinearityFromCrossTermBoundary
      ≡ false

    moduloNullQuadraticStillBlocked :
      ModuloNullRoute.quadraticEmergenceProved
        moduloNullLinearityFromCrossTermBoundary
      ≡ false

    moduloNullTerminalPromotionFalse :
      ModuloNullRoute.terminalUnificationPromotion
        moduloNullLinearityFromCrossTermBoundary
      ≡ false

    routePolarizationResidualRecorded :
      FourPointRoute.polarizationFourPointResidualRecorded
        fourPointCancellationFromCrossTermBoundary
      ≡ true

    routeModuloNullLinearityRecorded :
      FourPointRoute.moduloNullLinearityRouteRecorded
        fourPointCancellationFromCrossTermBoundary
      ≡ true

    routeParallelogramConsumerRecorded :
      FourPointRoute.parallelogramConsumerRecorded
        fourPointCancellationFromCrossTermBoundary
      ≡ true

    routeModuloNullLinearityStillOpen :
      FourPointRoute.moduloNullLinearityProved
        fourPointCancellationFromCrossTermBoundary
      ≡ false

    routeGluingResidualStillOpen :
      FourPointRoute.gluingResidualForcesFourPointCancellationProved
        fourPointCancellationFromCrossTermBoundary
      ≡ false

    routeFourPointStillOpen :
      FourPointRoute.fourPointCancellationProved
        fourPointCancellationFromCrossTermBoundary
      ≡ false

    routeParallelogramStillOpen :
      FourPointRoute.parallelogramProved
        fourPointCancellationFromCrossTermBoundary
      ≡ false

    routeQuadraticStillBlocked :
      FourPointRoute.quadraticEmergenceProved
        fourPointCancellationFromCrossTermBoundary
      ≡ false

    routeTerminalPromotionFalse :
      FourPointRoute.terminalUnificationPromotion
        fourPointCancellationFromCrossTermBoundary
      ≡ false

    residualPolarizationRequired :
      Residual.gluingPolarizationResidualRequired
        gluingResidualFourPointBoundary
      ≡ true

    residualTheoremStillOpen :
      Residual.gluingResidualForcesFourPointCancellationProved
        gluingResidualFourPointBoundary
      ≡ false

    residualFourPointStillOpen :
      Residual.fourPointDefectVanishes
        gluingResidualFourPointBoundary
      ≡ false

    residualParallelogramStillOpen :
      Residual.parallelogramLawProved
        gluingResidualFourPointBoundary
      ≡ false

    residualQuadraticStillBlocked :
      Residual.quadraticFormEmergenceApplied
        gluingResidualFourPointBoundary
      ≡ false

    residualTerminalPromotionFalse :
      Residual.terminalUnificationPromoted
        gluingResidualFourPointBoundary
      ≡ false

    residualClayPromotionFalse :
      Residual.clayPromotion gluingResidualFourPointBoundary
      ≡ false

    parallelogramInterfaceNormalized :
      Parallelogram.fourPointInterfaceNormalized
        defectFourPointParallelogramBoundary
      ≡ true

    parallelogramConcreteSupportChecked :
      Parallelogram.concreteIdentityShiftSupportChecked
        defectFourPointParallelogramBoundary
      ≡ true

    parallelogramMissingLemmaStillOpen :
      Parallelogram.hierarchyConsistencyKillsFourPointDefectProved
        defectFourPointParallelogramBoundary
      ≡ false

    parallelogramQuotientWellDefinednessStillOpen :
      Parallelogram.quotientWellDefinednessProved
        defectFourPointParallelogramBoundary
      ≡ false

    parallelogramLawStillOpen :
      Parallelogram.fourPointParallelogramLawProved
        defectFourPointParallelogramBoundary
      ≡ false

    parallelogramPolarizationExternalNotApplied :
      Parallelogram.polarizationJordanVonNeumannApplied
        defectFourPointParallelogramBoundary
      ≡ false

    parallelogramQuadraticPromotionFalse :
      Parallelogram.quadraticFormEmergencePromoted
        defectFourPointParallelogramBoundary
      ≡ false

    parallelogramClayPromotionFalse :
      Parallelogram.clayPromoted defectFourPointParallelogramBoundary
      ≡ false

    parallelogramTerminalPromotionFalse :
      Parallelogram.terminalPromotion defectFourPointParallelogramBoundary
      ≡ false

open FourPointToParallelogramQuadraticImportedSupport public

canonicalFourPointToParallelogramQuadraticImportedSupport :
  FourPointToParallelogramQuadraticImportedSupport
canonicalFourPointToParallelogramQuadraticImportedSupport =
  record
    { moduloNullLinearityFromCrossTermBoundary =
        ModuloNullRoute.canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary
    ; fourPointCancellationFromCrossTermBoundary =
        FourPointRoute.canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
    ; defectFourPointParallelogramBoundary =
        Parallelogram.canonicalDefectFourPointParallelogramLawBoundary
    ; gluingResidualFourPointBoundary =
        Residual.canonicalGluingResidualForcesFourPointCancellationBoundary
    ; moduloNullRouteRecorded =
        ModuloNullRoute.canonicalModuloNullFromCrossTermFourPointRouteRecorded
    ; moduloNullConsumersRecorded =
        ModuloNullRoute.canonicalModuloNullFromCrossTermConsumersRecorded
    ; moduloNullCrossTermStillOpen =
        ModuloNullRoute.canonicalModuloNullFromCrossTermNullityStillOpen
    ; moduloNullLinearityStillOpen =
        ModuloNullRoute.canonicalModuloNullFromCrossTermLinearityStillOpen
    ; moduloNullFourPointStillOpen =
        ModuloNullRoute.canonicalModuloNullFromCrossTermFourPointStillOpen
    ; moduloNullParallelogramStillOpen =
        ModuloNullRoute.canonicalModuloNullFromCrossTermParallelogramStillOpen
    ; moduloNullQuadraticStillBlocked =
        ModuloNullRoute.canonicalModuloNullFromCrossTermQuadraticStillBlocked
    ; moduloNullTerminalPromotionFalse =
        ModuloNullRoute.canonicalModuloNullFromCrossTermTerminalPromotionFalse
    ; routePolarizationResidualRecorded =
        FourPointRoute.canonicalPolarizationFourPointResidualRecorded
    ; routeModuloNullLinearityRecorded =
        FourPointRoute.canonicalModuloNullLinearityRouteRecorded
    ; routeParallelogramConsumerRecorded =
        FourPointRoute.canonicalParallelogramConsumerRecorded
    ; routeModuloNullLinearityStillOpen =
        FourPointRoute.canonicalRouteModuloNullLinearityStillOpen
    ; routeGluingResidualStillOpen =
        FourPointRoute.canonicalGluingResidualRouteStillOpen
    ; routeFourPointStillOpen =
        FourPointRoute.canonicalRouteFourPointCancellationStillOpen
    ; routeParallelogramStillOpen =
        FourPointRoute.canonicalRouteParallelogramStillOpen
    ; routeQuadraticStillBlocked =
        FourPointRoute.canonicalRouteQuadraticStillBlocked
    ; routeTerminalPromotionFalse =
        FourPointRoute.canonicalRouteTerminalPromotionFalse
    ; residualPolarizationRequired =
        Residual.canonicalGluingPolarizationResidualRequired
    ; residualTheoremStillOpen =
        Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen
    ; residualFourPointStillOpen =
        Residual.canonicalFourPointDefectStillOpen
    ; residualParallelogramStillOpen =
        Residual.canonicalParallelogramLawStillOpen
    ; residualQuadraticStillBlocked =
        Residual.canonicalQuadraticFormEmergenceStillBlocked
    ; residualTerminalPromotionFalse =
        Residual.canonicalTerminalUnificationPromotionFalse
    ; residualClayPromotionFalse =
        Residual.canonicalClayPromotionFalse
    ; parallelogramInterfaceNormalized =
        refl
    ; parallelogramConcreteSupportChecked =
        Parallelogram.canonicalFourPointBoundaryConcreteSupportChecked
    ; parallelogramMissingLemmaStillOpen =
        Parallelogram.canonicalFourPointBoundaryMissingLemmaStillOpen
    ; parallelogramQuotientWellDefinednessStillOpen =
        Parallelogram.canonicalFourPointBoundaryQuotientWellDefinednessStillOpen
    ; parallelogramLawStillOpen =
        Parallelogram.canonicalFourPointBoundaryParallelogramStillOpen
    ; parallelogramPolarizationExternalNotApplied =
        Parallelogram.canonicalFourPointBoundaryPolarizationExternalNotApplied
    ; parallelogramQuadraticPromotionFalse =
        Parallelogram.canonicalFourPointBoundaryQuadraticFormPromotionFalse
    ; parallelogramClayPromotionFalse =
        Parallelogram.canonicalFourPointBoundaryClayPromotionFalse
    ; parallelogramTerminalPromotionFalse =
        Parallelogram.canonicalFourPointBoundaryTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Handoff ladder.

data FourPointToParallelogramQuadraticStage : Set where
  moduloNullLinearityImported :
    FourPointToParallelogramQuadraticStage

  polarizationResidualRecordedStage :
    FourPointToParallelogramQuadraticStage

  gluingResidualTheoremInput :
    FourPointToParallelogramQuadraticStage

  fourPointCancellationInput :
    FourPointToParallelogramQuadraticStage

  quotientWellDefinednessInput :
    FourPointToParallelogramQuadraticStage

  defectFourPointInterface :
    FourPointToParallelogramQuadraticStage

  parallelogramLawConsumer :
    FourPointToParallelogramQuadraticStage

  polarizationBoundaryHandoff :
    FourPointToParallelogramQuadraticStage

  jordanVonNeumannBoundaryHandoff :
    FourPointToParallelogramQuadraticStage

  quadraticEmergenceConsumer :
    FourPointToParallelogramQuadraticStage

  signatureCliffordConsumers :
    FourPointToParallelogramQuadraticStage

  terminalPromotionGate :
    FourPointToParallelogramQuadraticStage

data FourPointToParallelogramQuadraticStatus : Set where
  importedBoundary :
    FourPointToParallelogramQuadraticStatus

  targetRecorded :
    FourPointToParallelogramQuadraticStatus

  theoremOpen :
    FourPointToParallelogramQuadraticStatus

  prerequisiteOpen :
    FourPointToParallelogramQuadraticStatus

  interfaceReady :
    FourPointToParallelogramQuadraticStatus

  downstreamBlocked :
    FourPointToParallelogramQuadraticStatus

  externalBoundary :
    FourPointToParallelogramQuadraticStatus

  promotionHeld :
    FourPointToParallelogramQuadraticStatus

canonicalFourPointToParallelogramQuadraticStatus :
  FourPointToParallelogramQuadraticStage →
  FourPointToParallelogramQuadraticStatus
canonicalFourPointToParallelogramQuadraticStatus moduloNullLinearityImported =
  importedBoundary
canonicalFourPointToParallelogramQuadraticStatus polarizationResidualRecordedStage =
  targetRecorded
canonicalFourPointToParallelogramQuadraticStatus gluingResidualTheoremInput =
  theoremOpen
canonicalFourPointToParallelogramQuadraticStatus fourPointCancellationInput =
  theoremOpen
canonicalFourPointToParallelogramQuadraticStatus quotientWellDefinednessInput =
  prerequisiteOpen
canonicalFourPointToParallelogramQuadraticStatus defectFourPointInterface =
  interfaceReady
canonicalFourPointToParallelogramQuadraticStatus parallelogramLawConsumer =
  theoremOpen
canonicalFourPointToParallelogramQuadraticStatus polarizationBoundaryHandoff =
  externalBoundary
canonicalFourPointToParallelogramQuadraticStatus jordanVonNeumannBoundaryHandoff =
  externalBoundary
canonicalFourPointToParallelogramQuadraticStatus quadraticEmergenceConsumer =
  downstreamBlocked
canonicalFourPointToParallelogramQuadraticStatus signatureCliffordConsumers =
  downstreamBlocked
canonicalFourPointToParallelogramQuadraticStatus terminalPromotionGate =
  promotionHeld

data FourPointToParallelogramQuadraticBlocker : Set where
  noBlockerForImportedBoundary :
    FourPointToParallelogramQuadraticBlocker

  noBlockerForRecordedTarget :
    FourPointToParallelogramQuadraticBlocker

  missingGluingResidualForcesFourPointCancellation :
    FourPointToParallelogramQuadraticBlocker

  missingActualFourPointCancellation :
    FourPointToParallelogramQuadraticBlocker

  missingQuotientWellDefinedness :
    FourPointToParallelogramQuadraticBlocker

  noBlockerForNormalizedInterface :
    FourPointToParallelogramQuadraticBlocker

  missingParallelogramLaw :
    FourPointToParallelogramQuadraticBlocker

  parallelogramRequiredBeforePolarization :
    FourPointToParallelogramQuadraticBlocker

  parallelogramRequiredBeforeJordanVonNeumann :
    FourPointToParallelogramQuadraticBlocker

  missingQuadraticEmergence :
    FourPointToParallelogramQuadraticBlocker

  quadraticRequiredBeforeSignatureClifford :
    FourPointToParallelogramQuadraticBlocker

  noTerminalPromotionAuthority :
    FourPointToParallelogramQuadraticBlocker

canonicalFourPointToParallelogramQuadraticBlocker :
  FourPointToParallelogramQuadraticStage →
  FourPointToParallelogramQuadraticBlocker
canonicalFourPointToParallelogramQuadraticBlocker moduloNullLinearityImported =
  noBlockerForImportedBoundary
canonicalFourPointToParallelogramQuadraticBlocker polarizationResidualRecordedStage =
  noBlockerForRecordedTarget
canonicalFourPointToParallelogramQuadraticBlocker gluingResidualTheoremInput =
  missingGluingResidualForcesFourPointCancellation
canonicalFourPointToParallelogramQuadraticBlocker fourPointCancellationInput =
  missingActualFourPointCancellation
canonicalFourPointToParallelogramQuadraticBlocker quotientWellDefinednessInput =
  missingQuotientWellDefinedness
canonicalFourPointToParallelogramQuadraticBlocker defectFourPointInterface =
  noBlockerForNormalizedInterface
canonicalFourPointToParallelogramQuadraticBlocker parallelogramLawConsumer =
  missingParallelogramLaw
canonicalFourPointToParallelogramQuadraticBlocker polarizationBoundaryHandoff =
  parallelogramRequiredBeforePolarization
canonicalFourPointToParallelogramQuadraticBlocker jordanVonNeumannBoundaryHandoff =
  parallelogramRequiredBeforeJordanVonNeumann
canonicalFourPointToParallelogramQuadraticBlocker quadraticEmergenceConsumer =
  missingQuadraticEmergence
canonicalFourPointToParallelogramQuadraticBlocker signatureCliffordConsumers =
  quadraticRequiredBeforeSignatureClifford
canonicalFourPointToParallelogramQuadraticBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record FourPointToParallelogramQuadraticRow : Set where
  field
    stage :
      FourPointToParallelogramQuadraticStage

    status :
      FourPointToParallelogramQuadraticStatus

    statusIsCanonical :
      status ≡ canonicalFourPointToParallelogramQuadraticStatus stage

    blocker :
      FourPointToParallelogramQuadraticBlocker

    blockerIsCanonical :
      blocker ≡ canonicalFourPointToParallelogramQuadraticBlocker stage

    handoffContract :
      String

    consumedSurface :
      String

    provedOrPromotedHere :
      Bool

    provedOrPromotedHereIsFalse :
      provedOrPromotedHere ≡ false

open FourPointToParallelogramQuadraticRow public

mkFourPointToParallelogramQuadraticRow :
  FourPointToParallelogramQuadraticStage →
  String →
  String →
  FourPointToParallelogramQuadraticRow
mkFourPointToParallelogramQuadraticRow
  stage handoffContract consumedSurface =
  record
    { stage =
        stage
    ; status =
        canonicalFourPointToParallelogramQuadraticStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalFourPointToParallelogramQuadraticBlocker stage
    ; blockerIsCanonical =
        refl
    ; handoffContract =
        handoffContract
    ; consumedSurface =
        consumedSurface
    ; provedOrPromotedHere =
        false
    ; provedOrPromotedHereIsFalse =
        refl
    }

canonicalFourPointToParallelogramQuadraticRows :
  List FourPointToParallelogramQuadraticRow
canonicalFourPointToParallelogramQuadraticRows =
  mkFourPointToParallelogramQuadraticRow
    moduloNullLinearityImported
    "import the cross-term-nullity to modulo-null-linearity route without proving it"
    "UnificationModuloNullLinearityFromCrossTermNullityBoundary"
  ∷ mkFourPointToParallelogramQuadraticRow
    polarizationResidualRecordedStage
    "record Q(x+y)+Q(x-y)-2Q(x)-2Q(y) as the exact four-point residual"
    "UnificationFourPointCancellationFromCrossTermNullityBoundary"
  ∷ mkFourPointToParallelogramQuadraticRow
    gluingResidualTheoremInput
    "require the theorem that gluing/polarization residual nullity forces four-point cancellation"
    "GluingResidualForcesFourPointCancellationBoundary"
  ∷ mkFourPointToParallelogramQuadraticRow
    fourPointCancellationInput
    "consume actual four-point cancellation only after the residual theorem is proved"
    "FourPointRoute.fourPointCancellationProved"
  ∷ mkFourPointToParallelogramQuadraticRow
    quotientWellDefinednessInput
    "require Q and the four-point expression to be representative-invariant on the quotient"
    "DefectFourPointParallelogramLawBoundary.quotientWellDefinednessProved"
  ∷ mkFourPointToParallelogramQuadraticRow
    defectFourPointInterface
    "use the normalized abelian quotient defect surface as the target interface"
    "DefectFourPointParallelogramLawBoundary.AbelianQuotientDefectSurface"
  ∷ mkFourPointToParallelogramQuadraticRow
    parallelogramLawConsumer
    "turn four-point cancellation into Q(x+y)+Q(x-y)=2Q(x)+2Q(y)"
    "DefectFourPointParallelogramLawBoundary.ParallelogramLaw"
  ∷ mkFourPointToParallelogramQuadraticRow
    polarizationBoundaryHandoff
    "polarization is accepted only as an external boundary after the parallelogram law"
    "DefectFourPointParallelogramLawBoundary.polarizationBoundaryAccepted"
  ∷ mkFourPointToParallelogramQuadraticRow
    jordanVonNeumannBoundaryHandoff
    "Jordan-von-Neumann quadratic emergence is only a downstream external theorem boundary"
    "DefectFourPointParallelogramLawBoundary.jordanVonNeumannBoundaryAccepted"
  ∷ mkFourPointToParallelogramQuadraticRow
    quadraticEmergenceConsumer
    "quadratic emergence waits for parallelogram plus polarization/Jordan-von-Neumann application"
    "DefectFourPointParallelogramLawBoundary.quadraticFormEmergencePromoted"
  ∷ mkFourPointToParallelogramQuadraticRow
    signatureCliffordConsumers
    "signature and Clifford consumers wait for an actual quadratic form"
    "downstream signature/Clifford surfaces"
  ∷ mkFourPointToParallelogramQuadraticRow
    terminalPromotionGate
    "terminal unification and Clay promotion remain authority-gated and false"
    "all imported terminal gates"
  ∷ []

canonicalFourPointToParallelogramQuadraticRowCount : Nat
canonicalFourPointToParallelogramQuadraticRowCount =
  listLength canonicalFourPointToParallelogramQuadraticRows

canonicalFourPointToParallelogramQuadraticRowCountIs12 :
  canonicalFourPointToParallelogramQuadraticRowCount ≡ 12
canonicalFourPointToParallelogramQuadraticRowCountIs12 =
  refl

------------------------------------------------------------------------
-- Boundary.

data FourPointToParallelogramQuadraticPromotionAuthority : Set where

fourPointToParallelogramQuadraticPromotionAuthorityImpossible :
  FourPointToParallelogramQuadraticPromotionAuthority →
  ⊥
fourPointToParallelogramQuadraticPromotionAuthorityImpossible ()

record UnificationFourPointToParallelogramQuadraticCompositeBoundary :
  Setω where
  field
    importedSupport :
      FourPointToParallelogramQuadraticImportedSupport

    handoffRows :
      List FourPointToParallelogramQuadraticRow

    handoffRowCount :
      Nat

    handoffRowCountIs12 :
      handoffRowCount ≡ 12

    handoffRowCountMatchesRows :
      handoffRowCount ≡ listLength handoffRows

    moduloNullLinearityRouteRecorded :
      Bool

    moduloNullLinearityRouteRecordedIsTrue :
      moduloNullLinearityRouteRecorded ≡ true

    fourPointResidualRecorded :
      Bool

    fourPointResidualRecordedIsTrue :
      fourPointResidualRecorded ≡ true

    gluingResidualFourPointTheoremRequired :
      Bool

    gluingResidualFourPointTheoremRequiredIsTrue :
      gluingResidualFourPointTheoremRequired ≡ true

    normalizedParallelogramInterfaceRecorded :
      Bool

    normalizedParallelogramInterfaceRecordedIsTrue :
      normalizedParallelogramInterfaceRecorded ≡ true

    polarizationJordanVonNeumannBoundaryRecorded :
      Bool

    polarizationJordanVonNeumannBoundaryRecordedIsTrue :
      polarizationJordanVonNeumannBoundaryRecorded ≡ true

    crossTermNullityProved :
      Bool

    crossTermNullityProvedIsFalse :
      crossTermNullityProved ≡ false

    moduloNullLinearityProved :
      Bool

    moduloNullLinearityProvedIsFalse :
      moduloNullLinearityProved ≡ false

    gluingResidualForcesFourPointCancellationProved :
      Bool

    gluingResidualForcesFourPointCancellationProvedIsFalse :
      gluingResidualForcesFourPointCancellationProved ≡ false

    fourPointCancellationProved :
      Bool

    fourPointCancellationProvedIsFalse :
      fourPointCancellationProved ≡ false

    quotientWellDefinednessProved :
      Bool

    quotientWellDefinednessProvedIsFalse :
      quotientWellDefinednessProved ≡ false

    parallelogramLawProved :
      Bool

    parallelogramLawProvedIsFalse :
      parallelogramLawProved ≡ false

    polarizationJordanVonNeumannApplied :
      Bool

    polarizationJordanVonNeumannAppliedIsFalse :
      polarizationJordanVonNeumannApplied ≡ false

    quadraticEmergencePromoted :
      Bool

    quadraticEmergencePromotedIsFalse :
      quadraticEmergencePromoted ≡ false

    signatureCliffordConsumersPromoted :
      Bool

    signatureCliffordConsumersPromotedIsFalse :
      signatureCliffordConsumersPromoted ≡ false

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
      FourPointToParallelogramQuadraticPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationFourPointToParallelogramQuadraticCompositeBoundary public

canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary :
  UnificationFourPointToParallelogramQuadraticCompositeBoundary
canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary =
  record
    { importedSupport =
        canonicalFourPointToParallelogramQuadraticImportedSupport
    ; handoffRows =
        canonicalFourPointToParallelogramQuadraticRows
    ; handoffRowCount =
        12
    ; handoffRowCountIs12 =
        refl
    ; handoffRowCountMatchesRows =
        refl
    ; moduloNullLinearityRouteRecorded =
        true
    ; moduloNullLinearityRouteRecordedIsTrue =
        ModuloNullRoute.canonicalModuloNullFromCrossTermFourPointRouteRecorded
    ; fourPointResidualRecorded =
        true
    ; fourPointResidualRecordedIsTrue =
        FourPointRoute.canonicalPolarizationFourPointResidualRecorded
    ; gluingResidualFourPointTheoremRequired =
        true
    ; gluingResidualFourPointTheoremRequiredIsTrue =
        Residual.canonicalGluingPolarizationResidualRequired
    ; normalizedParallelogramInterfaceRecorded =
        true
    ; normalizedParallelogramInterfaceRecordedIsTrue =
        refl
    ; polarizationJordanVonNeumannBoundaryRecorded =
        true
    ; polarizationJordanVonNeumannBoundaryRecordedIsTrue =
        refl
    ; crossTermNullityProved =
        false
    ; crossTermNullityProvedIsFalse =
        ModuloNullRoute.canonicalModuloNullFromCrossTermNullityStillOpen
    ; moduloNullLinearityProved =
        false
    ; moduloNullLinearityProvedIsFalse =
        ModuloNullRoute.canonicalModuloNullFromCrossTermLinearityStillOpen
    ; gluingResidualForcesFourPointCancellationProved =
        false
    ; gluingResidualForcesFourPointCancellationProvedIsFalse =
        Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen
    ; fourPointCancellationProved =
        false
    ; fourPointCancellationProvedIsFalse =
        FourPointRoute.canonicalRouteFourPointCancellationStillOpen
    ; quotientWellDefinednessProved =
        false
    ; quotientWellDefinednessProvedIsFalse =
        Parallelogram.canonicalFourPointBoundaryQuotientWellDefinednessStillOpen
    ; parallelogramLawProved =
        false
    ; parallelogramLawProvedIsFalse =
        Parallelogram.canonicalFourPointBoundaryParallelogramStillOpen
    ; polarizationJordanVonNeumannApplied =
        false
    ; polarizationJordanVonNeumannAppliedIsFalse =
        Parallelogram.canonicalFourPointBoundaryPolarizationExternalNotApplied
    ; quadraticEmergencePromoted =
        false
    ; quadraticEmergencePromotedIsFalse =
        Parallelogram.canonicalFourPointBoundaryQuadraticFormPromotionFalse
    ; signatureCliffordConsumersPromoted =
        false
    ; signatureCliffordConsumersPromotedIsFalse =
        refl
    ; terminalUnificationPromotion =
        false
    ; terminalUnificationPromotionIsFalse =
        Parallelogram.canonicalFourPointBoundaryTerminalPromotionFalse
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        Parallelogram.canonicalFourPointBoundaryClayPromotionFalse
    ; allPromotionFlagsFalse =
        true
    ; allPromotionFlagsFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        fourPointToParallelogramQuadraticPromotionAuthorityImpossible
    ; notes =
        "This composite is the U-1 through U-4 handoff: modulo-null linearity routes to four-point cancellation, then to parallelogram, then to quadratic emergence."
        ∷ "The exact four-point expression remains Q(x+y)+Q(x-y)-2Q(x)-2Q(y); no weaker two-homogeneous or monotone hypothesis is promoted."
        ∷ "The normalized abelian quotient defect interface is imported from DefectFourPointParallelogramLawBoundary."
        ∷ "Polarization and Jordan-von-Neumann are recorded as external mathematics boundaries only after the parallelogram law is proved."
        ∷ "Quadratic emergence, signature/Clifford consumers, terminal unification, and Clay promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Canonical guard lemmas.

canonicalFourPointToParallelogramQuadraticRowsCountIs12 :
  handoffRowCount
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ 12
canonicalFourPointToParallelogramQuadraticRowsCountIs12 =
  refl

canonicalFourPointToParallelogramQuadraticRowsMatch :
  handoffRowCount
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡
  listLength
    (handoffRows
      canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary)
canonicalFourPointToParallelogramQuadraticRowsMatch =
  refl

canonicalFourPointToParallelogramQuadraticModuloRouteRecorded :
  moduloNullLinearityRouteRecorded
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ true
canonicalFourPointToParallelogramQuadraticModuloRouteRecorded =
  ModuloNullRoute.canonicalModuloNullFromCrossTermFourPointRouteRecorded

canonicalFourPointToParallelogramQuadraticFourPointResidualRecorded :
  fourPointResidualRecorded
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ true
canonicalFourPointToParallelogramQuadraticFourPointResidualRecorded =
  FourPointRoute.canonicalPolarizationFourPointResidualRecorded

canonicalFourPointToParallelogramQuadraticGluingResidualRequired :
  gluingResidualFourPointTheoremRequired
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ true
canonicalFourPointToParallelogramQuadraticGluingResidualRequired =
  Residual.canonicalGluingPolarizationResidualRequired

canonicalFourPointToParallelogramQuadraticCrossTermStillOpen :
  crossTermNullityProved
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticCrossTermStillOpen =
  ModuloNullRoute.canonicalModuloNullFromCrossTermNullityStillOpen

canonicalFourPointToParallelogramQuadraticModuloLinearityStillOpen :
  moduloNullLinearityProved
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticModuloLinearityStillOpen =
  ModuloNullRoute.canonicalModuloNullFromCrossTermLinearityStillOpen

canonicalFourPointToParallelogramQuadraticResidualTheoremStillOpen :
  gluingResidualForcesFourPointCancellationProved
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticResidualTheoremStillOpen =
  Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen

canonicalFourPointToParallelogramQuadraticFourPointStillOpen :
  fourPointCancellationProved
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticFourPointStillOpen =
  FourPointRoute.canonicalRouteFourPointCancellationStillOpen

canonicalFourPointToParallelogramQuadraticQuotientStillOpen :
  quotientWellDefinednessProved
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticQuotientStillOpen =
  Parallelogram.canonicalFourPointBoundaryQuotientWellDefinednessStillOpen

canonicalFourPointToParallelogramQuadraticParallelogramStillOpen :
  parallelogramLawProved
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticParallelogramStillOpen =
  Parallelogram.canonicalFourPointBoundaryParallelogramStillOpen

canonicalFourPointToParallelogramQuadraticPolarizationNotApplied :
  polarizationJordanVonNeumannApplied
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticPolarizationNotApplied =
  Parallelogram.canonicalFourPointBoundaryPolarizationExternalNotApplied

canonicalFourPointToParallelogramQuadraticQuadraticPromotionFalse :
  quadraticEmergencePromoted
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticQuadraticPromotionFalse =
  Parallelogram.canonicalFourPointBoundaryQuadraticFormPromotionFalse

canonicalFourPointToParallelogramQuadraticTerminalPromotionFalse :
  terminalUnificationPromotion
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticTerminalPromotionFalse =
  Parallelogram.canonicalFourPointBoundaryTerminalPromotionFalse

canonicalFourPointToParallelogramQuadraticClayPromotionFalse :
  clayPromotion
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ false
canonicalFourPointToParallelogramQuadraticClayPromotionFalse =
  Parallelogram.canonicalFourPointBoundaryClayPromotionFalse

canonicalFourPointToParallelogramQuadraticAllPromotionFlagsFalse :
  allPromotionFlagsFalse
    canonicalUnificationFourPointToParallelogramQuadraticCompositeBoundary
  ≡ true
canonicalFourPointToParallelogramQuadraticAllPromotionFlagsFalse =
  refl
