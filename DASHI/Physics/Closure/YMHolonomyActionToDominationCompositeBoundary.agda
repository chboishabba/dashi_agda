module DASHI.Physics.Closure.YMHolonomyActionToDominationCompositeBoundary where

-- Yang-Mills holonomy-action to domination composite boundary.
--
-- This module records the exact bridge:
--
--   uniform positive holonomy/Wilson action
--   -> Hol_d positive part in the Bochner-Weitzenbock route
--   -> H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d
--   -> finite spectral-margin preconditions.
--
-- It is intentionally fail-closed.  The imported surfaces are consumed as
-- typed support; this module does not prove the holonomy classification,
-- Wilson lower bound, Hamiltonian domination, spectral margin, OS transfer,
-- continuum transfer, Yang-Mills Clay, or terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMUniformPositiveHolonomyActionBoundary
  as Holonomy
import DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary
  as Bochner
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMHolonomyActionToDominationImportedSurface : Set where
  uniformPositiveHolonomyActionBoundaryImported :
    YMHolonomyActionToDominationImportedSurface

  bochnerWeitzenbockHamiltonianDominationBoundaryImported :
    YMHolonomyActionToDominationImportedSurface

  hamiltonianDominatesFiniteHodgeDefectBoundaryImported :
    YMHolonomyActionToDominationImportedSurface

canonicalYMHolonomyActionToDominationImportedSurfaces :
  List YMHolonomyActionToDominationImportedSurface
canonicalYMHolonomyActionToDominationImportedSurfaces =
  uniformPositiveHolonomyActionBoundaryImported
  ∷ bochnerWeitzenbockHamiltonianDominationBoundaryImported
  ∷ hamiltonianDominatesFiniteHodgeDefectBoundaryImported
  ∷ []

record YMHolonomyActionToDominationInputPack : Setω where
  field
    holonomyInput :
      Holonomy.YMUniformPositiveHolonomyInputPack

    holonomyBridge :
      Holonomy.YMHolonomyToHamiltonianDominationBridge

    wilsonActionObligation :
      Holonomy.YMWilsonActionLowerBoundObligation

    conventionDependentWilsonObligation :
      Holonomy.YMBTConventionDependentWilsonObligation

    bochnerHolonomyRoute :
      Bochner.YMBochnerWeitzenbockRouteLine

    bochnerSpectralMarginRoute :
      Bochner.YMBochnerWeitzenbockRouteLine

    hodgeDominationTarget :
      Domination.HamiltonianDominationInequalityTarget

    hodgeHolonomyCostCarrier :
      Domination.HolonomyCostCarrier

    hodgePositiveActionTarget :
      Domination.TopologicalSectorPositiveActionTarget

open YMHolonomyActionToDominationInputPack public

canonicalYMHolonomyActionToDominationInputPack :
  YMHolonomyActionToDominationInputPack
canonicalYMHolonomyActionToDominationInputPack =
  record
    { holonomyInput =
        Holonomy.canonicalYMUniformPositiveHolonomyInputPack
    ; holonomyBridge =
        Holonomy.canonicalYMHolonomyToHamiltonianDominationBridge
    ; wilsonActionObligation =
        Holonomy.canonicalYMWilsonActionLowerBoundObligation
    ; conventionDependentWilsonObligation =
        Holonomy.canonicalYMBTConventionDependentWilsonObligation
    ; bochnerHolonomyRoute =
        Bochner.holonomyRouteLine
    ; bochnerSpectralMarginRoute =
        Bochner.spectralMarginRouteLine
    ; hodgeDominationTarget =
        Domination.canonicalHamiltonianDominationInequalityTarget
    ; hodgeHolonomyCostCarrier =
        Domination.canonicalHolonomyCostCarrier
    ; hodgePositiveActionTarget =
        Domination.canonicalTopologicalSectorPositiveActionTarget
    }

------------------------------------------------------------------------
-- Composite route.

data YMHolonomyActionToDominationStatus : Set where
  holonomyActionToDominationBoundaryRecordedStillOpen :
    YMHolonomyActionToDominationStatus

data YMHolonomyActionToDominationStage : Set where
  gluableZeroModeSectorSplitStage :
    YMHolonomyActionToDominationStage

  nonVacuumHolonomyClassificationStage :
    YMHolonomyActionToDominationStage

  uniformWilsonActionLowerBoundStage :
    YMHolonomyActionToDominationStage

  btBoundaryConventionUniformityStage :
    YMHolonomyActionToDominationStage

  holonomyCostCarrierConstructionStage :
    YMHolonomyActionToDominationStage

  bochnerHolonomyPositivePartStage :
    YMHolonomyActionToDominationStage

  hamiltonianDefectPlusHolonomyDominationStage :
    YMHolonomyActionToDominationStage

  controlledErrorAbsorptionStage :
    YMHolonomyActionToDominationStage

  spectralMarginPreconditionStage :
    YMHolonomyActionToDominationStage

  osContinuumTransferGuardStage :
    YMHolonomyActionToDominationStage

canonicalYMHolonomyActionToDominationStages :
  List YMHolonomyActionToDominationStage
canonicalYMHolonomyActionToDominationStages =
  gluableZeroModeSectorSplitStage
  ∷ nonVacuumHolonomyClassificationStage
  ∷ uniformWilsonActionLowerBoundStage
  ∷ btBoundaryConventionUniformityStage
  ∷ holonomyCostCarrierConstructionStage
  ∷ bochnerHolonomyPositivePartStage
  ∷ hamiltonianDefectPlusHolonomyDominationStage
  ∷ controlledErrorAbsorptionStage
  ∷ spectralMarginPreconditionStage
  ∷ osContinuumTransferGuardStage
  ∷ []

stageLabel :
  YMHolonomyActionToDominationStage →
  String
stageLabel gluableZeroModeSectorSplitStage =
  "gluable zero-mode sector split"
stageLabel nonVacuumHolonomyClassificationStage =
  "non-vacuum holonomy classification"
stageLabel uniformWilsonActionLowerBoundStage =
  "uniform Wilson action lower bound"
stageLabel btBoundaryConventionUniformityStage =
  "BT boundary convention uniformity"
stageLabel holonomyCostCarrierConstructionStage =
  "Hol_d cost carrier construction"
stageLabel bochnerHolonomyPositivePartStage =
  "Bochner holonomy positive part"
stageLabel hamiltonianDefectPlusHolonomyDominationStage =
  "Hamiltonian defect-plus-holonomy domination"
stageLabel controlledErrorAbsorptionStage =
  "controlled E_d absorption"
stageLabel spectralMarginPreconditionStage =
  "spectral margin precondition"
stageLabel osContinuumTransferGuardStage =
  "OS/continuum transfer guard"

data YMHolonomyActionToDominationBlocker : Set where
  missingHolonomyClassification :
    YMHolonomyActionToDominationBlocker

  missingUniformWilsonActionLowerBound :
    YMHolonomyActionToDominationBlocker

  missingBoundaryConventionUniformity :
    YMHolonomyActionToDominationBlocker

  missingHolonomyCostCarrier :
    YMHolonomyActionToDominationBlocker

  missingBochnerHolonomyPositivePart :
    YMHolonomyActionToDominationBlocker

  missingHamiltonianDefectPlusHolonomyDomination :
    YMHolonomyActionToDominationBlocker

  missingControlledErrorAbsorption :
    YMHolonomyActionToDominationBlocker

  missingUniformSpectralMarginAfterErrors :
    YMHolonomyActionToDominationBlocker

  missingReflectionPositiveOSTransfer :
    YMHolonomyActionToDominationBlocker

  missingContinuumNoSpectralPollutionTransfer :
    YMHolonomyActionToDominationBlocker

  missingClayYangMillsAuthority :
    YMHolonomyActionToDominationBlocker

canonicalYMHolonomyActionToDominationBlockers :
  List YMHolonomyActionToDominationBlocker
canonicalYMHolonomyActionToDominationBlockers =
  missingHolonomyClassification
  ∷ missingUniformWilsonActionLowerBound
  ∷ missingBoundaryConventionUniformity
  ∷ missingHolonomyCostCarrier
  ∷ missingBochnerHolonomyPositivePart
  ∷ missingHamiltonianDefectPlusHolonomyDomination
  ∷ missingControlledErrorAbsorption
  ∷ missingUniformSpectralMarginAfterErrors
  ∷ missingReflectionPositiveOSTransfer
  ∷ missingContinuumNoSpectralPollutionTransfer
  ∷ missingClayYangMillsAuthority
  ∷ []

data YMHolonomyActionDominationDependency : Set where
  wilsonLowerBoundSuppliesHolonomyCost :
    Holonomy.YMWilsonActionLowerBoundObligation →
    Domination.HolonomyCostCarrier →
    YMHolonomyActionDominationDependency

  boundaryConventionPreservesHolonomyMargin :
    Holonomy.YMBTConventionDependentWilsonObligation →
    YMHolonomyActionDominationDependency

  holonomyCostFeedsBochnerPositivePart :
    Bochner.YMBochnerWeitzenbockRouteLine →
    YMHolonomyActionDominationDependency

  bochnerPositivePartFeedsDominationInequality :
    Bochner.YMBochnerWeitzenbockRouteLine →
    Domination.HamiltonianDominationInequalityTarget →
    YMHolonomyActionDominationDependency

  dominationInequalityFeedsSpectralMargin :
    Bochner.YMBochnerWeitzenbockRouteLine →
    YMHolonomyActionDominationDependency

canonicalYMHolonomyActionDominationDependencies :
  List YMHolonomyActionDominationDependency
canonicalYMHolonomyActionDominationDependencies =
  wilsonLowerBoundSuppliesHolonomyCost
    Holonomy.canonicalYMWilsonActionLowerBoundObligation
    Domination.canonicalHolonomyCostCarrier
  ∷ boundaryConventionPreservesHolonomyMargin
    Holonomy.canonicalYMBTConventionDependentWilsonObligation
  ∷ holonomyCostFeedsBochnerPositivePart
    Bochner.holonomyRouteLine
  ∷ bochnerPositivePartFeedsDominationInequality
    Bochner.holonomyRouteLine
    Domination.canonicalHamiltonianDominationInequalityTarget
  ∷ dominationInequalityFeedsSpectralMargin
    Bochner.spectralMarginRouteLine
  ∷ []

record YMHolonomyActionToDominationRouteLine : Set where
  field
    stage :
      YMHolonomyActionToDominationStage

    label :
      String

    consumes :
      String

    produces :
      String

    blocker :
      YMHolonomyActionToDominationBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMHolonomyActionToDominationRouteLine public

holonomyClassificationRouteLine :
  YMHolonomyActionToDominationRouteLine
holonomyClassificationRouteLine =
  record
    { stage =
        nonVacuumHolonomyClassificationStage
    ; label =
        "holonomy classification"
    ; consumes =
        "gluable zero-mode sector split and transition cocycle data"
    ; produces =
        "non-vacuum sector separated from pure gauge vacuum"
    ; blocker =
        missingHolonomyClassification
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

wilsonActionRouteLine :
  YMHolonomyActionToDominationRouteLine
wilsonActionRouteLine =
  record
    { stage =
        uniformWilsonActionLowerBoundStage
    ; label =
        "uniform Wilson action"
    ; consumes =
        "non-vacuum gluable holonomy sectors"
    ; produces =
        "positive Hol_d action-cost target"
    ; blocker =
        missingUniformWilsonActionLowerBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

boundaryConventionRouteLine :
  YMHolonomyActionToDominationRouteLine
boundaryConventionRouteLine =
  record
    { stage =
        btBoundaryConventionUniformityStage
    ; label =
        "boundary convention uniformity"
    ; consumes =
        "full-degree/Killing BT convention and Wilson obligation"
    ; produces =
        "candidate uniform margin not destroyed by induced-ball truncation"
    ; blocker =
        missingBoundaryConventionUniformity
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomyCostCarrierRouteLine :
  YMHolonomyActionToDominationRouteLine
holonomyCostCarrierRouteLine =
  record
    { stage =
        holonomyCostCarrierConstructionStage
    ; label =
        "Hol_d carrier"
    ; consumes =
        "Wilson lower bound and topological-sector positive action target"
    ; produces =
        "finite holonomy cost term for Hamiltonian domination"
    ; blocker =
        missingHolonomyCostCarrier
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

bochnerPositivePartRouteLine :
  YMHolonomyActionToDominationRouteLine
bochnerPositivePartRouteLine =
  record
    { stage =
        bochnerHolonomyPositivePartStage
    ; label =
        "Bochner Hol_d positive part"
    ; consumes =
        "Hol_d carrier plus Bochner-Weitzenbock holonomy route line"
    ; produces =
        "positive c2 Hol_d contribution outside vacuum"
    ; blocker =
        missingBochnerHolonomyPositivePart
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

dominationRouteLine :
  YMHolonomyActionToDominationRouteLine
dominationRouteLine =
  record
    { stage =
        hamiltonianDefectPlusHolonomyDominationStage
    ; label =
        "defect plus holonomy domination"
    ; consumes =
        "Delta_YM,d coercivity, Hol_d positivity, and controlled E_d"
    ; produces =
        "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d target"
    ; blocker =
        missingHamiltonianDefectPlusHolonomyDomination
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

spectralMarginRouteLine :
  YMHolonomyActionToDominationRouteLine
spectralMarginRouteLine =
  record
    { stage =
        spectralMarginPreconditionStage
    ; label =
        "spectral margin after errors"
    ; consumes =
        "domination inequality plus E_d absorption"
    ; produces =
        "uniform finite margin precondition for OS/continuum transfer"
    ; blocker =
        missingUniformSpectralMarginAfterErrors
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMHolonomyActionToDominationRouteLines :
  List YMHolonomyActionToDominationRouteLine
canonicalYMHolonomyActionToDominationRouteLines =
  holonomyClassificationRouteLine
  ∷ wilsonActionRouteLine
  ∷ boundaryConventionRouteLine
  ∷ holonomyCostCarrierRouteLine
  ∷ bochnerPositivePartRouteLine
  ∷ dominationRouteLine
  ∷ spectralMarginRouteLine
  ∷ []

------------------------------------------------------------------------
-- Governance flags.

holonomyActionBoundaryConsumed : Bool
holonomyActionBoundaryConsumed =
  true

bochnerBoundaryConsumed : Bool
bochnerBoundaryConsumed =
  true

hodgeDominationBoundaryConsumed : Bool
hodgeDominationBoundaryConsumed =
  true

holonomyBridgeRecorded : Bool
holonomyBridgeRecorded =
  true

spectralMarginPreconditionRecorded : Bool
spectralMarginPreconditionRecorded =
  true

holonomyClassificationProved : Bool
holonomyClassificationProved =
  false

uniformWilsonActionLowerBoundProved : Bool
uniformWilsonActionLowerBoundProved =
  false

holonomyCostCarrierConstructed : Bool
holonomyCostCarrierConstructed =
  false

bochnerHolonomyPositivePartProved : Bool
bochnerHolonomyPositivePartProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

spectralMarginProved : Bool
spectralMarginProved =
  false

osTransferProved : Bool
osTransferProved =
  false

continuumNoSpectralPollutionProved : Bool
continuumNoSpectralPollutionProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

holonomyActionBoundaryConsumedIsTrue :
  holonomyActionBoundaryConsumed ≡ true
holonomyActionBoundaryConsumedIsTrue =
  refl

bochnerBoundaryConsumedIsTrue :
  bochnerBoundaryConsumed ≡ true
bochnerBoundaryConsumedIsTrue =
  refl

hodgeDominationBoundaryConsumedIsTrue :
  hodgeDominationBoundaryConsumed ≡ true
hodgeDominationBoundaryConsumedIsTrue =
  refl

holonomyBridgeRecordedIsTrue :
  holonomyBridgeRecorded ≡ true
holonomyBridgeRecordedIsTrue =
  refl

spectralMarginPreconditionRecordedIsTrue :
  spectralMarginPreconditionRecorded ≡ true
spectralMarginPreconditionRecordedIsTrue =
  refl

holonomyClassificationProvedIsFalse :
  holonomyClassificationProved ≡ false
holonomyClassificationProvedIsFalse =
  refl

uniformWilsonActionLowerBoundProvedIsFalse :
  uniformWilsonActionLowerBoundProved ≡ false
uniformWilsonActionLowerBoundProvedIsFalse =
  refl

holonomyCostCarrierConstructedIsFalse :
  holonomyCostCarrierConstructed ≡ false
holonomyCostCarrierConstructedIsFalse =
  refl

bochnerHolonomyPositivePartProvedIsFalse :
  bochnerHolonomyPositivePartProved ≡ false
bochnerHolonomyPositivePartProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

spectralMarginProvedIsFalse :
  spectralMarginProved ≡ false
spectralMarginProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
  refl

continuumNoSpectralPollutionProvedIsFalse :
  continuumNoSpectralPollutionProved ≡ false
continuumNoSpectralPollutionProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Fail-closed theorem surfaces.

HolonomyActionToDominationTheorem :
  Set
HolonomyActionToDominationTheorem =
  ⊥

SpectralMarginFromHolonomyDominationTheorem :
  Set
SpectralMarginFromHolonomyDominationTheorem =
  ⊥

YMClayPromotionAuthority :
  Set
YMClayPromotionAuthority =
  ⊥

------------------------------------------------------------------------
-- Composite boundary receipt.

record YMHolonomyActionToDominationCompositeBoundary : Setω where
  field
    status :
      YMHolonomyActionToDominationStatus

    inputPack :
      YMHolonomyActionToDominationInputPack

    holonomyBoundaryInputPack :
      Holonomy.YMUniformPositiveHolonomyInputPack

    holonomyBridge :
      Holonomy.YMHolonomyToHamiltonianDominationBridge

    bochnerBoundary :
      Bochner.YMBochnerWeitzenbockHamiltonianDominationBoundary

    hodgeDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    imports :
      List YMHolonomyActionToDominationImportedSurface

    importsAreCanonical :
      imports ≡ canonicalYMHolonomyActionToDominationImportedSurfaces

    importCount :
      Nat

    importCountIs3 :
      importCount ≡ 3

    stages :
      List YMHolonomyActionToDominationStage

    stagesAreCanonical :
      stages ≡ canonicalYMHolonomyActionToDominationStages

    stageCount :
      Nat

    stageCountIs10 :
      stageCount ≡ 10

    dependencies :
      List YMHolonomyActionDominationDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalYMHolonomyActionDominationDependencies

    dependencyCount :
      Nat

    dependencyCountIs5 :
      dependencyCount ≡ 5

    blockers :
      List YMHolonomyActionToDominationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMHolonomyActionToDominationBlockers

    blockerCount :
      Nat

    blockerCountIs11 :
      blockerCount ≡ 11

    routeLines :
      List YMHolonomyActionToDominationRouteLine

    routeLinesAreCanonical :
      routeLines ≡ canonicalYMHolonomyActionToDominationRouteLines

    routeLineCount :
      Nat

    routeLineCountIs7 :
      routeLineCount ≡ 7

    targetInequalityText :
      String

    targetInequalityTextIsCanonical :
      targetInequalityText
      ≡
      "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"

    importedHolonomyClassificationStillFalse :
      Holonomy.holonomyClassificationTheoremProved ≡ false

    importedHolonomyActionStillFalse :
      Holonomy.uniformPositiveHolonomyActionTheoremProved ≡ false

    importedWilsonLowerBoundStillFalse :
      Holonomy.uniformPositiveWilsonActionLowerBoundProved ≡ false

    importedHolonomyHamiltonianRouteStillFalse :
      Holonomy.hamiltonianDominationProved ≡ false

    importedBochnerHolonomyPositivePartPromoted :
      Bochner.holonomyPositiveActionProvedField bochnerBoundary ≡ true

    importedBochnerDominationPromoted :
      Bochner.hamiltonianDominationProvedField bochnerBoundary ≡ true

    importedBochnerSpectralMarginPromoted :
      Bochner.spectralMarginProvedField bochnerBoundary ≡ true

    importedBochnerOSStillFalse :
      Bochner.osTransferProvedField bochnerBoundary ≡ false

    importedBochnerContinuumStillFalse :
      Bochner.continuumNoSpectralPollutionProvedField bochnerBoundary
      ≡
      false

    importedHodgeHolonomyCostCarrierStillFalse :
      Domination.holonomyCostCarrierConstructedField
        hodgeDominationBoundary
      ≡
      false

    importedHodgePositiveActionStillFalse :
      Domination.positiveActionForTopologicalSectorsProvedField
        hodgeDominationBoundary
      ≡
      false

    importedHodgeDominationPlusHolonomyStillFalse :
      Domination.dominationPlusHolonomyProvedField
        hodgeDominationBoundary
      ≡
      false

    importedHodgeSpectralLiftStillFalse :
      Domination.selfAdjointSpectralGapLiftProvedField
        hodgeDominationBoundary
      ≡
      false

    importedHodgeContinuumStillFalse :
      Domination.continuumTransferNoSpectralPollutionProvedField
        hodgeDominationBoundary
      ≡
      false

    holonomyActionBoundaryConsumedField :
      Bool

    holonomyActionBoundaryConsumedFieldIsTrue :
      holonomyActionBoundaryConsumedField ≡ true

    bochnerBoundaryConsumedField :
      Bool

    bochnerBoundaryConsumedFieldIsTrue :
      bochnerBoundaryConsumedField ≡ true

    hodgeDominationBoundaryConsumedField :
      Bool

    hodgeDominationBoundaryConsumedFieldIsTrue :
      hodgeDominationBoundaryConsumedField ≡ true

    holonomyBridgeRecordedField :
      Bool

    holonomyBridgeRecordedFieldIsTrue :
      holonomyBridgeRecordedField ≡ true

    spectralMarginPreconditionRecordedField :
      Bool

    spectralMarginPreconditionRecordedFieldIsTrue :
      spectralMarginPreconditionRecordedField ≡ true

    holonomyClassificationProvedField :
      Bool

    holonomyClassificationProvedFieldIsFalse :
      holonomyClassificationProvedField ≡ false

    uniformWilsonActionLowerBoundProvedField :
      Bool

    uniformWilsonActionLowerBoundProvedFieldIsFalse :
      uniformWilsonActionLowerBoundProvedField ≡ false

    holonomyCostCarrierConstructedField :
      Bool

    holonomyCostCarrierConstructedFieldIsFalse :
      holonomyCostCarrierConstructedField ≡ false

    bochnerHolonomyPositivePartProvedField :
      Bool

    bochnerHolonomyPositivePartProvedFieldIsFalse :
      bochnerHolonomyPositivePartProvedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    spectralMarginProvedField :
      Bool

    spectralMarginProvedFieldIsFalse :
      spectralMarginProvedField ≡ false

    osTransferProvedField :
      Bool

    osTransferProvedFieldIsFalse :
      osTransferProvedField ≡ false

    continuumNoSpectralPollutionProvedField :
      Bool

    continuumNoSpectralPollutionProvedFieldIsFalse :
      continuumNoSpectralPollutionProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    firstBlocker :
      YMHolonomyActionToDominationBlocker

    firstBlockerIsHolonomyClassification :
      firstBlocker ≡ missingHolonomyClassification

    spectralMarginBlocker :
      YMHolonomyActionToDominationBlocker

    spectralMarginBlockerIsUniformMargin :
      spectralMarginBlocker ≡ missingUniformSpectralMarginAfterErrors

    clayBlocker :
      YMHolonomyActionToDominationBlocker

    clayBlockerIsAuthority :
      clayBlocker ≡ missingClayYangMillsAuthority

    notes :
      List String

open YMHolonomyActionToDominationCompositeBoundary public

canonicalYMHolonomyActionToDominationCompositeBoundary :
  YMHolonomyActionToDominationCompositeBoundary
canonicalYMHolonomyActionToDominationCompositeBoundary =
  record
    { status =
        holonomyActionToDominationBoundaryRecordedStillOpen
    ; inputPack =
        canonicalYMHolonomyActionToDominationInputPack
    ; holonomyBoundaryInputPack =
        Holonomy.canonicalYMUniformPositiveHolonomyInputPack
    ; holonomyBridge =
        Holonomy.canonicalYMHolonomyToHamiltonianDominationBridge
    ; bochnerBoundary =
        Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; hodgeDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; imports =
        canonicalYMHolonomyActionToDominationImportedSurfaces
    ; importsAreCanonical =
        refl
    ; importCount =
        listCount canonicalYMHolonomyActionToDominationImportedSurfaces
    ; importCountIs3 =
        refl
    ; stages =
        canonicalYMHolonomyActionToDominationStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMHolonomyActionToDominationStages
    ; stageCountIs10 =
        refl
    ; dependencies =
        canonicalYMHolonomyActionDominationDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyCount =
        listCount canonicalYMHolonomyActionDominationDependencies
    ; dependencyCountIs5 =
        refl
    ; blockers =
        canonicalYMHolonomyActionToDominationBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMHolonomyActionToDominationBlockers
    ; blockerCountIs11 =
        refl
    ; routeLines =
        canonicalYMHolonomyActionToDominationRouteLines
    ; routeLinesAreCanonical =
        refl
    ; routeLineCount =
        listCount canonicalYMHolonomyActionToDominationRouteLines
    ; routeLineCountIs7 =
        refl
    ; targetInequalityText =
        "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"
    ; targetInequalityTextIsCanonical =
        refl
    ; importedHolonomyClassificationStillFalse =
        Holonomy.holonomyClassificationTheoremProvedIsFalse
    ; importedHolonomyActionStillFalse =
        Holonomy.uniformPositiveHolonomyActionTheoremProvedIsFalse
    ; importedWilsonLowerBoundStillFalse =
        Holonomy.uniformPositiveWilsonActionLowerBoundProvedIsFalse
    ; importedHolonomyHamiltonianRouteStillFalse =
        Holonomy.hamiltonianDominationProvedIsFalse
    ; importedBochnerHolonomyPositivePartPromoted =
        Bochner.holonomyPositiveActionProvedFieldIsTrue
          Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; importedBochnerDominationPromoted =
        Bochner.hamiltonianDominationProvedFieldIsTrue
          Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; importedBochnerSpectralMarginPromoted =
        Bochner.spectralMarginProvedFieldIsTrue
          Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; importedBochnerOSStillFalse =
        Bochner.osTransferProvedFieldIsFalse
          Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; importedBochnerContinuumStillFalse =
        Bochner.continuumNoSpectralPollutionProvedFieldIsFalse
          Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; importedHodgeHolonomyCostCarrierStillFalse =
        Domination.holonomyCostCarrierConstructedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedHodgePositiveActionStillFalse =
        Domination.positiveActionForTopologicalSectorsProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedHodgeDominationPlusHolonomyStillFalse =
        Domination.dominationPlusHolonomyProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedHodgeSpectralLiftStillFalse =
        Domination.selfAdjointSpectralGapLiftProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedHodgeContinuumStillFalse =
        Domination.continuumTransferNoSpectralPollutionProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; holonomyActionBoundaryConsumedField =
        holonomyActionBoundaryConsumed
    ; holonomyActionBoundaryConsumedFieldIsTrue =
        holonomyActionBoundaryConsumedIsTrue
    ; bochnerBoundaryConsumedField =
        bochnerBoundaryConsumed
    ; bochnerBoundaryConsumedFieldIsTrue =
        bochnerBoundaryConsumedIsTrue
    ; hodgeDominationBoundaryConsumedField =
        hodgeDominationBoundaryConsumed
    ; hodgeDominationBoundaryConsumedFieldIsTrue =
        hodgeDominationBoundaryConsumedIsTrue
    ; holonomyBridgeRecordedField =
        holonomyBridgeRecorded
    ; holonomyBridgeRecordedFieldIsTrue =
        holonomyBridgeRecordedIsTrue
    ; spectralMarginPreconditionRecordedField =
        spectralMarginPreconditionRecorded
    ; spectralMarginPreconditionRecordedFieldIsTrue =
        spectralMarginPreconditionRecordedIsTrue
    ; holonomyClassificationProvedField =
        holonomyClassificationProved
    ; holonomyClassificationProvedFieldIsFalse =
        holonomyClassificationProvedIsFalse
    ; uniformWilsonActionLowerBoundProvedField =
        uniformWilsonActionLowerBoundProved
    ; uniformWilsonActionLowerBoundProvedFieldIsFalse =
        uniformWilsonActionLowerBoundProvedIsFalse
    ; holonomyCostCarrierConstructedField =
        holonomyCostCarrierConstructed
    ; holonomyCostCarrierConstructedFieldIsFalse =
        holonomyCostCarrierConstructedIsFalse
    ; bochnerHolonomyPositivePartProvedField =
        bochnerHolonomyPositivePartProved
    ; bochnerHolonomyPositivePartProvedFieldIsFalse =
        bochnerHolonomyPositivePartProvedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; spectralMarginProvedField =
        spectralMarginProved
    ; spectralMarginProvedFieldIsFalse =
        spectralMarginProvedIsFalse
    ; osTransferProvedField =
        osTransferProved
    ; osTransferProvedFieldIsFalse =
        osTransferProvedIsFalse
    ; continuumNoSpectralPollutionProvedField =
        continuumNoSpectralPollutionProved
    ; continuumNoSpectralPollutionProvedFieldIsFalse =
        continuumNoSpectralPollutionProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; firstBlocker =
        missingHolonomyClassification
    ; firstBlockerIsHolonomyClassification =
        refl
    ; spectralMarginBlocker =
        missingUniformSpectralMarginAfterErrors
    ; spectralMarginBlockerIsUniformMargin =
        refl
    ; clayBlocker =
        missingClayYangMillsAuthority
    ; clayBlockerIsAuthority =
        refl
    ; notes =
        "Composite bridge records how uniform positive holonomy/Wilson action would feed Hol_d in the Bochner-Weitzenbock domination route."
        ∷ "The concrete target remains H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d."
        ∷ "Holonomy classification, Wilson action positivity, Hol_d carrier construction, Bochner positive part, domination, and spectral margin all remain open."
        ∷ "Spectral margin is recorded as a precondition for reflection-positive OS transfer and continuum no-spectral-pollution, not as a proved gap."
        ∷ "YM Clay and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas and promotion blockers.

canonicalYMHolonomyActionToDominationImportCountIs3 :
  importCount canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  3
canonicalYMHolonomyActionToDominationImportCountIs3 =
  refl

canonicalYMHolonomyActionToDominationStageCountIs10 :
  stageCount canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  10
canonicalYMHolonomyActionToDominationStageCountIs10 =
  refl

canonicalYMHolonomyActionToDominationDependencyCountIs5 :
  dependencyCount canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  5
canonicalYMHolonomyActionToDominationDependencyCountIs5 =
  refl

canonicalYMHolonomyActionToDominationRouteLineCountIs7 :
  routeLineCount canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  7
canonicalYMHolonomyActionToDominationRouteLineCountIs7 =
  refl

canonicalYMHolonomyActionToDominationFirstBlocker :
  firstBlocker canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  missingHolonomyClassification
canonicalYMHolonomyActionToDominationFirstBlocker =
  refl

canonicalYMHolonomyActionToDominationSpectralMarginStillFalse :
  spectralMarginProvedField
    canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  false
canonicalYMHolonomyActionToDominationSpectralMarginStillFalse =
  refl

canonicalYMHolonomyActionToDominationClayStillFalse :
  ymClayPromotedField
    canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  false
canonicalYMHolonomyActionToDominationClayStillFalse =
  refl

canonicalYMHolonomyActionToDominationTerminalStillFalse :
  terminalPromotionField
    canonicalYMHolonomyActionToDominationCompositeBoundary
  ≡
  false
canonicalYMHolonomyActionToDominationTerminalStillFalse =
  refl

canonicalYMHolonomyActionToDominationNotes : List String
canonicalYMHolonomyActionToDominationNotes =
  notes canonicalYMHolonomyActionToDominationCompositeBoundary
