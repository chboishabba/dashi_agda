module DASHI.Physics.Closure.YMUniformPositiveHolonomyActionBoundary where

-- Yang-Mills uniform positive holonomy action boundary.
--
-- This module records the missing lower-bound obligation:
--
--   non-vacuum / non-flat gluable zero modes carry uniformly positive
--   Wilson action, with explicit dependence on the finite Bruhat-Tits
--   boundary convention, and with a route into Hamiltonian domination.
--
-- It consumes the current zero-mode rigidity, finite Hodge-defect
-- Hamiltonian-domination, and Bochner-Weitzenbock domination boundary
-- surfaces as inputs.  It does not prove the holonomy classification theorem,
-- does not prove the Wilson lower-bound theorem, does not prove Hamiltonian
-- domination, and does not promote Yang-Mills Clay.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary
  as ZeroMode
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Ham
import DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary
  as Bochner

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported surfaces.

data YMUniformPositiveHolonomyImportedSurface : Set where
  gaugeZeroModeVacuumRigidityBoundaryConsumed :
    YMUniformPositiveHolonomyImportedSurface

  hamiltonianDominatesFiniteHodgeDefectBoundaryConsumed :
    YMUniformPositiveHolonomyImportedSurface

  bochnerWeitzenbockHamiltonianDominationBoundaryConsumed :
    YMUniformPositiveHolonomyImportedSurface

canonicalYMUniformPositiveHolonomyImportedSurfaces :
  List YMUniformPositiveHolonomyImportedSurface
canonicalYMUniformPositiveHolonomyImportedSurfaces =
  gaugeZeroModeVacuumRigidityBoundaryConsumed
  ∷ hamiltonianDominatesFiniteHodgeDefectBoundaryConsumed
  ∷ bochnerWeitzenbockHamiltonianDominationBoundaryConsumed
  ∷ []

record YMUniformPositiveHolonomyInputPack : Set where
  field
    zeroModeSurface :
      ZeroMode.UniformPositiveHolonomyActionTarget

    hamiltonianSurface :
      Ham.HamiltonianDominationInequalityTarget

    bochnerSurface :
      Bochner.YMBochnerWeitzenbockRouteLine

open YMUniformPositiveHolonomyInputPack public

canonicalYMUniformPositiveHolonomyInputPack :
  YMUniformPositiveHolonomyInputPack
canonicalYMUniformPositiveHolonomyInputPack =
  record
    { zeroModeSurface =
        ZeroMode.canonicalUniformPositiveHolonomyActionTarget
    ; hamiltonianSurface =
        Ham.canonicalHamiltonianDominationInequalityTarget
    ; bochnerSurface =
        Bochner.holonomyRouteLine
    }

------------------------------------------------------------------------
-- Local flat/vacuum split.

data YMLocalZeroModeBranch : Set where
  locallyFlatGaugeZeroMode :
    YMLocalZeroModeBranch

  locallyCurvedGaugeZeroMode :
    YMLocalZeroModeBranch

  locallyPureGaugeVacuumMode :
    YMLocalZeroModeBranch

  locallyNonVacuumZeroMode :
    YMLocalZeroModeBranch

data YMFlatVacuumSplitJudgement : Set where
  flatAndVacuumModuloGaugeBranch :
    ZeroMode.FlatConnectionSector →
    ZeroMode.VacuumModuloGaugeSector →
    YMFlatVacuumSplitJudgement

  flatButNonVacuumHolonomyBranch :
    ZeroMode.FlatConnectionSector →
    ZeroMode.HolonomyClassificationTarget →
    YMFlatVacuumSplitJudgement

  nonFlatCurvatureBranch :
    YMLocalZeroModeBranch →
    YMFlatVacuumSplitJudgement

canonicalYMFlatVacuumSplitJudgements :
  List YMFlatVacuumSplitJudgement
canonicalYMFlatVacuumSplitJudgements =
  flatAndVacuumModuloGaugeBranch
    ZeroMode.canonicalFlatConnectionSector
    ZeroMode.canonicalVacuumModuloGaugeSector
  ∷ flatButNonVacuumHolonomyBranch
    ZeroMode.canonicalFlatConnectionSector
    ZeroMode.canonicalHolonomyClassificationTarget
  ∷ nonFlatCurvatureBranch locallyCurvedGaugeZeroMode
  ∷ []

data YMNonVacuumNonFlatObligationScope : Set where
  excludePureGaugeVacuumScope :
    YMNonVacuumNonFlatObligationScope

  includeFlatButTopologicallyNontrivialHolonomyScope :
    YMNonVacuumNonFlatObligationScope

  includeNonFlatCurvatureZeroModeScope :
    YMNonVacuumNonFlatObligationScope

  includeGluableCocycleNontrivialSectorScope :
    YMNonVacuumNonFlatObligationScope

canonicalYMNonVacuumNonFlatObligationScopes :
  List YMNonVacuumNonFlatObligationScope
canonicalYMNonVacuumNonFlatObligationScopes =
  excludePureGaugeVacuumScope
  ∷ includeFlatButTopologicallyNontrivialHolonomyScope
  ∷ includeNonFlatCurvatureZeroModeScope
  ∷ includeGluableCocycleNontrivialSectorScope
  ∷ []

------------------------------------------------------------------------
-- Transition cocycle and holonomy sector.

data YMTransitionCocycleStatus : Set where
  transitionCocycleRecordedButClassificationOpen :
    YMTransitionCocycleStatus

data YMTransitionCocycleDatum : Set where
  finitePatchTransitionGij :
    ZeroMode.LocalGaugeHodgeZeroModeSheaf →
    YMTransitionCocycleDatum

  tripleOverlapCocycleGijGjkGki :
    ZeroMode.GaugeTransitionCocycleBoundary →
    YMTransitionCocycleDatum

data YMHolonomySectorKind : Set where
  trivialHolonomyVacuumSector :
    YMHolonomySectorKind

  nontrivialFlatHolonomySector :
    YMHolonomySectorKind

  nonflatCurvatureHolonomySector :
    YMHolonomySectorKind

  topologicalChargeHolonomySector :
    YMHolonomySectorKind

data YMGluableHolonomySector : Set where
  gluableHolonomySectorFromCocycle :
    YMTransitionCocycleDatum →
    ZeroMode.HolonomyClassificationTarget →
    YMHolonomySectorKind →
    YMGluableHolonomySector

canonicalYMTransitionCocycleData :
  List YMTransitionCocycleDatum
canonicalYMTransitionCocycleData =
  finitePatchTransitionGij ZeroMode.canonicalLocalGaugeHodgeZeroModeSheaf
  ∷ tripleOverlapCocycleGijGjkGki
    ZeroMode.canonicalGaugeTransitionCocycleBoundary
  ∷ []

canonicalYMGluableHolonomySectors :
  List YMGluableHolonomySector
canonicalYMGluableHolonomySectors =
  gluableHolonomySectorFromCocycle
    (finitePatchTransitionGij ZeroMode.canonicalLocalGaugeHodgeZeroModeSheaf)
    ZeroMode.canonicalHolonomyClassificationTarget
    trivialHolonomyVacuumSector
  ∷ gluableHolonomySectorFromCocycle
    (tripleOverlapCocycleGijGjkGki
      ZeroMode.canonicalGaugeTransitionCocycleBoundary)
    ZeroMode.canonicalHolonomyClassificationTarget
    nontrivialFlatHolonomySector
  ∷ gluableHolonomySectorFromCocycle
    (tripleOverlapCocycleGijGjkGki
      ZeroMode.canonicalGaugeTransitionCocycleBoundary)
    ZeroMode.canonicalHolonomyClassificationTarget
    topologicalChargeHolonomySector
  ∷ []

------------------------------------------------------------------------
-- Wilson action lower-bound obligation.

data YMWilsonActionTerm : Set where
  plaquetteCurvatureContribution :
    YMWilsonActionTerm

  transitionCocycleMismatchContribution :
    YMWilsonActionTerm

  holonomyClassContribution :
    YMWilsonActionTerm

  topologicalChargeContribution :
    YMWilsonActionTerm

data YMWilsonActionLowerBoundConstant : Set where
  positiveUniformWilsonActionConstantTarget :
    YMWilsonActionLowerBoundConstant

data YMWilsonActionLowerBoundObligation : Set where
  nonVacuumNonFlatGluableZeroModesHavePositiveWilsonAction :
    YMGluableHolonomySector →
    ZeroMode.PositiveTopologicalEnergyTarget →
    Ham.HolonomyCostCarrier →
    YMWilsonActionLowerBoundConstant →
    YMWilsonActionLowerBoundObligation

  wilsonLowerBoundFeedsHolonomyCostCarrier :
    YMWilsonActionLowerBoundObligation →
    Ham.TopologicalSectorPositiveActionTarget →
    YMWilsonActionLowerBoundObligation

canonicalYMWilsonActionTerms :
  List YMWilsonActionTerm
canonicalYMWilsonActionTerms =
  plaquetteCurvatureContribution
  ∷ transitionCocycleMismatchContribution
  ∷ holonomyClassContribution
  ∷ topologicalChargeContribution
  ∷ []

canonicalYMWilsonActionLowerBoundConstant :
  YMWilsonActionLowerBoundConstant
canonicalYMWilsonActionLowerBoundConstant =
  positiveUniformWilsonActionConstantTarget

canonicalYMWilsonActionLowerBoundObligation :
  YMWilsonActionLowerBoundObligation
canonicalYMWilsonActionLowerBoundObligation =
  wilsonLowerBoundFeedsHolonomyCostCarrier
    (nonVacuumNonFlatGluableZeroModesHavePositiveWilsonAction
      (gluableHolonomySectorFromCocycle
        (tripleOverlapCocycleGijGjkGki
          ZeroMode.canonicalGaugeTransitionCocycleBoundary)
        ZeroMode.canonicalHolonomyClassificationTarget
        topologicalChargeHolonomySector)
      ZeroMode.canonicalPositiveTopologicalEnergyTarget
      Ham.canonicalHolonomyCostCarrier
      canonicalYMWilsonActionLowerBoundConstant)
    Ham.canonicalTopologicalSectorPositiveActionTarget

------------------------------------------------------------------------
-- Bruhat-Tits boundary convention dependence.

data YMBTBoundaryConventionClass : Set where
  inducedFiniteBallConventionClass :
    YMBTBoundaryConventionClass

  rootAnchoredInducedConventionClass :
    YMBTBoundaryConventionClass

  fullDegreeKillingConventionClass :
    YMBTBoundaryConventionClass

  fullDegreeRootAnchoredKillingConventionClass :
    YMBTBoundaryConventionClass

data YMBTBoundaryConventionEffect : Set where
  inducedConventionMayCollapseHolonomyMargin :
    YMBTBoundaryConventionEffect

  rootAnchoringAloneDoesNotSupplyUniformMargin :
    YMBTBoundaryConventionEffect

  fullDegreeKillingConventionPreservesCandidateMargin :
    YMBTBoundaryConventionEffect

  boundaryConventionMustBeCarriedIntoGaugeQuotient :
    YMBTBoundaryConventionEffect

data YMBTConventionDependentWilsonObligation : Set where
  wilsonActionLowerBoundDependsOnBTBoundaryConvention :
    YMBTBoundaryConventionClass →
    YMBTBoundaryConventionEffect →
    YMWilsonActionLowerBoundObligation →
    YMBTConventionDependentWilsonObligation

canonicalYMBTBoundaryConventionEffects :
  List YMBTBoundaryConventionEffect
canonicalYMBTBoundaryConventionEffects =
  inducedConventionMayCollapseHolonomyMargin
  ∷ rootAnchoringAloneDoesNotSupplyUniformMargin
  ∷ fullDegreeKillingConventionPreservesCandidateMargin
  ∷ boundaryConventionMustBeCarriedIntoGaugeQuotient
  ∷ []

canonicalYMBTConventionDependentWilsonObligation :
  YMBTConventionDependentWilsonObligation
canonicalYMBTConventionDependentWilsonObligation =
  wilsonActionLowerBoundDependsOnBTBoundaryConvention
    fullDegreeKillingConventionClass
    boundaryConventionMustBeCarriedIntoGaugeQuotient
    canonicalYMWilsonActionLowerBoundObligation

------------------------------------------------------------------------
-- Route to Hamiltonian domination and Bochner-Weitzenbock.

data YMHolonomyActionRouteStage : Set where
  localFlatVacuumSplitStage :
    YMHolonomyActionRouteStage

  transitionCocycleGluingStage :
    YMHolonomyActionRouteStage

  holonomyTopologicalSectorStage :
    YMHolonomyActionRouteStage

  wilsonActionLowerBoundStage :
    YMHolonomyActionRouteStage

  btBoundaryConventionDependenceStage :
    YMHolonomyActionRouteStage

  hamiltonianHolonomyCostCarrierStage :
    YMHolonomyActionRouteStage

  bochnerWeitzenbockPositivePartStage :
    YMHolonomyActionRouteStage

  clayGuardStage :
    YMHolonomyActionRouteStage

canonicalYMHolonomyActionRouteStages :
  List YMHolonomyActionRouteStage
canonicalYMHolonomyActionRouteStages =
  localFlatVacuumSplitStage
  ∷ transitionCocycleGluingStage
  ∷ holonomyTopologicalSectorStage
  ∷ wilsonActionLowerBoundStage
  ∷ btBoundaryConventionDependenceStage
  ∷ hamiltonianHolonomyCostCarrierStage
  ∷ bochnerWeitzenbockPositivePartStage
  ∷ clayGuardStage
  ∷ []

data YMHolonomyActionBlocker : Set where
  missingLocalFlatVacuumDichotomyProof :
    YMHolonomyActionBlocker

  missingTransitionCocycleClassification :
    YMHolonomyActionBlocker

  missingHolonomySectorSeparationTheorem :
    YMHolonomyActionBlocker

  missingUniformWilsonActionLowerBound :
    YMHolonomyActionBlocker

  missingBTBoundaryConventionUniformity :
    YMHolonomyActionBlocker

  missingHolonomyCostCarrierConstruction :
    YMHolonomyActionBlocker

  missingHamiltonianDominationRoute :
    YMHolonomyActionBlocker

  missingBochnerWeitzenbockPositivePartProof :
    YMHolonomyActionBlocker

  missingContinuumNoSpectralPollutionTransfer :
    YMHolonomyActionBlocker

  missingClayYangMillsAuthorityToken :
    YMHolonomyActionBlocker

canonicalYMHolonomyActionBlockers :
  List YMHolonomyActionBlocker
canonicalYMHolonomyActionBlockers =
  missingLocalFlatVacuumDichotomyProof
  ∷ missingTransitionCocycleClassification
  ∷ missingHolonomySectorSeparationTheorem
  ∷ missingUniformWilsonActionLowerBound
  ∷ missingBTBoundaryConventionUniformity
  ∷ missingHolonomyCostCarrierConstruction
  ∷ missingHamiltonianDominationRoute
  ∷ missingBochnerWeitzenbockPositivePartProof
  ∷ missingContinuumNoSpectralPollutionTransfer
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record YMHolonomyActionRouteLine : Set where
  field
    stage :
      YMHolonomyActionRouteStage

    label :
      String

    consumes :
      String

    produces :
      String

    blocker :
      YMHolonomyActionBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMHolonomyActionRouteLine public

flatVacuumSplitRouteLine :
  YMHolonomyActionRouteLine
flatVacuumSplitRouteLine =
  record
    { stage =
        localFlatVacuumSplitStage
    ; label =
        "local flat/vacuum split"
    ; consumes =
        "gauge zero-mode vacuum-rigidity boundary"
    ; produces =
        "vacuum branch versus non-vacuum/non-flat obligation branch"
    ; blocker =
        missingLocalFlatVacuumDichotomyProof
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

cocycleRouteLine :
  YMHolonomyActionRouteLine
cocycleRouteLine =
  record
    { stage =
        transitionCocycleGluingStage
    ; label =
        "transition cocycle"
    ; consumes =
        "local zero-mode sheaf plus g_ij g_jk g_ki cocycle boundary"
    ; produces =
        "gluable holonomy sector ledger"
    ; blocker =
        missingTransitionCocycleClassification
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomySectorRouteLine :
  YMHolonomyActionRouteLine
holonomySectorRouteLine =
  record
    { stage =
        holonomyTopologicalSectorStage
    ; label =
        "holonomy sector separation"
    ; consumes =
        "flat/non-flat split and topological-charge sector boundary"
    ; produces =
        "trivial vacuum sector separated from nontrivial holonomy sectors"
    ; blocker =
        missingHolonomySectorSeparationTheorem
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

wilsonLowerBoundRouteLine :
  YMHolonomyActionRouteLine
wilsonLowerBoundRouteLine =
  record
    { stage =
        wilsonActionLowerBoundStage
    ; label =
        "Wilson action lower bound"
    ; consumes =
        "non-vacuum gluable holonomy sector and positive topological energy target"
    ; produces =
        "uniform positive Wilson action constant target"
    ; blocker =
        missingUniformWilsonActionLowerBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

btConventionRouteLine :
  YMHolonomyActionRouteLine
btConventionRouteLine =
  record
    { stage =
        btBoundaryConventionDependenceStage
    ; label =
        "BT boundary convention"
    ; consumes =
        "finite BT boundary convention and full-degree/killing candidate"
    ; produces =
        "convention-dependent lower-bound obligation"
    ; blocker =
        missingBTBoundaryConventionUniformity
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

hamiltonianRouteLine :
  YMHolonomyActionRouteLine
hamiltonianRouteLine =
  record
    { stage =
        hamiltonianHolonomyCostCarrierStage
    ; label =
        "Hamiltonian domination feed"
    ; consumes =
        "Wilson lower-bound obligation and Hol_d carrier"
    ; produces =
        "H_d >= c Delta_YM,d + c' Hol_d - E_d target"
    ; blocker =
        missingHamiltonianDominationRoute
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

bochnerRouteLine :
  YMHolonomyActionRouteLine
bochnerRouteLine =
  record
    { stage =
        bochnerWeitzenbockPositivePartStage
    ; label =
        "Bochner-Weitzenbock positive part"
    ; consumes =
        "Hamiltonian domination boundary plus Bochner holonomy route line"
    ; produces =
        "curvature/holonomy positive part obligation"
    ; blocker =
        missingBochnerWeitzenbockPositivePartProof
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMHolonomyActionRouteLines :
  List YMHolonomyActionRouteLine
canonicalYMHolonomyActionRouteLines =
  flatVacuumSplitRouteLine
  ∷ cocycleRouteLine
  ∷ holonomySectorRouteLine
  ∷ wilsonLowerBoundRouteLine
  ∷ btConventionRouteLine
  ∷ hamiltonianRouteLine
  ∷ bochnerRouteLine
  ∷ []

data YMHolonomyToHamiltonianDominationBridge : Set where
  holonomyWilsonBoundRoutesToHamiltonianDomination :
    YMUniformPositiveHolonomyInputPack →
    YMBTConventionDependentWilsonObligation →
    Ham.HamiltonianDominationInequalityTarget →
    Bochner.YMBochnerWeitzenbockRouteLine →
    YMHolonomyToHamiltonianDominationBridge

canonicalYMHolonomyToHamiltonianDominationBridge :
  YMHolonomyToHamiltonianDominationBridge
canonicalYMHolonomyToHamiltonianDominationBridge =
  holonomyWilsonBoundRoutesToHamiltonianDomination
    canonicalYMUniformPositiveHolonomyInputPack
    canonicalYMBTConventionDependentWilsonObligation
    Ham.canonicalHamiltonianDominationInequalityTarget
    Bochner.holonomyRouteLine

------------------------------------------------------------------------
-- Rows and counts.

data YMUniformPositiveHolonomyActionRow : Set where
  importedZeroModeVacuumRigidityRow :
    YMUniformPositiveHolonomyActionRow

  importedHamiltonianDominationBoundaryRow :
    YMUniformPositiveHolonomyActionRow

  importedBochnerWeitzenbockBoundaryRow :
    YMUniformPositiveHolonomyActionRow

  localFlatVacuumSplitRow :
    YMUniformPositiveHolonomyActionRow

  nonVacuumNonFlatObligationScopeRow :
    YMUniformPositiveHolonomyActionRow

  transitionCocycleGijGjkGkiRow :
    YMUniformPositiveHolonomyActionRow

  gluableHolonomySectorRow :
    YMUniformPositiveHolonomyActionRow

  topologicalChargeSectorRow :
    YMUniformPositiveHolonomyActionRow

  wilsonActionLowerBoundConstantRow :
    YMUniformPositiveHolonomyActionRow

  btBoundaryConventionDependenceRow :
    YMUniformPositiveHolonomyActionRow

  holonomyCostCarrierRouteRow :
    YMUniformPositiveHolonomyActionRow

  hamiltonianDominationRouteRow :
    YMUniformPositiveHolonomyActionRow

  bochnerWeitzenbockRouteRow :
    YMUniformPositiveHolonomyActionRow

  holonomyClassificationTheoremStillMissingRow :
    YMUniformPositiveHolonomyActionRow

  uniformPositiveWilsonActionTheoremStillMissingRow :
    YMUniformPositiveHolonomyActionRow

  hamiltonianDominationStillMissingRow :
    YMUniformPositiveHolonomyActionRow

  clayAndTerminalHeldFalseRow :
    YMUniformPositiveHolonomyActionRow

canonicalYMUniformPositiveHolonomyActionRows :
  List YMUniformPositiveHolonomyActionRow
canonicalYMUniformPositiveHolonomyActionRows =
  importedZeroModeVacuumRigidityRow
  ∷ importedHamiltonianDominationBoundaryRow
  ∷ importedBochnerWeitzenbockBoundaryRow
  ∷ localFlatVacuumSplitRow
  ∷ nonVacuumNonFlatObligationScopeRow
  ∷ transitionCocycleGijGjkGkiRow
  ∷ gluableHolonomySectorRow
  ∷ topologicalChargeSectorRow
  ∷ wilsonActionLowerBoundConstantRow
  ∷ btBoundaryConventionDependenceRow
  ∷ holonomyCostCarrierRouteRow
  ∷ hamiltonianDominationRouteRow
  ∷ bochnerWeitzenbockRouteRow
  ∷ holonomyClassificationTheoremStillMissingRow
  ∷ uniformPositiveWilsonActionTheoremStillMissingRow
  ∷ hamiltonianDominationStillMissingRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

ymUniformPositiveHolonomyImportedSurfaceCount : Nat
ymUniformPositiveHolonomyImportedSurfaceCount =
  listCount canonicalYMUniformPositiveHolonomyImportedSurfaces

ymHolonomyActionRouteStageCount : Nat
ymHolonomyActionRouteStageCount =
  listCount canonicalYMHolonomyActionRouteStages

ymHolonomyActionRouteLineCount : Nat
ymHolonomyActionRouteLineCount =
  listCount canonicalYMHolonomyActionRouteLines

ymUniformPositiveHolonomyActionRowCount : Nat
ymUniformPositiveHolonomyActionRowCount =
  listCount canonicalYMUniformPositiveHolonomyActionRows

------------------------------------------------------------------------
-- Governance booleans.
-- True means the boundary target is recorded.  False means the theorem or
-- promotion is not constructed in this module.

zeroModeVacuumRigidityBoundaryConsumed : Bool
zeroModeVacuumRigidityBoundaryConsumed =
  true

hamiltonianDominationBoundaryConsumed : Bool
hamiltonianDominationBoundaryConsumed =
  true

bochnerWeitzenbockBoundaryConsumed : Bool
bochnerWeitzenbockBoundaryConsumed =
  true

localFlatVacuumSplitRecorded : Bool
localFlatVacuumSplitRecorded =
  true

transitionCocycleHolonomySectorRecorded : Bool
transitionCocycleHolonomySectorRecorded =
  true

wilsonActionLowerBoundObligationRecorded : Bool
wilsonActionLowerBoundObligationRecorded =
  true

btBoundaryConventionDependenceRecorded : Bool
btBoundaryConventionDependenceRecorded =
  true

hamiltonianDominationRouteRecorded : Bool
hamiltonianDominationRouteRecorded =
  true

holonomyClassificationTheoremProved : Bool
holonomyClassificationTheoremProved =
  false

uniformPositiveHolonomyActionTheoremProved : Bool
uniformPositiveHolonomyActionTheoremProved =
  false

uniformPositiveWilsonActionLowerBoundProved : Bool
uniformPositiveWilsonActionLowerBoundProved =
  false

btBoundaryConventionUniformityProved : Bool
btBoundaryConventionUniformityProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

bochnerWeitzenbockPositivePartProved : Bool
bochnerWeitzenbockPositivePartProved =
  false

continuumNoSpectralPollutionTransferProved : Bool
continuumNoSpectralPollutionTransferProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

zeroModeVacuumRigidityBoundaryConsumedIsTrue :
  zeroModeVacuumRigidityBoundaryConsumed ≡ true
zeroModeVacuumRigidityBoundaryConsumedIsTrue =
  refl

hamiltonianDominationBoundaryConsumedIsTrue :
  hamiltonianDominationBoundaryConsumed ≡ true
hamiltonianDominationBoundaryConsumedIsTrue =
  refl

bochnerWeitzenbockBoundaryConsumedIsTrue :
  bochnerWeitzenbockBoundaryConsumed ≡ true
bochnerWeitzenbockBoundaryConsumedIsTrue =
  refl

localFlatVacuumSplitRecordedIsTrue :
  localFlatVacuumSplitRecorded ≡ true
localFlatVacuumSplitRecordedIsTrue =
  refl

transitionCocycleHolonomySectorRecordedIsTrue :
  transitionCocycleHolonomySectorRecorded ≡ true
transitionCocycleHolonomySectorRecordedIsTrue =
  refl

wilsonActionLowerBoundObligationRecordedIsTrue :
  wilsonActionLowerBoundObligationRecorded ≡ true
wilsonActionLowerBoundObligationRecordedIsTrue =
  refl

btBoundaryConventionDependenceRecordedIsTrue :
  btBoundaryConventionDependenceRecorded ≡ true
btBoundaryConventionDependenceRecordedIsTrue =
  refl

hamiltonianDominationRouteRecordedIsTrue :
  hamiltonianDominationRouteRecorded ≡ true
hamiltonianDominationRouteRecordedIsTrue =
  refl

holonomyClassificationTheoremProvedIsFalse :
  holonomyClassificationTheoremProved ≡ false
holonomyClassificationTheoremProvedIsFalse =
  refl

uniformPositiveHolonomyActionTheoremProvedIsFalse :
  uniformPositiveHolonomyActionTheoremProved ≡ false
uniformPositiveHolonomyActionTheoremProvedIsFalse =
  refl

uniformPositiveWilsonActionLowerBoundProvedIsFalse :
  uniformPositiveWilsonActionLowerBoundProved ≡ false
uniformPositiveWilsonActionLowerBoundProvedIsFalse =
  refl

btBoundaryConventionUniformityProvedIsFalse :
  btBoundaryConventionUniformityProved ≡ false
btBoundaryConventionUniformityProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

bochnerWeitzenbockPositivePartProvedIsFalse :
  bochnerWeitzenbockPositivePartProved ≡ false
bochnerWeitzenbockPositivePartProvedIsFalse =
  refl

continuumNoSpectralPollutionTransferProvedIsFalse :
  continuumNoSpectralPollutionTransferProved ≡ false
continuumNoSpectralPollutionTransferProvedIsFalse =
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

HolonomyClassificationTheorem :
  Set
HolonomyClassificationTheorem =
  ⊥

UniformPositiveHolonomyActionTheorem :
  Set
UniformPositiveHolonomyActionTheorem =
  ⊥

HamiltonianDominationFromHolonomyActionTheorem :
  Set
HamiltonianDominationFromHolonomyActionTheorem =
  ⊥

YMClayPromotionAuthority :
  Set
YMClayPromotionAuthority =
  ⊥

data YMUniformPositiveHolonomyActionStatus : Set where
  boundaryRecordedUniformPositiveHolonomyActionStillOpen :
    YMUniformPositiveHolonomyActionStatus

canonicalYMUniformPositiveHolonomyActionStatus :
  YMUniformPositiveHolonomyActionStatus
canonicalYMUniformPositiveHolonomyActionStatus =
  boundaryRecordedUniformPositiveHolonomyActionStillOpen
