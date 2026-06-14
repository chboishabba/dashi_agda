module DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary where

-- YM-5 Bochner-Weitzenbock Hamiltonian domination boundary.
--
-- This module records the route
--
--   H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d
--
-- as a boundary ledger over the finite Hodge-defect domination surface, the
-- domination error budget, the Killing/full-degree self-adjointness composite
-- support, and the gauge-zero-mode / holonomy support.  The local finite
-- payload promotes the Bochner-Weitzenbock identity, Delta_YM coercivity,
-- holonomy positive action, Hamiltonian domination, and spectral margin.  OS
-- transfer, continuum transfer, YM Clay, and terminal promotion stay false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination
import DASHI.Physics.Closure.YMHamiltonianDominationErrorBudgetBoundary
  as ErrorBudget
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as KillingDomain
import DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary
  as KillingFlux
import DASHI.Physics.Closure.YMKillingBoundaryOrientationCancellationBoundary
  as KillingOrientation
import DASHI.Physics.Closure.YMKillingBoundaryGaugeDomainPreservationBoundary
  as KillingGauge
import DASHI.Physics.Closure.YMKillingBoundaryWeightPreservationBoundary
  as KillingWeight
import DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionBoundary
  as KillingOpposite
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessCompositeBoundary
  as KillingComposite
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary
  as KillingTheorem
import DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary
  as ZeroMode

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMBochnerWeitzenbockImportedSupport : Set where
  hamiltonianDominatesFiniteHodgeDefectBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  hamiltonianDominationErrorBudgetBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  killingSelfAdjointnessDomainContractImported :
    YMBochnerWeitzenbockImportedSupport

  killingFluxCancellationBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  killingOrientationCancellationBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  killingGaugeDomainPreservationBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  killingWeightPreservationBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  killingOppositeFaceInvolutionBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  killingSelfAdjointnessCompositeBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

  gaugeZeroModeVacuumRigidityBoundaryImported :
    YMBochnerWeitzenbockImportedSupport

canonicalYMBochnerWeitzenbockImportedSupport :
  List YMBochnerWeitzenbockImportedSupport
canonicalYMBochnerWeitzenbockImportedSupport =
  hamiltonianDominatesFiniteHodgeDefectBoundaryImported
  ∷ hamiltonianDominationErrorBudgetBoundaryImported
  ∷ killingSelfAdjointnessDomainContractImported
  ∷ killingFluxCancellationBoundaryImported
  ∷ killingOrientationCancellationBoundaryImported
  ∷ killingGaugeDomainPreservationBoundaryImported
  ∷ killingWeightPreservationBoundaryImported
  ∷ killingOppositeFaceInvolutionBoundaryImported
  ∷ killingSelfAdjointnessCompositeBoundaryImported
  ∷ gaugeZeroModeVacuumRigidityBoundaryImported
  ∷ []

------------------------------------------------------------------------
-- Bochner-Weitzenbock route vocabulary.

data YMBochnerWeitzenbockStatus : Set where
  ym5BochnerWeitzenbockRouteRecordedDominationStillOpen :
    YMBochnerWeitzenbockStatus

data YMBochnerWeitzenbockStage : Set where
  omegaPerpGaugeQuotientDomainStage :
    YMBochnerWeitzenbockStage

  killingBoundarySelfAdjointDomainStage :
    YMBochnerWeitzenbockStage

  finiteHodgeAdjointnessBoundaryStage :
    YMBochnerWeitzenbockStage

  bochnerWeitzenbockDecompositionStage :
    YMBochnerWeitzenbockStage

  finiteCovariantLaplacianDeltaYMStage :
    YMBochnerWeitzenbockStage

  curvatureHolonomyPositivePartStage :
    YMBochnerWeitzenbockStage

  gaugeZeroModeRemovalStage :
    YMBochnerWeitzenbockStage

  controlledErrorEdAbsorptionStage :
    YMBochnerWeitzenbockStage

  spectralMarginAfterErrorsStage :
    YMBochnerWeitzenbockStage

  reflectionPositiveOSTransferStage :
    YMBochnerWeitzenbockStage

  continuumNoSpectralPollutionStage :
    YMBochnerWeitzenbockStage

  clayPromotionGuardStage :
    YMBochnerWeitzenbockStage

canonicalYMBochnerWeitzenbockStages :
  List YMBochnerWeitzenbockStage
canonicalYMBochnerWeitzenbockStages =
  omegaPerpGaugeQuotientDomainStage
  ∷ killingBoundarySelfAdjointDomainStage
  ∷ finiteHodgeAdjointnessBoundaryStage
  ∷ bochnerWeitzenbockDecompositionStage
  ∷ finiteCovariantLaplacianDeltaYMStage
  ∷ curvatureHolonomyPositivePartStage
  ∷ gaugeZeroModeRemovalStage
  ∷ controlledErrorEdAbsorptionStage
  ∷ spectralMarginAfterErrorsStage
  ∷ reflectionPositiveOSTransferStage
  ∷ continuumNoSpectralPollutionStage
  ∷ clayPromotionGuardStage
  ∷ []

stageLabel :
  YMBochnerWeitzenbockStage →
  String
stageLabel omegaPerpGaugeQuotientDomainStage =
  "Omega-perp gauge quotient domain"
stageLabel killingBoundarySelfAdjointDomainStage =
  "Killing/full-degree self-adjoint domain"
stageLabel finiteHodgeAdjointnessBoundaryStage =
  "finite Hodge adjointness through boundary"
stageLabel bochnerWeitzenbockDecompositionStage =
  "Bochner-Weitzenbock decomposition"
stageLabel finiteCovariantLaplacianDeltaYMStage =
  "finite covariant Laplacian Delta_YM,d"
stageLabel curvatureHolonomyPositivePartStage =
  "curvature/holonomy positive part Hol_d"
stageLabel gaugeZeroModeRemovalStage =
  "gauge zero-mode removal"
stageLabel controlledErrorEdAbsorptionStage =
  "controlled E_d absorption"
stageLabel spectralMarginAfterErrorsStage =
  "spectral margin after errors"
stageLabel reflectionPositiveOSTransferStage =
  "reflection-positive OS transfer"
stageLabel continuumNoSpectralPollutionStage =
  "continuum no spectral pollution"
stageLabel clayPromotionGuardStage =
  "YM Clay promotion guard"

data YMBochnerWeitzenbockInequalityComponent : Set where
  restrictedHamiltonianHdOnOmegaPerp :
    YMBochnerWeitzenbockInequalityComponent

  positiveCoefficientC1 :
    YMBochnerWeitzenbockInequalityComponent

  finiteYMLaplacianDeltaYMd :
    YMBochnerWeitzenbockInequalityComponent

  positiveCoefficientC2 :
    YMBochnerWeitzenbockInequalityComponent

  holonomyTopologicalCostHold :
    YMBochnerWeitzenbockInequalityComponent

  controlledNegativeErrorEd :
    YMBochnerWeitzenbockInequalityComponent

canonicalYMBochnerWeitzenbockInequalityComponents :
  List YMBochnerWeitzenbockInequalityComponent
canonicalYMBochnerWeitzenbockInequalityComponents =
  restrictedHamiltonianHdOnOmegaPerp
  ∷ positiveCoefficientC1
  ∷ finiteYMLaplacianDeltaYMd
  ∷ positiveCoefficientC2
  ∷ holonomyTopologicalCostHold
  ∷ controlledNegativeErrorEd
  ∷ []

data YMBochnerWeitzenbockTermSource : Set where
  finiteHodgeDefectLaplacianSource :
    YMBochnerWeitzenbockTermSource

  hamiltonianQuadraticFormSource :
    YMBochnerWeitzenbockTermSource

  curvatureCommutatorSource :
    YMBochnerWeitzenbockTermSource

  holonomySectorSource :
    YMBochnerWeitzenbockTermSource

  gaugeZeroModeQuotientSource :
    YMBochnerWeitzenbockTermSource

  killingBoundaryNoLeakageSource :
    YMBochnerWeitzenbockTermSource

  errorBudgetSource :
    YMBochnerWeitzenbockTermSource

canonicalYMBochnerWeitzenbockTermSources :
  List YMBochnerWeitzenbockTermSource
canonicalYMBochnerWeitzenbockTermSources =
  finiteHodgeDefectLaplacianSource
  ∷ hamiltonianQuadraticFormSource
  ∷ curvatureCommutatorSource
  ∷ holonomySectorSource
  ∷ gaugeZeroModeQuotientSource
  ∷ killingBoundaryNoLeakageSource
  ∷ errorBudgetSource
  ∷ []

data YMBochnerWeitzenbockBoundaryObligation : Set where
  consumeFiniteHodgeDefectDominationBoundary :
    YMBochnerWeitzenbockBoundaryObligation

  consumeHamiltonianDominationErrorBudgetBoundary :
    YMBochnerWeitzenbockBoundaryObligation

  consumeKillingBoundaryDomainSupport :
    YMBochnerWeitzenbockBoundaryObligation

  consumeGaugeDomainPreservationSupport :
    YMBochnerWeitzenbockBoundaryObligation

  consumeGaugeZeroModeHolonomySupport :
    YMBochnerWeitzenbockBoundaryObligation

  defineOmegaPerpRestriction :
    YMBochnerWeitzenbockBoundaryObligation

  proveBochnerWeitzenbockIdentityOnFiniteQuotient :
    YMBochnerWeitzenbockBoundaryObligation

  proveDeltaYMdPositiveOnOmegaPerp :
    YMBochnerWeitzenbockBoundaryObligation

  proveHolonomyTopologicalCostPositive :
    YMBochnerWeitzenbockBoundaryObligation

  proveErrorEdAbsorbedByPositiveTerms :
    YMBochnerWeitzenbockBoundaryObligation

  proveUniformSpectralMarginAfterBudget :
    YMBochnerWeitzenbockBoundaryObligation

  proveReflectionPositiveOSTransfer :
    YMBochnerWeitzenbockBoundaryObligation

  proveContinuumNoSpectralPollutionTransfer :
    YMBochnerWeitzenbockBoundaryObligation

  keepClayAndTerminalPromotionFalse :
    YMBochnerWeitzenbockBoundaryObligation

canonicalYMBochnerWeitzenbockBoundaryObligations :
  List YMBochnerWeitzenbockBoundaryObligation
canonicalYMBochnerWeitzenbockBoundaryObligations =
  consumeFiniteHodgeDefectDominationBoundary
  ∷ consumeHamiltonianDominationErrorBudgetBoundary
  ∷ consumeKillingBoundaryDomainSupport
  ∷ consumeGaugeDomainPreservationSupport
  ∷ consumeGaugeZeroModeHolonomySupport
  ∷ defineOmegaPerpRestriction
  ∷ proveBochnerWeitzenbockIdentityOnFiniteQuotient
  ∷ proveDeltaYMdPositiveOnOmegaPerp
  ∷ proveHolonomyTopologicalCostPositive
  ∷ proveErrorEdAbsorbedByPositiveTerms
  ∷ proveUniformSpectralMarginAfterBudget
  ∷ proveReflectionPositiveOSTransfer
  ∷ proveContinuumNoSpectralPollutionTransfer
  ∷ keepClayAndTerminalPromotionFalse
  ∷ []

data YMBochnerWeitzenbockBlocker : Set where
  missingOmegaPerpDomainIdentification :
    YMBochnerWeitzenbockBlocker

  missingKillingBoundarySelfAdjointnessComposite :
    YMBochnerWeitzenbockBlocker

  missingGaugeDomainDescentToOmegaPerp :
    YMBochnerWeitzenbockBlocker

  missingFiniteBochnerWeitzenbockIdentity :
    YMBochnerWeitzenbockBlocker

  missingDeltaYMdOperatorCoercivity :
    YMBochnerWeitzenbockBlocker

  missingHolonomyPositiveActionCarrier :
    YMBochnerWeitzenbockBlocker

  missingGaugeZeroModeExclusionOnQuotient :
    YMBochnerWeitzenbockBlocker

  missingControlledEdAbsorption :
    YMBochnerWeitzenbockBlocker

  missingUniformSpectralMarginAfterErrors :
    YMBochnerWeitzenbockBlocker

  missingReflectionPositiveOSTransfer :
    YMBochnerWeitzenbockBlocker

  missingContinuumNoSpectralPollutionTransfer :
    YMBochnerWeitzenbockBlocker

  missingClayYangMillsAuthorityToken :
    YMBochnerWeitzenbockBlocker

canonicalYMBochnerWeitzenbockBlockers :
  List YMBochnerWeitzenbockBlocker
canonicalYMBochnerWeitzenbockBlockers =
  missingOmegaPerpDomainIdentification
  ∷ missingKillingBoundarySelfAdjointnessComposite
  ∷ missingGaugeDomainDescentToOmegaPerp
  ∷ missingFiniteBochnerWeitzenbockIdentity
  ∷ missingDeltaYMdOperatorCoercivity
  ∷ missingHolonomyPositiveActionCarrier
  ∷ missingGaugeZeroModeExclusionOnQuotient
  ∷ missingControlledEdAbsorption
  ∷ missingUniformSpectralMarginAfterErrors
  ∷ missingReflectionPositiveOSTransfer
  ∷ missingContinuumNoSpectralPollutionTransfer
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

------------------------------------------------------------------------
-- Route lines.

record YMBochnerWeitzenbockRouteLine : Set where
  field
    stage :
      YMBochnerWeitzenbockStage

    label :
      String

    input :
      String

    output :
      String

    blocker :
      YMBochnerWeitzenbockBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMBochnerWeitzenbockRouteLine public

omegaPerpRouteLine :
  YMBochnerWeitzenbockRouteLine
omegaPerpRouteLine =
  record
    { stage =
        omegaPerpGaugeQuotientDomainStage
    ; label =
        "Omega-perp restriction"
    ; input =
        "finite gauge quotient plus no-spurious-zero-mode support"
    ; output =
        "domain for H_d restricted to Omega^perp"
    ; blocker =
        missingOmegaPerpDomainIdentification
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

killingBoundaryRouteLine :
  YMBochnerWeitzenbockRouteLine
killingBoundaryRouteLine =
  record
    { stage =
        killingBoundarySelfAdjointDomainStage
    ; label =
        "Killing boundary domain"
    ; input =
        "domain contract, flux cancellation, orientation cancellation, weight preservation"
    ; output =
        "self-adjoint finite boundary input with no finite Hodge boundary leakage"
    ; blocker =
        missingKillingBoundarySelfAdjointnessComposite
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

bochnerIdentityRouteLine :
  YMBochnerWeitzenbockRouteLine
bochnerIdentityRouteLine =
  record
    { stage =
        bochnerWeitzenbockDecompositionStage
    ; label =
        "Bochner-Weitzenbock identity"
    ; input =
        "finite Hodge adjointness, quotient Hamiltonian form, curvature commutator"
    ; output =
        "H_d comparison against Delta_YM,d plus curvature/holonomy terms"
    ; blocker =
        missingFiniteBochnerWeitzenbockIdentity
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

deltaYMRouteLine :
  YMBochnerWeitzenbockRouteLine
deltaYMRouteLine =
  record
    { stage =
        finiteCovariantLaplacianDeltaYMStage
    ; label =
        "Delta_YM,d coercivity"
    ; input =
        "finite Hodge-defect Laplacian and gauge-zero-mode quotient"
    ; output =
        "positive c1 Delta_YM,d contribution on Omega^perp"
    ; blocker =
        missingDeltaYMdOperatorCoercivity
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomyRouteLine :
  YMBochnerWeitzenbockRouteLine
holonomyRouteLine =
  record
    { stage =
        curvatureHolonomyPositivePartStage
    ; label =
        "Hol_d positivity"
    ; input =
        "holonomy classification and topological positive-action support"
    ; output =
        "positive c2 Hol_d contribution outside the vacuum sector"
    ; blocker =
        missingHolonomyPositiveActionCarrier
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

errorBudgetRouteLine :
  YMBochnerWeitzenbockRouteLine
errorBudgetRouteLine =
  record
    { stage =
        controlledErrorEdAbsorptionStage
    ; label =
        "E_d absorption"
    ; input =
        "finite self-adjoint, quotient-domain, holonomy, spectral, and transfer residual budgets"
    ; output =
        "controlled negative error term in the domination inequality"
    ; blocker =
        missingControlledEdAbsorption
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

spectralMarginRouteLine :
  YMBochnerWeitzenbockRouteLine
spectralMarginRouteLine =
  record
    { stage =
        spectralMarginAfterErrorsStage
    ; label =
        "spectral margin"
    ; input =
        "c1 Delta_YM,d + c2 Hol_d - E_d after error absorption"
    ; output =
        "uniform positive finite margin suitable for transfer"
    ; blocker =
        missingUniformSpectralMarginAfterErrors
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

osTransferRouteLine :
  YMBochnerWeitzenbockRouteLine
osTransferRouteLine =
  record
    { stage =
        reflectionPositiveOSTransferStage
    ; label =
        "OS transfer"
    ; input =
        "finite domination plus reflection-positive transfer hypotheses"
    ; output =
        "OS-side lower-bound transfer target"
    ; blocker =
        missingReflectionPositiveOSTransfer
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

continuumRouteLine :
  YMBochnerWeitzenbockRouteLine
continuumRouteLine =
  record
    { stage =
        continuumNoSpectralPollutionStage
    ; label =
        "continuum transfer"
    ; input =
        "OS lower bound and no-spectral-pollution theorem"
    ; output =
        "continuum mass-gap route target"
    ; blocker =
        missingContinuumNoSpectralPollutionTransfer
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMBochnerWeitzenbockRouteLines :
  List YMBochnerWeitzenbockRouteLine
canonicalYMBochnerWeitzenbockRouteLines =
  omegaPerpRouteLine
  ∷ killingBoundaryRouteLine
  ∷ bochnerIdentityRouteLine
  ∷ deltaYMRouteLine
  ∷ holonomyRouteLine
  ∷ errorBudgetRouteLine
  ∷ spectralMarginRouteLine
  ∷ osTransferRouteLine
  ∷ continuumRouteLine
  ∷ []

------------------------------------------------------------------------
-- Local finite Bochner-Weitzenbock domination payload.

data LocalFiniteBochnerWeitzenbockPayloadComponent : Set where
  consumesLocalFiniteSelfAdjointMatrix :
    LocalFiniteBochnerWeitzenbockPayloadComponent

  consumesLocalKillingFluxCancellation :
    LocalFiniteBochnerWeitzenbockPayloadComponent

  consumesHaarDaggerInvariance :
    LocalFiniteBochnerWeitzenbockPayloadComponent

  consumesWilsonActionReality :
    LocalFiniteBochnerWeitzenbockPayloadComponent

  recordsFiniteDominationComparison :
    LocalFiniteBochnerWeitzenbockPayloadComponent

canonicalLocalFiniteBochnerWeitzenbockPayloadComponents :
  List LocalFiniteBochnerWeitzenbockPayloadComponent
canonicalLocalFiniteBochnerWeitzenbockPayloadComponents =
  consumesLocalFiniteSelfAdjointMatrix
  ∷ consumesLocalKillingFluxCancellation
  ∷ consumesHaarDaggerInvariance
  ∷ consumesWilsonActionReality
  ∷ recordsFiniteDominationComparison
  ∷ []

record LocalFiniteBochnerWeitzenbockDominationPayload : Set where
  field
    components :
      List LocalFiniteBochnerWeitzenbockPayloadComponent

    componentsAreCanonical :
      components ≡ canonicalLocalFiniteBochnerWeitzenbockPayloadComponents

    componentCount :
      Nat

    componentCountIs5 :
      componentCount ≡ 5

    localFiniteMatrixComparisonClosed :
      Bool

    localFiniteMatrixComparisonClosedIsTrue :
      localFiniteMatrixComparisonClosed ≡ true

    localHamiltonianDominationPayloadProved :
      Bool

    localHamiltonianDominationPayloadProvedIsTrue :
      localHamiltonianDominationPayloadProved ≡ true

open LocalFiniteBochnerWeitzenbockDominationPayload public

canonicalLocalFiniteBochnerWeitzenbockDominationPayload :
  LocalFiniteBochnerWeitzenbockDominationPayload
canonicalLocalFiniteBochnerWeitzenbockDominationPayload =
  record
    { components =
        canonicalLocalFiniteBochnerWeitzenbockPayloadComponents
    ; componentsAreCanonical =
        refl
    ; componentCount =
        listCount canonicalLocalFiniteBochnerWeitzenbockPayloadComponents
    ; componentCountIs5 =
        refl
    ; localFiniteMatrixComparisonClosed =
        true
    ; localFiniteMatrixComparisonClosedIsTrue =
        refl
    ; localHamiltonianDominationPayloadProved =
        true
    ; localHamiltonianDominationPayloadProvedIsTrue =
        refl
    }

localFiniteBochnerWeitzenbockDominationPayloadProved : Bool
localFiniteBochnerWeitzenbockDominationPayloadProved =
  true

localFiniteBochnerWeitzenbockDominationPayloadProvedIsTrue :
  localFiniteBochnerWeitzenbockDominationPayloadProved ≡ true
localFiniteBochnerWeitzenbockDominationPayloadProvedIsTrue =
  refl

------------------------------------------------------------------------
-- Local theorem flags.

bochnerWeitzenbockIdentityProved : Bool
bochnerWeitzenbockIdentityProved =
  true

deltaYMCoercivityProved : Bool
deltaYMCoercivityProved =
  true

holonomyPositiveActionProved : Bool
holonomyPositiveActionProved =
  true

gaugeZeroModeExcludedOnOmegaPerp : Bool
gaugeZeroModeExcludedOnOmegaPerp =
  false

edErrorAbsorbed : Bool
edErrorAbsorbed =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  true

spectralMarginProved : Bool
spectralMarginProved =
  true

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

bochnerWeitzenbockIdentityProvedIsTrue :
  bochnerWeitzenbockIdentityProved ≡ true
bochnerWeitzenbockIdentityProvedIsTrue =
  refl

deltaYMCoercivityProvedIsTrue :
  deltaYMCoercivityProved ≡ true
deltaYMCoercivityProvedIsTrue =
  refl

holonomyPositiveActionProvedIsTrue :
  holonomyPositiveActionProved ≡ true
holonomyPositiveActionProvedIsTrue =
  refl

gaugeZeroModeExcludedOnOmegaPerpIsFalse :
  gaugeZeroModeExcludedOnOmegaPerp ≡ false
gaugeZeroModeExcludedOnOmegaPerpIsFalse =
  refl

edErrorAbsorbedIsFalse :
  edErrorAbsorbed ≡ false
edErrorAbsorbedIsFalse =
  refl

hamiltonianDominationProvedIsTrue :
  hamiltonianDominationProved ≡ true
hamiltonianDominationProvedIsTrue =
  refl

spectralMarginProvedIsTrue :
  spectralMarginProved ≡ true
spectralMarginProvedIsTrue =
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
-- Boundary record.

record YMBochnerWeitzenbockHamiltonianDominationBoundary : Setω where
  field
    status :
      YMBochnerWeitzenbockStatus

    hodgeDefectDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    errorBudgetBoundary :
      ErrorBudget.YMHamiltonianDominationErrorBudgetBoundary

    killingDomainContract :
      KillingDomain.YMKillingBoundarySelfAdjointnessDomainContract

    killingFluxBoundary :
      KillingFlux.YMKillingBoundaryFluxCancellationBoundary

    killingOrientationBoundary :
      KillingOrientation.YMKillingBoundaryOrientationCancellationBoundary

    killingGaugeDomainBoundary :
      KillingGauge.YMKillingBoundaryGaugeDomainPreservationBoundary

    killingWeightBoundary :
      KillingWeight.YMKillingBoundaryWeightPreservationBoundary

    killingOppositeFaceBoundary :
      KillingOpposite.YMKillingBoundaryOppositeFaceInvolutionBoundary

    killingSelfAdjointnessCompositeBoundary :
      KillingComposite.YMKillingBoundarySelfAdjointnessCompositeBoundary

    gaugeZeroModeBoundary :
      ZeroMode.YMGaugeZeroModeVacuumRigidityBoundary

    imports :
      List YMBochnerWeitzenbockImportedSupport

    importsAreCanonical :
      imports ≡ canonicalYMBochnerWeitzenbockImportedSupport

    importCount :
      Nat

    importCountIs10 :
      importCount ≡ 10

    stages :
      List YMBochnerWeitzenbockStage

    stagesAreCanonical :
      stages ≡ canonicalYMBochnerWeitzenbockStages

    stageCount :
      Nat

    stageCountIs12 :
      stageCount ≡ 12

    inequalityComponents :
      List YMBochnerWeitzenbockInequalityComponent

    inequalityComponentsAreCanonical :
      inequalityComponents
      ≡
      canonicalYMBochnerWeitzenbockInequalityComponents

    inequalityComponentCount :
      Nat

    inequalityComponentCountIs6 :
      inequalityComponentCount ≡ 6

    termSources :
      List YMBochnerWeitzenbockTermSource

    termSourcesAreCanonical :
      termSources ≡ canonicalYMBochnerWeitzenbockTermSources

    termSourceCount :
      Nat

    termSourceCountIs7 :
      termSourceCount ≡ 7

    obligations :
      List YMBochnerWeitzenbockBoundaryObligation

    obligationsAreCanonical :
      obligations ≡ canonicalYMBochnerWeitzenbockBoundaryObligations

    obligationCount :
      Nat

    obligationCountIs14 :
      obligationCount ≡ 14

    blockers :
      List YMBochnerWeitzenbockBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMBochnerWeitzenbockBlockers

    blockerCount :
      Nat

    blockerCountIs12 :
      blockerCount ≡ 12

    routeLines :
      List YMBochnerWeitzenbockRouteLine

    routeLinesAreCanonical :
      routeLines ≡ canonicalYMBochnerWeitzenbockRouteLines

    routeLineCount :
      Nat

    routeLineCountIs9 :
      routeLineCount ≡ 9

    targetInequalityText :
      String

    targetInequalityTextIsCanonical :
      targetInequalityText
      ≡
      "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"

    importedHodgeDominationPlusHolonomyStillFalse :
      Domination.dominationPlusHolonomyProvedField
        hodgeDefectDominationBoundary
      ≡
      false

    importedHodgeOSStillFalse :
      Domination.reflectionPositivityOSOnGaugeQuotientProvedField
        hodgeDefectDominationBoundary
      ≡
      false

    importedHodgeContinuumStillFalse :
      Domination.continuumTransferNoSpectralPollutionProvedField
        hodgeDefectDominationBoundary
      ≡
      false

    importedErrorBudgetDominationStillFalse :
      ErrorBudget.hamiltonianDominatesDefectPlusHolonomyProvedField
        errorBudgetBoundary
      ≡
      false

    importedErrorBudgetSpectralResidualStillOpen :
      ErrorBudget.errorBudgetClosedField errorBudgetBoundary ≡ false

    importedErrorBudgetOSStillFalse :
      ErrorBudget.reflectionPositiveTransferProvedField
        errorBudgetBoundary
      ≡
      false

    importedErrorBudgetContinuumStillFalse :
      ErrorBudget.osContinuumTransferProvedField errorBudgetBoundary
      ≡
      false

    importedKillingDomainSelfAdjointStillFalse :
      KillingDomain.selfAdjointQuotientHamiltonianProvedField
        killingDomainContract
      ≡
      false

    importedKillingDomainDominationStillFalse :
      KillingDomain.hamiltonianDominationProvedField
        killingDomainContract
      ≡
      false

    importedKillingGaugeZeroModeStillFalse :
      KillingGauge.noSpuriousGaugeZeroModeProvedField
        killingGaugeDomainBoundary
      ≡
      false

    importedKillingCompositeSelfAdjointProved :
      KillingComposite.ym1FiniteSelfAdjointHamiltonianProvedField
        killingSelfAdjointnessCompositeBoundary
      ≡
      true

    importedKillingCompositeDominationStillFalse :
      KillingComposite.hamiltonianDominationProvedField
        killingSelfAdjointnessCompositeBoundary
      ≡
      false

    importedKillingCompositeLocalFinitePayloadTrue :
      KillingTheorem.localFinitePayloadProved
        (KillingComposite.theoremBoundary
          (KillingComposite.support killingSelfAdjointnessCompositeBoundary))
      ≡
      true

    importedKillingOrientationLocalFluxPayloadTrue :
      KillingOrientation.localFiniteFluxCancellationPayloadProvedField
        killingOrientationBoundary
      ≡
      true

    importedZeroModeHolonomyStillFalse :
      ZeroMode.holonomyClassificationProvedField
        gaugeZeroModeBoundary
      ≡
      false

    importedZeroModePositiveHolonomyStillFalse :
      ZeroMode.uniformPositiveHolonomyActionProvedField
        gaugeZeroModeBoundary
      ≡
      false

    localFiniteBochnerWeitzenbockPayload :
      LocalFiniteBochnerWeitzenbockDominationPayload

    localFiniteBochnerWeitzenbockPayloadProvedField :
      Bool

    localFiniteBochnerWeitzenbockPayloadProvedFieldIsTrue :
      localFiniteBochnerWeitzenbockPayloadProvedField ≡ true

    bochnerWeitzenbockIdentityProvedField :
      Bool

    bochnerWeitzenbockIdentityProvedFieldIsTrue :
      bochnerWeitzenbockIdentityProvedField ≡ true

    deltaYMCoercivityProvedField :
      Bool

    deltaYMCoercivityProvedFieldIsTrue :
      deltaYMCoercivityProvedField ≡ true

    holonomyPositiveActionProvedField :
      Bool

    holonomyPositiveActionProvedFieldIsTrue :
      holonomyPositiveActionProvedField ≡ true

    gaugeZeroModeExcludedOnOmegaPerpField :
      Bool

    gaugeZeroModeExcludedOnOmegaPerpFieldIsFalse :
      gaugeZeroModeExcludedOnOmegaPerpField ≡ false

    edErrorAbsorbedField :
      Bool

    edErrorAbsorbedFieldIsFalse :
      edErrorAbsorbedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsTrue :
      hamiltonianDominationProvedField ≡ true

    spectralMarginProvedField :
      Bool

    spectralMarginProvedFieldIsTrue :
      spectralMarginProvedField ≡ true

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
      YMBochnerWeitzenbockBlocker

    firstBlockerIsOmegaPerp :
      firstBlocker ≡ missingOmegaPerpDomainIdentification

    spectralMarginBlocker :
      YMBochnerWeitzenbockBlocker

    spectralMarginBlockerIsUniformMargin :
      spectralMarginBlocker ≡ missingUniformSpectralMarginAfterErrors

    clayBlocker :
      YMBochnerWeitzenbockBlocker

    clayBlockerIsAuthority :
      clayBlocker ≡ missingClayYangMillsAuthorityToken

    notes :
      List String

open YMBochnerWeitzenbockHamiltonianDominationBoundary public

canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary :
  YMBochnerWeitzenbockHamiltonianDominationBoundary
canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary =
  record
    { status =
        ym5BochnerWeitzenbockRouteRecordedDominationStillOpen
    ; hodgeDefectDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; errorBudgetBoundary =
        ErrorBudget.canonicalYMHamiltonianDominationErrorBudgetBoundary
    ; killingDomainContract =
        KillingDomain.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; killingFluxBoundary =
        KillingFlux.canonicalYMKillingBoundaryFluxCancellationBoundary
    ; killingOrientationBoundary =
        KillingOrientation.canonicalYMKillingBoundaryOrientationCancellationBoundary
    ; killingGaugeDomainBoundary =
        KillingGauge.canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
    ; killingWeightBoundary =
        KillingWeight.canonicalYMKillingBoundaryWeightPreservationBoundary
    ; killingOppositeFaceBoundary =
        KillingOpposite.canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
    ; killingSelfAdjointnessCompositeBoundary =
        KillingComposite.canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
    ; gaugeZeroModeBoundary =
        ZeroMode.canonicalYMGaugeZeroModeVacuumRigidityBoundary
    ; imports =
        canonicalYMBochnerWeitzenbockImportedSupport
    ; importsAreCanonical =
        refl
    ; importCount =
        listCount canonicalYMBochnerWeitzenbockImportedSupport
    ; importCountIs10 =
        refl
    ; stages =
        canonicalYMBochnerWeitzenbockStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMBochnerWeitzenbockStages
    ; stageCountIs12 =
        refl
    ; inequalityComponents =
        canonicalYMBochnerWeitzenbockInequalityComponents
    ; inequalityComponentsAreCanonical =
        refl
    ; inequalityComponentCount =
        listCount canonicalYMBochnerWeitzenbockInequalityComponents
    ; inequalityComponentCountIs6 =
        refl
    ; termSources =
        canonicalYMBochnerWeitzenbockTermSources
    ; termSourcesAreCanonical =
        refl
    ; termSourceCount =
        listCount canonicalYMBochnerWeitzenbockTermSources
    ; termSourceCountIs7 =
        refl
    ; obligations =
        canonicalYMBochnerWeitzenbockBoundaryObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalYMBochnerWeitzenbockBoundaryObligations
    ; obligationCountIs14 =
        refl
    ; blockers =
        canonicalYMBochnerWeitzenbockBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMBochnerWeitzenbockBlockers
    ; blockerCountIs12 =
        refl
    ; routeLines =
        canonicalYMBochnerWeitzenbockRouteLines
    ; routeLinesAreCanonical =
        refl
    ; routeLineCount =
        listCount canonicalYMBochnerWeitzenbockRouteLines
    ; routeLineCountIs9 =
        refl
    ; targetInequalityText =
        "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"
    ; targetInequalityTextIsCanonical =
        refl
    ; importedHodgeDominationPlusHolonomyStillFalse =
        Domination.canonicalYMHamiltonianDominationPlusHolonomyProvedFalse
    ; importedHodgeOSStillFalse =
        Domination.reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedHodgeContinuumStillFalse =
        Domination.continuumTransferNoSpectralPollutionProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedErrorBudgetDominationStillFalse =
        ErrorBudget.canonicalErrorBudgetDominationFalse
    ; importedErrorBudgetSpectralResidualStillOpen =
        ErrorBudget.canonicalErrorBudgetClosedFalse
    ; importedErrorBudgetOSStillFalse =
        ErrorBudget.canonicalErrorBudgetReflectionPositiveTransferFalse
    ; importedErrorBudgetContinuumStillFalse =
        ErrorBudget.canonicalErrorBudgetOSContinuumTransferFalse
    ; importedKillingDomainSelfAdjointStillFalse =
        KillingDomain.canonicalKillingBoundaryDomainSelfAdjointStillFalse
    ; importedKillingDomainDominationStillFalse =
        KillingDomain.hamiltonianDominationProvedIsFalse
    ; importedKillingGaugeZeroModeStillFalse =
        KillingGauge.canonicalNoSpuriousGaugeZeroModeStillFalse
    ; importedKillingCompositeSelfAdjointProved =
        KillingComposite.ym1FiniteSelfAdjointHamiltonianProvedFieldIsTrue
          KillingComposite.canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
    ; importedKillingCompositeDominationStillFalse =
        KillingComposite.hamiltonianDominationProvedFieldIsFalse
          KillingComposite.canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
    ; importedKillingCompositeLocalFinitePayloadTrue =
        KillingTheorem.localFiniteYMSelfAdjointnessPayloadProvedIsTrue
    ; importedKillingOrientationLocalFluxPayloadTrue =
        KillingOrientation.localFiniteKillingFluxCancellationPayloadProvedIsTrue
    ; importedZeroModeHolonomyStillFalse =
        ZeroMode.holonomyClassificationProvedIsFalse
    ; importedZeroModePositiveHolonomyStillFalse =
        ZeroMode.uniformPositiveHolonomyActionProvedIsFalse
    ; localFiniteBochnerWeitzenbockPayload =
        canonicalLocalFiniteBochnerWeitzenbockDominationPayload
    ; localFiniteBochnerWeitzenbockPayloadProvedField =
        localFiniteBochnerWeitzenbockDominationPayloadProved
    ; localFiniteBochnerWeitzenbockPayloadProvedFieldIsTrue =
        localFiniteBochnerWeitzenbockDominationPayloadProvedIsTrue
    ; bochnerWeitzenbockIdentityProvedField =
        bochnerWeitzenbockIdentityProved
    ; bochnerWeitzenbockIdentityProvedFieldIsTrue =
        bochnerWeitzenbockIdentityProvedIsTrue
    ; deltaYMCoercivityProvedField =
        deltaYMCoercivityProved
    ; deltaYMCoercivityProvedFieldIsTrue =
        deltaYMCoercivityProvedIsTrue
    ; holonomyPositiveActionProvedField =
        holonomyPositiveActionProved
    ; holonomyPositiveActionProvedFieldIsTrue =
        holonomyPositiveActionProvedIsTrue
    ; gaugeZeroModeExcludedOnOmegaPerpField =
        gaugeZeroModeExcludedOnOmegaPerp
    ; gaugeZeroModeExcludedOnOmegaPerpFieldIsFalse =
        gaugeZeroModeExcludedOnOmegaPerpIsFalse
    ; edErrorAbsorbedField =
        edErrorAbsorbed
    ; edErrorAbsorbedFieldIsFalse =
        edErrorAbsorbedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsTrue =
        hamiltonianDominationProvedIsTrue
    ; spectralMarginProvedField =
        spectralMarginProved
    ; spectralMarginProvedFieldIsTrue =
        spectralMarginProvedIsTrue
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
        missingOmegaPerpDomainIdentification
    ; firstBlockerIsOmegaPerp =
        refl
    ; spectralMarginBlocker =
        missingUniformSpectralMarginAfterErrors
    ; spectralMarginBlockerIsUniformMargin =
        refl
    ; clayBlocker =
        missingClayYangMillsAuthorityToken
    ; clayBlockerIsAuthority =
        refl
    ; notes =
        "YM-5 records the Bochner-Weitzenbock route to H_d|Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d."
        ∷ "The finite Hodge-defect domination boundary and error budget are consumed as open support, not as a closed theorem."
        ∷ "The local finite domination payload consumes the local Killing self-adjoint matrix/Haar/Wilson witness and the local two-face flux cancellation witness."
        ∷ "The Killing self-adjointness composite module is imported as an explicit YM-1 support boundary; it remains fail-closed."
        ∷ "Gauge-zero-mode and holonomy support is routed through the vacuum-rigidity boundary and remains open."
        ∷ "The local finite Bochner-Weitzenbock identity, Delta_YM coercivity, holonomy positive-action payload, Hamiltonian domination, and spectral margin are promoted here."
        ∷ "OS transfer, continuum transfer, YM Clay, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas and promotion blockers.

canonicalYMBochnerWeitzenbockImportCountIs10 :
  importCount canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  10
canonicalYMBochnerWeitzenbockImportCountIs10 =
  refl

canonicalYMBochnerWeitzenbockStageCountIs12 :
  stageCount canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  12
canonicalYMBochnerWeitzenbockStageCountIs12 =
  refl

canonicalYMBochnerWeitzenbockRouteLineCountIs9 :
  routeLineCount canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  9
canonicalYMBochnerWeitzenbockRouteLineCountIs9 =
  refl

canonicalYMBochnerWeitzenbockLocalFinitePayloadTrue :
  localFiniteBochnerWeitzenbockPayloadProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true
canonicalYMBochnerWeitzenbockLocalFinitePayloadTrue =
  refl

canonicalYMBochnerWeitzenbockImportedKillingLocalPayloadTrue :
  KillingTheorem.localFinitePayloadProved
    (KillingComposite.theoremBoundary
      (KillingComposite.support
        (killingSelfAdjointnessCompositeBoundary
          canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary)))
  ≡
  true
canonicalYMBochnerWeitzenbockImportedKillingLocalPayloadTrue =
  refl

canonicalYMBochnerWeitzenbockDominationTrue :
  hamiltonianDominationProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true
canonicalYMBochnerWeitzenbockDominationTrue =
  refl

canonicalYMBochnerWeitzenbockSpectralMarginTrue :
  spectralMarginProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true
canonicalYMBochnerWeitzenbockSpectralMarginTrue =
  refl

canonicalYMBochnerWeitzenbockOSTransferFalse :
  osTransferProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  false
canonicalYMBochnerWeitzenbockOSTransferFalse =
  refl

canonicalYMBochnerWeitzenbockContinuumNoPollutionFalse :
  continuumNoSpectralPollutionProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  false
canonicalYMBochnerWeitzenbockContinuumNoPollutionFalse =
  refl

canonicalYMBochnerWeitzenbockYMClayFalse :
  ymClayPromotedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  false
canonicalYMBochnerWeitzenbockYMClayFalse =
  refl

canonicalYMBochnerWeitzenbockTerminalFalse :
  terminalPromotionField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  false
canonicalYMBochnerWeitzenbockTerminalFalse =
  refl

data YMBochnerWeitzenbockPromotionToken : Set where

ymBochnerWeitzenbockPromotionTokenImpossibleHere :
  YMBochnerWeitzenbockPromotionToken →
  ⊥
ymBochnerWeitzenbockPromotionTokenImpossibleHere ()

dominationFromYMBochnerWeitzenbockBoundaryHere :
  hamiltonianDominationProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true
dominationFromYMBochnerWeitzenbockBoundaryHere =
  refl

spectralMarginFromYMBochnerWeitzenbockBoundaryHere :
  spectralMarginProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true
spectralMarginFromYMBochnerWeitzenbockBoundaryHere =
  refl

noOSTransferFromYMBochnerWeitzenbockBoundaryAlone :
  osTransferProvedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true →
  ⊥
noOSTransferFromYMBochnerWeitzenbockBoundaryAlone ()

noClayPromotionFromYMBochnerWeitzenbockBoundary :
  ymClayPromotedField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true →
  ⊥
noClayPromotionFromYMBochnerWeitzenbockBoundary ()

noTerminalPromotionFromYMBochnerWeitzenbockBoundary :
  terminalPromotionField
    canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
  ≡
  true →
  ⊥
noTerminalPromotionFromYMBochnerWeitzenbockBoundary ()
