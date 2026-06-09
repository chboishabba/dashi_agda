module DASHI.Physics.Closure.YMSpectralMarginFromHolonomyDominationBoundary where

-- Yang-Mills spectral margin from holonomy-domination boundary.
--
-- This module records the fail-closed bridge
--
--   domination + uniform holonomy action
--   -> finite quotient spectral-margin error budget
--   -> proxy diagnostic consistency
--   -> OS/continuum transfer preconditions.
--
-- It is a receipt only.  It does not prove Hamiltonian domination, uniform
-- holonomy action, finite spectral margin, reflection positivity, BT-to-OS
-- transfer, continuum no-pollution, Yang-Mills Clay, or terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMHolonomyActionToDominationCompositeBoundary
  as HolDom
import DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary
  as Margin
import DASHI.Physics.Closure.YMDominationSpectralMarginProxyHarnessResult
  as Proxy
import DASHI.Physics.Closure.YMBruhatTitsToOSLatticeTransferBoundary
  as BTOS

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMSpectralMarginFromHolonomySupport : Set where
  holonomyActionToDominationCompositeImported :
    YMSpectralMarginFromHolonomySupport

  spectralMarginErrorBudgetCompositeImported :
    YMSpectralMarginFromHolonomySupport

  dominationSpectralMarginProxyHarnessImported :
    YMSpectralMarginFromHolonomySupport

  bruhatTitsToOSLatticeTransferBoundaryImported :
    YMSpectralMarginFromHolonomySupport

canonicalYMSpectralMarginFromHolonomySupport :
  List YMSpectralMarginFromHolonomySupport
canonicalYMSpectralMarginFromHolonomySupport =
  holonomyActionToDominationCompositeImported
  ∷ spectralMarginErrorBudgetCompositeImported
  ∷ dominationSpectralMarginProxyHarnessImported
  ∷ bruhatTitsToOSLatticeTransferBoundaryImported
  ∷ []

supportCount : Nat
supportCount =
  listCount canonicalYMSpectralMarginFromHolonomySupport

supportCountIs4 : supportCount ≡ 4
supportCountIs4 =
  refl

record YMSpectralMarginFromHolonomyInputPack : Setω where
  field
    holonomyDominationBoundary :
      HolDom.YMHolonomyActionToDominationCompositeBoundary

    spectralMarginErrorBudgetBoundary :
      Margin.YMSpectralMarginErrorBudgetCompositeBoundary

    dominationSpectralMarginProxy :
      Proxy.YMDominationSpectralMarginProxyHarnessResult

    bruhatTitsToOSBoundary :
      BTOS.YMBruhatTitsToOSLatticeTransferBoundary

    holonomyDominationBoundaryCanonical :
      Bool

    spectralMarginErrorBudgetBoundaryCanonical :
      Bool

    dominationSpectralMarginProxyCanonical :
      Bool

    bruhatTitsToOSBoundaryCanonical :
      Bool

    holonomyDominationBoundaryCanonicalIsTrue :
      holonomyDominationBoundaryCanonical ≡ true

    spectralMarginErrorBudgetBoundaryCanonicalIsTrue :
      spectralMarginErrorBudgetBoundaryCanonical ≡ true

    dominationSpectralMarginProxyCanonicalIsTrue :
      dominationSpectralMarginProxyCanonical ≡ true

    bruhatTitsToOSBoundaryCanonicalIsTrue :
      bruhatTitsToOSBoundaryCanonical ≡ true

open YMSpectralMarginFromHolonomyInputPack public

canonicalYMSpectralMarginFromHolonomyInputPack :
  YMSpectralMarginFromHolonomyInputPack
canonicalYMSpectralMarginFromHolonomyInputPack =
  record
    { holonomyDominationBoundary =
        HolDom.canonicalYMHolonomyActionToDominationCompositeBoundary
    ; spectralMarginErrorBudgetBoundary =
        Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
    ; dominationSpectralMarginProxy =
        Proxy.canonicalYMDominationSpectralMarginProxyHarnessResult
    ; bruhatTitsToOSBoundary =
        BTOS.canonicalYMBruhatTitsToOSLatticeTransferBoundary
    ; holonomyDominationBoundaryCanonical =
        true
    ; spectralMarginErrorBudgetBoundaryCanonical =
        true
    ; dominationSpectralMarginProxyCanonical =
        true
    ; bruhatTitsToOSBoundaryCanonical =
        true
    ; holonomyDominationBoundaryCanonicalIsTrue =
        refl
    ; spectralMarginErrorBudgetBoundaryCanonicalIsTrue =
        refl
    ; dominationSpectralMarginProxyCanonicalIsTrue =
        refl
    ; bruhatTitsToOSBoundaryCanonicalIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Bridge stages and blockers.

data YMSpectralMarginFromHolonomyStage : Set where
  finiteGaugeQuotientCarrierStage :
    YMSpectralMarginFromHolonomyStage

  killingBoundarySelfAdjointHamiltonianStage :
    YMSpectralMarginFromHolonomyStage

  holonomyFloorIntoDominationStage :
    YMSpectralMarginFromHolonomyStage

  bochnerDefectPlusHolonomyDominationStage :
    YMSpectralMarginFromHolonomyStage

  finiteErrorBudgetAbsorptionStage :
    YMSpectralMarginFromHolonomyStage

  proxySpectralMarginDiagnosticStage :
    YMSpectralMarginFromHolonomyStage

  uniformFiniteSpectralMarginStage :
    YMSpectralMarginFromHolonomyStage

  reflectionPositiveTransferMatrixPreconditionStage :
    YMSpectralMarginFromHolonomyStage

  bruhatTitsWilsonComparisonPreconditionStage :
    YMSpectralMarginFromHolonomyStage

  osSchwingerFunctionTransferPreconditionStage :
    YMSpectralMarginFromHolonomyStage

  noDepthSpectralPollutionPreconditionStage :
    YMSpectralMarginFromHolonomyStage

  noContinuumSpectralPollutionPreconditionStage :
    YMSpectralMarginFromHolonomyStage

  clayYangMillsAuthorityGuardStage :
    YMSpectralMarginFromHolonomyStage

canonicalYMSpectralMarginFromHolonomyStages :
  List YMSpectralMarginFromHolonomyStage
canonicalYMSpectralMarginFromHolonomyStages =
  finiteGaugeQuotientCarrierStage
  ∷ killingBoundarySelfAdjointHamiltonianStage
  ∷ holonomyFloorIntoDominationStage
  ∷ bochnerDefectPlusHolonomyDominationStage
  ∷ finiteErrorBudgetAbsorptionStage
  ∷ proxySpectralMarginDiagnosticStage
  ∷ uniformFiniteSpectralMarginStage
  ∷ reflectionPositiveTransferMatrixPreconditionStage
  ∷ bruhatTitsWilsonComparisonPreconditionStage
  ∷ osSchwingerFunctionTransferPreconditionStage
  ∷ noDepthSpectralPollutionPreconditionStage
  ∷ noContinuumSpectralPollutionPreconditionStage
  ∷ clayYangMillsAuthorityGuardStage
  ∷ []

stageCount : Nat
stageCount =
  listCount canonicalYMSpectralMarginFromHolonomyStages

stageCountIs13 : stageCount ≡ 13
stageCountIs13 =
  refl

stageLabel :
  YMSpectralMarginFromHolonomyStage →
  String
stageLabel finiteGaugeQuotientCarrierStage =
  "finite gauge quotient carrier"
stageLabel killingBoundarySelfAdjointHamiltonianStage =
  "Killing-boundary self-adjoint Hamiltonian"
stageLabel holonomyFloorIntoDominationStage =
  "holonomy floor into domination"
stageLabel bochnerDefectPlusHolonomyDominationStage =
  "Bochner defect-plus-holonomy domination"
stageLabel finiteErrorBudgetAbsorptionStage =
  "finite E_d absorption"
stageLabel proxySpectralMarginDiagnosticStage =
  "proxy spectral-margin diagnostic"
stageLabel uniformFiniteSpectralMarginStage =
  "uniform finite spectral margin"
stageLabel reflectionPositiveTransferMatrixPreconditionStage =
  "reflection-positive transfer-matrix precondition"
stageLabel bruhatTitsWilsonComparisonPreconditionStage =
  "BT-to-Wilson action comparison precondition"
stageLabel osSchwingerFunctionTransferPreconditionStage =
  "OS Schwinger-function transfer precondition"
stageLabel noDepthSpectralPollutionPreconditionStage =
  "no depth-limit spectral pollution"
stageLabel noContinuumSpectralPollutionPreconditionStage =
  "no continuum-limit spectral pollution"
stageLabel clayYangMillsAuthorityGuardStage =
  "Clay Yang-Mills authority guard"

data YMSpectralMarginFromHolonomyBlocker : Set where
  missingFiniteGaugeQuotientCarrier :
    YMSpectralMarginFromHolonomyBlocker

  missingSelfAdjointHamiltonianOnGaugeQuotient :
    YMSpectralMarginFromHolonomyBlocker

  missingUniformHolonomyFloor :
    YMSpectralMarginFromHolonomyBlocker

  missingBochnerDefectPlusHolonomyDomination :
    YMSpectralMarginFromHolonomyBlocker

  missingFiniteErrorAbsorption :
    YMSpectralMarginFromHolonomyBlocker

  proxyDiagnosticNotATheorem :
    YMSpectralMarginFromHolonomyBlocker

  missingUniformFiniteSpectralMargin :
    YMSpectralMarginFromHolonomyBlocker

  missingBTWilsonActionComparison :
    YMSpectralMarginFromHolonomyBlocker

  missingReflectionPositiveTransferMatrix :
    YMSpectralMarginFromHolonomyBlocker

  missingOSSchwingerFunctionTransfer :
    YMSpectralMarginFromHolonomyBlocker

  missingNoDepthSpectralPollution :
    YMSpectralMarginFromHolonomyBlocker

  missingNoContinuumSpectralPollution :
    YMSpectralMarginFromHolonomyBlocker

  externalAuthorityCandidatesNotAccepted :
    YMSpectralMarginFromHolonomyBlocker

  missingClayYangMillsAuthority :
    YMSpectralMarginFromHolonomyBlocker

canonicalYMSpectralMarginFromHolonomyBlockers :
  List YMSpectralMarginFromHolonomyBlocker
canonicalYMSpectralMarginFromHolonomyBlockers =
  missingFiniteGaugeQuotientCarrier
  ∷ missingSelfAdjointHamiltonianOnGaugeQuotient
  ∷ missingUniformHolonomyFloor
  ∷ missingBochnerDefectPlusHolonomyDomination
  ∷ missingFiniteErrorAbsorption
  ∷ proxyDiagnosticNotATheorem
  ∷ missingUniformFiniteSpectralMargin
  ∷ missingBTWilsonActionComparison
  ∷ missingReflectionPositiveTransferMatrix
  ∷ missingOSSchwingerFunctionTransfer
  ∷ missingNoDepthSpectralPollution
  ∷ missingNoContinuumSpectralPollution
  ∷ externalAuthorityCandidatesNotAccepted
  ∷ missingClayYangMillsAuthority
  ∷ []

blockerCount : Nat
blockerCount =
  listCount canonicalYMSpectralMarginFromHolonomyBlockers

blockerCountIs14 : blockerCount ≡ 14
blockerCountIs14 =
  refl

------------------------------------------------------------------------
-- Route rows.

record YMSpectralMarginFromHolonomyRouteRow : Set where
  field
    stage :
      YMSpectralMarginFromHolonomyStage

    label :
      String

    consumes :
      String

    produces :
      String

    blocker :
      YMSpectralMarginFromHolonomyBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMSpectralMarginFromHolonomyRouteRow public

quotientCarrierRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
quotientCarrierRouteRow =
  record
    { stage =
        finiteGaugeQuotientCarrierStage
    ; label =
        "quotient carrier"
    ; consumes =
        "finite BT gauge fields, gauge action, invariant measure, and Killing domain"
    ; produces =
        "Hilbert carrier L2(A_d/G_d) for finite Hamiltonian"
    ; blocker =
        missingFiniteGaugeQuotientCarrier
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

selfAdjointRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
selfAdjointRouteRow =
  record
    { stage =
        killingBoundarySelfAdjointHamiltonianStage
    ; label =
        "self-adjoint quotient Hamiltonian"
    ; consumes =
        "Killing boundary cancellation and gauge-preserved domain"
    ; produces =
        "symmetric closed finite H_d on the gauge quotient"
    ; blocker =
        missingSelfAdjointHamiltonianOnGaugeQuotient
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomyFloorRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
holonomyFloorRouteRow =
  record
    { stage =
        holonomyFloorIntoDominationStage
    ; label =
        "holonomy floor"
    ; consumes =
        "uniform positive Wilson/holonomy action boundary"
    ; produces =
        "positive c2 Hol_d contribution outside the vacuum"
    ; blocker =
        missingUniformHolonomyFloor
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

dominationRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
dominationRouteRow =
  record
    { stage =
        bochnerDefectPlusHolonomyDominationStage
    ; label =
        "defect plus holonomy domination"
    ; consumes =
        "Bochner-Weitzenbock kinetic term, Hol_d floor, and E_d budget"
    ; produces =
        "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"
    ; blocker =
        missingBochnerDefectPlusHolonomyDomination
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

errorAbsorptionRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
errorAbsorptionRouteRow =
  record
    { stage =
        finiteErrorBudgetAbsorptionStage
    ; label =
        "E_d absorption"
    ; consumes =
        "kinetic margin, holonomy floor, quotient-domain residual, and E_d"
    ; produces =
        "positive finite spectral-margin budget candidate"
    ; blocker =
        missingFiniteErrorAbsorption
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

proxyDiagnosticRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
proxyDiagnosticRouteRow =
  record
    { stage =
        proxySpectralMarginDiagnosticStage
    ; label =
        "proxy diagnostic"
    ; consumes =
        "finite symmetric-matrix proxy good and bad cases"
    ; produces =
        "diagnostic evidence only, not a theorem"
    ; blocker =
        proxyDiagnosticNotATheorem
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

finiteSpectralMarginRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
finiteSpectralMarginRouteRow =
  record
    { stage =
        uniformFiniteSpectralMarginStage
    ; label =
        "finite spectral margin"
    ; consumes =
        "self-adjoint quotient H_d and absorbed domination budget"
    ; produces =
        "lambda1(H_d | Omega^perp) >= m_d > 0 with uniform constants"
    ; blocker =
        missingUniformFiniteSpectralMargin
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

reflectionRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
reflectionRouteRow =
  record
    { stage =
        reflectionPositiveTransferMatrixPreconditionStage
    ; label =
        "reflection positivity"
    ; consumes =
        "finite quotient Hamiltonian and transfer matrix T_d = exp(-a H_d)"
    ; produces =
        "reflection-positive Schwinger-function precondition"
    ; blocker =
        missingReflectionPositiveTransferMatrix
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

btWilsonRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
btWilsonRouteRow =
  record
    { stage =
        bruhatTitsWilsonComparisonPreconditionStage
    ; label =
        "BT Wilson comparison"
    ; consumes =
        "BT finite gauge action and Wilson plaquette action class"
    ; produces =
        "action-comparison hypothesis for external OS framework"
    ; blocker =
        missingBTWilsonActionComparison
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

osTransferRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
osTransferRouteRow =
  record
    { stage =
        osSchwingerFunctionTransferPreconditionStage
    ; label =
        "OS transfer"
    ; consumes =
        "reflection positivity, clustering, observable inclusion, and finite margin"
    ; produces =
        "candidate OS/Wightman reconstruction transfer"
    ; blocker =
        missingOSSchwingerFunctionTransfer
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

depthPollutionRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
depthPollutionRouteRow =
  record
    { stage =
        noDepthSpectralPollutionPreconditionStage
    ; label =
        "depth no-pollution"
    ; consumes =
        "uniform finite margins across depth d"
    ; produces =
        "no near-zero spectral pollution in depth limit"
    ; blocker =
        missingNoDepthSpectralPollution
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

continuumPollutionRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
continuumPollutionRouteRow =
  record
    { stage =
        noContinuumSpectralPollutionPreconditionStage
    ; label =
        "continuum no-pollution"
    ; consumes =
        "depth no-pollution, OS transfer, and lattice-spacing limit"
    ; produces =
        "continuum mass-gap transfer precondition"
    ; blocker =
        missingNoContinuumSpectralPollution
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

clayAuthorityRouteRow :
  YMSpectralMarginFromHolonomyRouteRow
clayAuthorityRouteRow =
  record
    { stage =
        clayYangMillsAuthorityGuardStage
    ; label =
        "Clay authority guard"
    ; consumes =
        "completed OS/Wightman construction, no-pollution proof, and external validation"
    ; produces =
        "possible authority token outside this boundary"
    ; blocker =
        missingClayYangMillsAuthority
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMSpectralMarginFromHolonomyRouteRows :
  List YMSpectralMarginFromHolonomyRouteRow
canonicalYMSpectralMarginFromHolonomyRouteRows =
  quotientCarrierRouteRow
  ∷ selfAdjointRouteRow
  ∷ holonomyFloorRouteRow
  ∷ dominationRouteRow
  ∷ errorAbsorptionRouteRow
  ∷ proxyDiagnosticRouteRow
  ∷ finiteSpectralMarginRouteRow
  ∷ reflectionRouteRow
  ∷ btWilsonRouteRow
  ∷ osTransferRouteRow
  ∷ depthPollutionRouteRow
  ∷ continuumPollutionRouteRow
  ∷ clayAuthorityRouteRow
  ∷ []

routeRowCount : Nat
routeRowCount =
  listCount canonicalYMSpectralMarginFromHolonomyRouteRows

routeRowCountIs13 : routeRowCount ≡ 13
routeRowCountIs13 =
  refl

------------------------------------------------------------------------
-- False gates observed in the imported surfaces.

holonomyDominationImportedStillOpen :
  HolDom.hamiltonianDominationProved ≡ false
holonomyDominationImportedStillOpen =
  HolDom.hamiltonianDominationProvedIsFalse

holonomySpectralMarginImportedStillOpen :
  HolDom.spectralMarginProved ≡ false
holonomySpectralMarginImportedStillOpen =
  HolDom.spectralMarginProvedIsFalse

holonomyOSTransferImportedStillOpen :
  HolDom.osTransferProved ≡ false
holonomyOSTransferImportedStillOpen =
  HolDom.osTransferProvedIsFalse

holonomyContinuumNoPollutionImportedStillOpen :
  HolDom.continuumNoSpectralPollutionProved ≡ false
holonomyContinuumNoPollutionImportedStillOpen =
  HolDom.continuumNoSpectralPollutionProvedIsFalse

spectralMarginBudgetStillOpen :
  Margin.spectralMarginTheoremProved
    Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
spectralMarginBudgetStillOpen =
  Margin.spectralMarginTheoremProvedIsFalse

spectralMarginBudgetDominationStillOpen :
  Margin.hamiltonianDominationProved
    Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
spectralMarginBudgetDominationStillOpen =
  Margin.hamiltonianDominationProvedIsFalse

spectralMarginBudgetTransferStillOpen :
  Margin.reflectionPositiveTransferProved
    Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
spectralMarginBudgetTransferStillOpen =
  Margin.reflectionPositiveTransferProvedIsFalse

spectralMarginBudgetContinuumStillOpen :
  Margin.noSpectralPollutionProved
    Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
spectralMarginBudgetContinuumStillOpen =
  Margin.noSpectralPollutionProvedIsFalse

proxyObservedOk :
  Proxy.ok_observed ≡ true
proxyObservedOk =
  Proxy.ok_observed_is_true

proxyDiagnosticOnly :
  Proxy.diagnostic_only ≡ true
proxyDiagnosticOnly =
  Proxy.diagnostic_only_is_true

proxyPromotionStillFalse :
  Proxy.promotion ≡ false
proxyPromotionStillFalse =
  Proxy.promotion_is_false

proxySpectralMarginTheoremStillFalse :
  Proxy.spectralMarginTheoremProved ≡ false
proxySpectralMarginTheoremStillFalse =
  Proxy.spectralMarginTheoremProvedIsFalse

proxyContinuumNoPollutionStillFalse :
  Proxy.continuumNoPollutionProved ≡ false
proxyContinuumNoPollutionStillFalse =
  Proxy.continuumNoPollutionProvedIsFalse

btosWilsonComparisonStillOpen :
  BTOS.bTWilsonActionComparisonProved ≡ false
btosWilsonComparisonStillOpen =
  BTOS.bTWilsonActionComparisonProvedIsFalse

btosReflectionPositiveStillOpen :
  BTOS.bTReflectionPositiveTransferMatrixProved ≡ false
btosReflectionPositiveStillOpen =
  BTOS.bTReflectionPositiveTransferMatrixProvedIsFalse

btosOSLatticeTransferStillOpen :
  BTOS.bruhatTitsToOSLatticeTransferProved ≡ false
btosOSLatticeTransferStillOpen =
  BTOS.bruhatTitsToOSLatticeTransferProvedIsFalse

btosDepthNoPollutionStillOpen :
  BTOS.noSpectralPollutionDepthLimitProved ≡ false
btosDepthNoPollutionStillOpen =
  BTOS.noSpectralPollutionDepthLimitProvedIsFalse

btosContinuumNoPollutionStillOpen :
  BTOS.noSpectralPollutionContinuumLimitProved ≡ false
btosContinuumNoPollutionStillOpen =
  BTOS.noSpectralPollutionContinuumLimitProvedIsFalse

btosClayPromotionStillFalse :
  BTOS.clayYangMillsPromoted ≡ false
btosClayPromotionStillFalse =
  BTOS.clayYangMillsPromotedIsFalse

------------------------------------------------------------------------
-- Composite governance flags.

dominationHolonomyBridgeRecorded : Bool
dominationHolonomyBridgeRecorded =
  true

finiteSpectralMarginRouteRecorded : Bool
finiteSpectralMarginRouteRecorded =
  true

proxyDiagnosticConsumed : Bool
proxyDiagnosticConsumed =
  true

osContinuumPreconditionsRecorded : Bool
osContinuumPreconditionsRecorded =
  true

finiteGaugeQuotientCarrierConstructed : Bool
finiteGaugeQuotientCarrierConstructed =
  false

selfAdjointHamiltonianOnGaugeQuotientProved : Bool
selfAdjointHamiltonianOnGaugeQuotientProved =
  false

uniformHolonomyFloorProved : Bool
uniformHolonomyFloorProved =
  false

bochnerDefectPlusHolonomyDominationProved : Bool
bochnerDefectPlusHolonomyDominationProved =
  false

finiteErrorBudgetAbsorbed : Bool
finiteErrorBudgetAbsorbed =
  false

finiteSpectralMarginProved : Bool
finiteSpectralMarginProved =
  false

reflectionPositiveTransferMatrixProved : Bool
reflectionPositiveTransferMatrixProved =
  false

bTWilsonActionComparisonProved : Bool
bTWilsonActionComparisonProved =
  false

osContinuumTransferProved : Bool
osContinuumTransferProved =
  false

depthNoSpectralPollutionProved : Bool
depthNoSpectralPollutionProved =
  false

continuumNoSpectralPollutionProved : Bool
continuumNoSpectralPollutionProved =
  false

externalAuthorityAccepted : Bool
externalAuthorityAccepted =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

dominationHolonomyBridgeRecordedIsTrue :
  dominationHolonomyBridgeRecorded ≡ true
dominationHolonomyBridgeRecordedIsTrue =
  refl

finiteSpectralMarginRouteRecordedIsTrue :
  finiteSpectralMarginRouteRecorded ≡ true
finiteSpectralMarginRouteRecordedIsTrue =
  refl

proxyDiagnosticConsumedIsTrue :
  proxyDiagnosticConsumed ≡ true
proxyDiagnosticConsumedIsTrue =
  refl

osContinuumPreconditionsRecordedIsTrue :
  osContinuumPreconditionsRecorded ≡ true
osContinuumPreconditionsRecordedIsTrue =
  refl

finiteGaugeQuotientCarrierConstructedIsFalse :
  finiteGaugeQuotientCarrierConstructed ≡ false
finiteGaugeQuotientCarrierConstructedIsFalse =
  refl

selfAdjointHamiltonianOnGaugeQuotientProvedIsFalse :
  selfAdjointHamiltonianOnGaugeQuotientProved ≡ false
selfAdjointHamiltonianOnGaugeQuotientProvedIsFalse =
  refl

uniformHolonomyFloorProvedIsFalse :
  uniformHolonomyFloorProved ≡ false
uniformHolonomyFloorProvedIsFalse =
  refl

bochnerDefectPlusHolonomyDominationProvedIsFalse :
  bochnerDefectPlusHolonomyDominationProved ≡ false
bochnerDefectPlusHolonomyDominationProvedIsFalse =
  refl

finiteErrorBudgetAbsorbedIsFalse :
  finiteErrorBudgetAbsorbed ≡ false
finiteErrorBudgetAbsorbedIsFalse =
  refl

finiteSpectralMarginProvedIsFalse :
  finiteSpectralMarginProved ≡ false
finiteSpectralMarginProvedIsFalse =
  refl

reflectionPositiveTransferMatrixProvedIsFalse :
  reflectionPositiveTransferMatrixProved ≡ false
reflectionPositiveTransferMatrixProvedIsFalse =
  refl

bTWilsonActionComparisonProvedIsFalse :
  bTWilsonActionComparisonProved ≡ false
bTWilsonActionComparisonProvedIsFalse =
  refl

osContinuumTransferProvedIsFalse :
  osContinuumTransferProved ≡ false
osContinuumTransferProvedIsFalse =
  refl

depthNoSpectralPollutionProvedIsFalse :
  depthNoSpectralPollutionProved ≡ false
depthNoSpectralPollutionProvedIsFalse =
  refl

continuumNoSpectralPollutionProvedIsFalse :
  continuumNoSpectralPollutionProved ≡ false
continuumNoSpectralPollutionProvedIsFalse =
  refl

externalAuthorityAcceptedIsFalse :
  externalAuthorityAccepted ≡ false
externalAuthorityAcceptedIsFalse =
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

SpectralMarginFromHolonomyDominationTheorem : Set
SpectralMarginFromHolonomyDominationTheorem =
  ⊥

FiniteSpectralMarginTheorem : Set
FiniteSpectralMarginTheorem =
  ⊥

OSContinuumTransferTheorem : Set
OSContinuumTransferTheorem =
  ⊥

YMClayPromotionAuthority : Set
YMClayPromotionAuthority =
  ⊥

------------------------------------------------------------------------
-- Boundary receipt.

data YMSpectralMarginFromHolonomyStatus : Set where
  spectralMarginFromHolonomyBoundaryRecordedStillOpen :
    YMSpectralMarginFromHolonomyStatus

record YMSpectralMarginFromHolonomyDominationBoundary : Setω where
  field
    status :
      YMSpectralMarginFromHolonomyStatus

    inputPack :
      YMSpectralMarginFromHolonomyInputPack

    support :
      List YMSpectralMarginFromHolonomySupport

    supportIsCanonical :
      support ≡ canonicalYMSpectralMarginFromHolonomySupport

    supportCountField :
      Nat

    supportCountFieldIs4 :
      supportCountField ≡ 4

    stages :
      List YMSpectralMarginFromHolonomyStage

    stagesAreCanonical :
      stages ≡ canonicalYMSpectralMarginFromHolonomyStages

    stageCountField :
      Nat

    stageCountFieldIs13 :
      stageCountField ≡ 13

    blockers :
      List YMSpectralMarginFromHolonomyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMSpectralMarginFromHolonomyBlockers

    blockerCountField :
      Nat

    blockerCountFieldIs14 :
      blockerCountField ≡ 14

    routeRows :
      List YMSpectralMarginFromHolonomyRouteRow

    routeRowsAreCanonical :
      routeRows ≡ canonicalYMSpectralMarginFromHolonomyRouteRows

    routeRowCountField :
      Nat

    routeRowCountFieldIs13 :
      routeRowCountField ≡ 13

    targetFiniteInequalityText :
      String

    targetFiniteInequalityTextIsCanonical :
      targetFiniteInequalityText
      ≡
      "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"

    targetSpectralMarginText :
      String

    targetSpectralMarginTextIsCanonical :
      targetSpectralMarginText
      ≡
      "lambda1(H_d | Omega^perp) >= m_d > 0 uniformly after E_d absorption"

    targetTransferText :
      String

    targetTransferTextIsCanonical :
      targetTransferText
      ≡
      "finite margin + reflection positivity + no spectral pollution -> OS/continuum preconditions"

    importedHolonomyDominationStillFalse :
      HolDom.hamiltonianDominationProved ≡ false

    importedHolonomySpectralMarginStillFalse :
      HolDom.spectralMarginProved ≡ false

    importedHolonomyOSTransferStillFalse :
      HolDom.osTransferProved ≡ false

    importedSpectralBudgetStillFalse :
      Margin.spectralMarginTheoremProved
        Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
      ≡
      false

    importedSpectralBudgetTransferStillFalse :
      Margin.reflectionPositiveTransferProved
        Margin.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
      ≡
      false

    importedProxyObservedOk :
      Proxy.ok_observed ≡ true

    importedProxyDiagnosticOnly :
      Proxy.diagnostic_only ≡ true

    importedProxyPromotionStillFalse :
      Proxy.promotion ≡ false

    importedProxySpectralMarginStillFalse :
      Proxy.spectralMarginTheoremProved ≡ false

    importedBTOSWilsonComparisonStillFalse :
      BTOS.bTWilsonActionComparisonProved ≡ false

    importedBTOSReflectionStillFalse :
      BTOS.bTReflectionPositiveTransferMatrixProved ≡ false

    importedBTOSDepthNoPollutionStillFalse :
      BTOS.noSpectralPollutionDepthLimitProved ≡ false

    importedBTOSContinuumNoPollutionStillFalse :
      BTOS.noSpectralPollutionContinuumLimitProved ≡ false

    importedBTOSClayStillFalse :
      BTOS.clayYangMillsPromoted ≡ false

    finiteGaugeQuotientCarrierConstructedField :
      Bool

    finiteGaugeQuotientCarrierConstructedFieldIsFalse :
      finiteGaugeQuotientCarrierConstructedField ≡ false

    selfAdjointHamiltonianOnGaugeQuotientProvedField :
      Bool

    selfAdjointHamiltonianOnGaugeQuotientProvedFieldIsFalse :
      selfAdjointHamiltonianOnGaugeQuotientProvedField ≡ false

    uniformHolonomyFloorProvedField :
      Bool

    uniformHolonomyFloorProvedFieldIsFalse :
      uniformHolonomyFloorProvedField ≡ false

    bochnerDefectPlusHolonomyDominationProvedField :
      Bool

    bochnerDefectPlusHolonomyDominationProvedFieldIsFalse :
      bochnerDefectPlusHolonomyDominationProvedField ≡ false

    finiteErrorBudgetAbsorbedField :
      Bool

    finiteErrorBudgetAbsorbedFieldIsFalse :
      finiteErrorBudgetAbsorbedField ≡ false

    finiteSpectralMarginProvedField :
      Bool

    finiteSpectralMarginProvedFieldIsFalse :
      finiteSpectralMarginProvedField ≡ false

    reflectionPositiveTransferMatrixProvedField :
      Bool

    reflectionPositiveTransferMatrixProvedFieldIsFalse :
      reflectionPositiveTransferMatrixProvedField ≡ false

    bTWilsonActionComparisonProvedField :
      Bool

    bTWilsonActionComparisonProvedFieldIsFalse :
      bTWilsonActionComparisonProvedField ≡ false

    osContinuumTransferProvedField :
      Bool

    osContinuumTransferProvedFieldIsFalse :
      osContinuumTransferProvedField ≡ false

    depthNoSpectralPollutionProvedField :
      Bool

    depthNoSpectralPollutionProvedFieldIsFalse :
      depthNoSpectralPollutionProvedField ≡ false

    continuumNoSpectralPollutionProvedField :
      Bool

    continuumNoSpectralPollutionProvedFieldIsFalse :
      continuumNoSpectralPollutionProvedField ≡ false

    externalAuthorityAcceptedField :
      Bool

    externalAuthorityAcceptedFieldIsFalse :
      externalAuthorityAcceptedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    noSpectralMarginPromotion :
      SpectralMarginFromHolonomyDominationTheorem → ⊥

    noFiniteMarginPromotion :
      FiniteSpectralMarginTheorem → ⊥

    noOSTransferPromotion :
      OSContinuumTransferTheorem → ⊥

    noClayPromotion :
      YMClayPromotionAuthority → ⊥

open YMSpectralMarginFromHolonomyDominationBoundary public

canonicalYMSpectralMarginFromHolonomyDominationBoundary :
  YMSpectralMarginFromHolonomyDominationBoundary
canonicalYMSpectralMarginFromHolonomyDominationBoundary =
  record
    { status =
        spectralMarginFromHolonomyBoundaryRecordedStillOpen
    ; inputPack =
        canonicalYMSpectralMarginFromHolonomyInputPack
    ; support =
        canonicalYMSpectralMarginFromHolonomySupport
    ; supportIsCanonical =
        refl
    ; supportCountField =
        supportCount
    ; supportCountFieldIs4 =
        supportCountIs4
    ; stages =
        canonicalYMSpectralMarginFromHolonomyStages
    ; stagesAreCanonical =
        refl
    ; stageCountField =
        stageCount
    ; stageCountFieldIs13 =
        stageCountIs13
    ; blockers =
        canonicalYMSpectralMarginFromHolonomyBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountField =
        blockerCount
    ; blockerCountFieldIs14 =
        blockerCountIs14
    ; routeRows =
        canonicalYMSpectralMarginFromHolonomyRouteRows
    ; routeRowsAreCanonical =
        refl
    ; routeRowCountField =
        routeRowCount
    ; routeRowCountFieldIs13 =
        routeRowCountIs13
    ; targetFiniteInequalityText =
        "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"
    ; targetFiniteInequalityTextIsCanonical =
        refl
    ; targetSpectralMarginText =
        "lambda1(H_d | Omega^perp) >= m_d > 0 uniformly after E_d absorption"
    ; targetSpectralMarginTextIsCanonical =
        refl
    ; targetTransferText =
        "finite margin + reflection positivity + no spectral pollution -> OS/continuum preconditions"
    ; targetTransferTextIsCanonical =
        refl
    ; importedHolonomyDominationStillFalse =
        holonomyDominationImportedStillOpen
    ; importedHolonomySpectralMarginStillFalse =
        holonomySpectralMarginImportedStillOpen
    ; importedHolonomyOSTransferStillFalse =
        holonomyOSTransferImportedStillOpen
    ; importedSpectralBudgetStillFalse =
        spectralMarginBudgetStillOpen
    ; importedSpectralBudgetTransferStillFalse =
        spectralMarginBudgetTransferStillOpen
    ; importedProxyObservedOk =
        proxyObservedOk
    ; importedProxyDiagnosticOnly =
        proxyDiagnosticOnly
    ; importedProxyPromotionStillFalse =
        proxyPromotionStillFalse
    ; importedProxySpectralMarginStillFalse =
        proxySpectralMarginTheoremStillFalse
    ; importedBTOSWilsonComparisonStillFalse =
        btosWilsonComparisonStillOpen
    ; importedBTOSReflectionStillFalse =
        btosReflectionPositiveStillOpen
    ; importedBTOSDepthNoPollutionStillFalse =
        btosDepthNoPollutionStillOpen
    ; importedBTOSContinuumNoPollutionStillFalse =
        btosContinuumNoPollutionStillOpen
    ; importedBTOSClayStillFalse =
        btosClayPromotionStillFalse
    ; finiteGaugeQuotientCarrierConstructedField =
        false
    ; finiteGaugeQuotientCarrierConstructedFieldIsFalse =
        refl
    ; selfAdjointHamiltonianOnGaugeQuotientProvedField =
        false
    ; selfAdjointHamiltonianOnGaugeQuotientProvedFieldIsFalse =
        refl
    ; uniformHolonomyFloorProvedField =
        false
    ; uniformHolonomyFloorProvedFieldIsFalse =
        refl
    ; bochnerDefectPlusHolonomyDominationProvedField =
        false
    ; bochnerDefectPlusHolonomyDominationProvedFieldIsFalse =
        refl
    ; finiteErrorBudgetAbsorbedField =
        false
    ; finiteErrorBudgetAbsorbedFieldIsFalse =
        refl
    ; finiteSpectralMarginProvedField =
        false
    ; finiteSpectralMarginProvedFieldIsFalse =
        refl
    ; reflectionPositiveTransferMatrixProvedField =
        false
    ; reflectionPositiveTransferMatrixProvedFieldIsFalse =
        refl
    ; bTWilsonActionComparisonProvedField =
        false
    ; bTWilsonActionComparisonProvedFieldIsFalse =
        refl
    ; osContinuumTransferProvedField =
        false
    ; osContinuumTransferProvedFieldIsFalse =
        refl
    ; depthNoSpectralPollutionProvedField =
        false
    ; depthNoSpectralPollutionProvedFieldIsFalse =
        refl
    ; continuumNoSpectralPollutionProvedField =
        false
    ; continuumNoSpectralPollutionProvedFieldIsFalse =
        refl
    ; externalAuthorityAcceptedField =
        false
    ; externalAuthorityAcceptedFieldIsFalse =
        refl
    ; ymClayPromotedField =
        false
    ; ymClayPromotedFieldIsFalse =
        refl
    ; terminalPromotionField =
        false
    ; terminalPromotionFieldIsFalse =
        refl
    ; noSpectralMarginPromotion =
        λ ()
    ; noFiniteMarginPromotion =
        λ ()
    ; noOSTransferPromotion =
        λ ()
    ; noClayPromotion =
        λ ()
    }

canonicalFiniteSpectralMarginFalse :
  finiteSpectralMarginProvedField
    canonicalYMSpectralMarginFromHolonomyDominationBoundary
  ≡
  false
canonicalFiniteSpectralMarginFalse =
  refl

canonicalOSTransferFalse :
  osContinuumTransferProvedField
    canonicalYMSpectralMarginFromHolonomyDominationBoundary
  ≡
  false
canonicalOSTransferFalse =
  refl

canonicalYMClayPromotionFalse :
  ymClayPromotedField
    canonicalYMSpectralMarginFromHolonomyDominationBoundary
  ≡
  false
canonicalYMClayPromotionFalse =
  refl

canonicalTerminalPromotionFalse :
  terminalPromotionField
    canonicalYMSpectralMarginFromHolonomyDominationBoundary
  ≡
  false
canonicalTerminalPromotionFalse =
  refl
