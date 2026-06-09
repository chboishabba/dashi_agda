module DASHI.Physics.Closure.NSHarmonicPressureTailAbsorptionEstimateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary
  as ErrorBudget
import DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary
  as Localization
import DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary
  as Commutator
import DASHI.Physics.Closure.NSPressureTailAbsorptionProxyHarnessResult
  as TailHarness

------------------------------------------------------------------------
-- Fail-closed theorem-contract boundary.
--
-- This module records the remaining analytic contract for harmonic
-- pressure tail absorption under A6 localization.  It is intentionally a
-- theorem boundary, not a theorem proof: it records the target surfaces,
-- imported anchors, budget routing, no-sign governance, counts, and
-- false promotion flags required before any Clay-facing promotion can be
-- considered.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported support anchors.

pressureCommutatorEstimateContractBoundaryReference : String
pressureCommutatorEstimateContractBoundaryReference =
  "DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary"

pressureTailAbsorptionProxyHarnessResultReference : String
pressureTailAbsorptionProxyHarnessResultReference =
  "DASHI.Physics.Closure.NSPressureTailAbsorptionProxyHarnessResult"

localizationPressureCommutatorBoundaryReference : String
localizationPressureCommutatorBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary"

nsa6ErrorBudgetCompositeBoundaryReference : String
nsa6ErrorBudgetCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary"

pressureCommutatorEstimateContractBoundaryImported : Bool
pressureCommutatorEstimateContractBoundaryImported =
  true

pressureTailAbsorptionProxyHarnessResultImported : Bool
pressureTailAbsorptionProxyHarnessResultImported =
  true

localizationPressureCommutatorBoundaryImported : Bool
localizationPressureCommutatorBoundaryImported =
  true

nsa6ErrorBudgetCompositeBoundaryImported : Bool
nsa6ErrorBudgetCompositeBoundaryImported =
  true

record ImportedNSHarmonicPressureTailSupport : Set where
  field
    pressureCommutatorContract :
      Commutator.NSPressureCommutatorEstimateContractBoundary
    pressureCommutatorContractIsCanonical :
      pressureCommutatorContract
        ≡ Commutator.canonicalNSPressureCommutatorEstimateContractBoundary
    pressureTailHarness :
      TailHarness.NSPressureTailAbsorptionProxyHarnessResult
    pressureTailHarnessIsCanonical :
      pressureTailHarness
        ≡ TailHarness.canonicalNSPressureTailAbsorptionProxyHarnessResult
    localizationBoundary :
      Localization.NSLocalizationPressureCommutatorBoundary
    localizationBoundaryIsCanonical :
      localizationBoundary
        ≡ Localization.canonicalNSLocalizationPressureCommutatorBoundary
    errorBudgetComposite :
      ErrorBudget.NSA6ErrorBudgetCompositeBoundary
    errorBudgetCompositeIsCanonical :
      errorBudgetComposite
        ≡ ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    pressureCommutatorEstimateContractBoundaryImportedIsTrue :
      pressureCommutatorEstimateContractBoundaryImported ≡ true
    pressureTailAbsorptionProxyHarnessResultImportedIsTrue :
      pressureTailAbsorptionProxyHarnessResultImported ≡ true
    localizationPressureCommutatorBoundaryImportedIsTrue :
      localizationPressureCommutatorBoundaryImported ≡ true
    nsa6ErrorBudgetCompositeBoundaryImportedIsTrue :
      nsa6ErrorBudgetCompositeBoundaryImported ≡ true

canonicalImportedNSHarmonicPressureTailSupport :
  ImportedNSHarmonicPressureTailSupport
canonicalImportedNSHarmonicPressureTailSupport =
  record
    { pressureCommutatorContract =
        Commutator.canonicalNSPressureCommutatorEstimateContractBoundary
    ; pressureCommutatorContractIsCanonical =
        refl
    ; pressureTailHarness =
        TailHarness.canonicalNSPressureTailAbsorptionProxyHarnessResult
    ; pressureTailHarnessIsCanonical =
        refl
    ; localizationBoundary =
        Localization.canonicalNSLocalizationPressureCommutatorBoundary
    ; localizationBoundaryIsCanonical =
        refl
    ; errorBudgetComposite =
        ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    ; errorBudgetCompositeIsCanonical =
        refl
    ; pressureCommutatorEstimateContractBoundaryImportedIsTrue =
        refl
    ; pressureTailAbsorptionProxyHarnessResultImportedIsTrue =
        refl
    ; localizationPressureCommutatorBoundaryImportedIsTrue =
        refl
    ; nsa6ErrorBudgetCompositeBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Harmonic pressure-tail theorem targets.

data HarmonicPressureTailTheoremTarget : Set where
  harmonicPressureDecomposition :
    HarmonicPressureTailTheoremTarget
  exteriorAnnulusKernelDecay :
    HarmonicPressureTailTheoremTarget
  meanSubtractionOnQr :
    HarmonicPressureTailTheoremTarget
  scaleSeparatedTailAbsorption :
    HarmonicPressureTailTheoremTarget
  epsilonGradientSplit :
    HarmonicPressureTailTheoremTarget
  lowerOrderPressureTailBudgetRouting :
    HarmonicPressureTailTheoremTarget
  noSignClaim :
    HarmonicPressureTailTheoremTarget

canonicalHarmonicPressureTailTheoremTargets :
  List HarmonicPressureTailTheoremTarget
canonicalHarmonicPressureTailTheoremTargets =
  harmonicPressureDecomposition
  ∷ exteriorAnnulusKernelDecay
  ∷ meanSubtractionOnQr
  ∷ scaleSeparatedTailAbsorption
  ∷ epsilonGradientSplit
  ∷ lowerOrderPressureTailBudgetRouting
  ∷ noSignClaim
  ∷ []

harmonicPressureTailTheoremTargetCount : Nat
harmonicPressureTailTheoremTargetCount =
  listLength canonicalHarmonicPressureTailTheoremTargets

harmonicPressureTailTheoremTargetCountIs7 :
  harmonicPressureTailTheoremTargetCount ≡ 7
harmonicPressureTailTheoremTargetCountIs7 =
  refl

targetStatement :
  HarmonicPressureTailTheoremTarget →
  String
targetStatement harmonicPressureDecomposition =
  "Target: decompose localized pressure into Q_r local Calderon-Zygmund core plus harmonic exterior tail induced by outside-annulus data."
targetStatement exteriorAnnulusKernelDecay =
  "Target: prove exterior annulus kernel decay with scale-separated distance from Q_r to dyadic annuli and no hidden supercritical loss."
targetStatement meanSubtractionOnQr =
  "Target: subtract the Q_r mean of harmonic pressure before pairing with localized velocity gradients or shell energies."
targetStatement scaleSeparatedTailAbsorption =
  "Target: absorb scale-separated harmonic pressure tails into epsilon dissipation plus controlled lower-order pressure-tail budgets."
targetStatement epsilonGradientSplit =
  "Target: split each pressure-tail pairing into epsilon times localized gradient dissipation and C_epsilon times lower-order tail load."
targetStatement lowerOrderPressureTailBudgetRouting =
  "Target: route every residual tail term to ErrorBudget.pressureTailBudgetRow while preserving localizationCutoffBudget and pressureCommutatorBudget ownership."
targetStatement noSignClaim =
  "Target: make no pointwise positivity, negativity, monotonicity, or favorable-sign claim about pressure or harmonic pressure."

record HarmonicPressureTailTargetRow : Set where
  field
    target :
      HarmonicPressureTailTheoremTarget
    statement :
      String
    statementIsCanonical :
      statement ≡ targetStatement target

harmonicPressureDecompositionRow :
  HarmonicPressureTailTargetRow
harmonicPressureDecompositionRow =
  record
    { target =
        harmonicPressureDecomposition
    ; statement =
        targetStatement harmonicPressureDecomposition
    ; statementIsCanonical =
        refl
    }

exteriorAnnulusKernelDecayRow :
  HarmonicPressureTailTargetRow
exteriorAnnulusKernelDecayRow =
  record
    { target =
        exteriorAnnulusKernelDecay
    ; statement =
        targetStatement exteriorAnnulusKernelDecay
    ; statementIsCanonical =
        refl
    }

meanSubtractionOnQrRow :
  HarmonicPressureTailTargetRow
meanSubtractionOnQrRow =
  record
    { target =
        meanSubtractionOnQr
    ; statement =
        targetStatement meanSubtractionOnQr
    ; statementIsCanonical =
        refl
    }

scaleSeparatedTailAbsorptionRow :
  HarmonicPressureTailTargetRow
scaleSeparatedTailAbsorptionRow =
  record
    { target =
        scaleSeparatedTailAbsorption
    ; statement =
        targetStatement scaleSeparatedTailAbsorption
    ; statementIsCanonical =
        refl
    }

epsilonGradientSplitRow :
  HarmonicPressureTailTargetRow
epsilonGradientSplitRow =
  record
    { target =
        epsilonGradientSplit
    ; statement =
        targetStatement epsilonGradientSplit
    ; statementIsCanonical =
        refl
    }

lowerOrderPressureTailBudgetRoutingRow :
  HarmonicPressureTailTargetRow
lowerOrderPressureTailBudgetRoutingRow =
  record
    { target =
        lowerOrderPressureTailBudgetRouting
    ; statement =
        targetStatement lowerOrderPressureTailBudgetRouting
    ; statementIsCanonical =
        refl
    }

noSignClaimRow :
  HarmonicPressureTailTargetRow
noSignClaimRow =
  record
    { target =
        noSignClaim
    ; statement =
        targetStatement noSignClaim
    ; statementIsCanonical =
        refl
    }

canonicalHarmonicPressureTailTargetRows :
  List HarmonicPressureTailTargetRow
canonicalHarmonicPressureTailTargetRows =
  harmonicPressureDecompositionRow
  ∷ exteriorAnnulusKernelDecayRow
  ∷ meanSubtractionOnQrRow
  ∷ scaleSeparatedTailAbsorptionRow
  ∷ epsilonGradientSplitRow
  ∷ lowerOrderPressureTailBudgetRoutingRow
  ∷ noSignClaimRow
  ∷ []

harmonicPressureTailTargetRowCount : Nat
harmonicPressureTailTargetRowCount =
  listLength canonicalHarmonicPressureTailTargetRows

harmonicPressureTailTargetRowCountIs7 :
  harmonicPressureTailTargetRowCount ≡ 7
harmonicPressureTailTargetRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Budget routing and fail-closed controls.

data HarmonicPressureTailBudgetRoute : Set where
  routeLocalCZCoreToPressureCommutatorBudget :
    HarmonicPressureTailBudgetRoute
  routeCutoffDerivativeLeakageToLocalizationCutoffBudget :
    HarmonicPressureTailBudgetRoute
  routeHarmonicExteriorTailToPressureTailBudget :
    HarmonicPressureTailBudgetRoute
  routeAnnularMeanSubtractionResidualToPressureTailBudget :
    HarmonicPressureTailBudgetRoute
  routeEpsilonGradientPieceToOffDiagonalAbsorptionBudget :
    HarmonicPressureTailBudgetRoute
  routeLowerOrderPieceToCompositePressureTailBudget :
    HarmonicPressureTailBudgetRoute

canonicalHarmonicPressureTailBudgetRoutes :
  List HarmonicPressureTailBudgetRoute
canonicalHarmonicPressureTailBudgetRoutes =
  routeLocalCZCoreToPressureCommutatorBudget
  ∷ routeCutoffDerivativeLeakageToLocalizationCutoffBudget
  ∷ routeHarmonicExteriorTailToPressureTailBudget
  ∷ routeAnnularMeanSubtractionResidualToPressureTailBudget
  ∷ routeEpsilonGradientPieceToOffDiagonalAbsorptionBudget
  ∷ routeLowerOrderPieceToCompositePressureTailBudget
  ∷ []

harmonicPressureTailBudgetRouteCount : Nat
harmonicPressureTailBudgetRouteCount =
  listLength canonicalHarmonicPressureTailBudgetRoutes

harmonicPressureTailBudgetRouteCountIs6 :
  harmonicPressureTailBudgetRouteCount ≡ 6
harmonicPressureTailBudgetRouteCountIs6 =
  refl

routeStatement :
  HarmonicPressureTailBudgetRoute →
  String
routeStatement routeLocalCZCoreToPressureCommutatorBudget =
  "Route: local Calderon-Zygmund pressure core and Riesz commutator defects feed pressureCommutatorBudget."
routeStatement routeCutoffDerivativeLeakageToLocalizationCutoffBudget =
  "Route: cutoff-gradient and cutoff-Laplacian leakage feed localizationCutoffBudget."
routeStatement routeHarmonicExteriorTailToPressureTailBudget =
  "Route: exterior harmonic pressure tail feeds pressureTailBudget only after annular kernel decay is proved."
routeStatement routeAnnularMeanSubtractionResidualToPressureTailBudget =
  "Route: Q_r mean-subtraction residual and annular recentering defects remain pressure-tail lower-order costs."
routeStatement routeEpsilonGradientPieceToOffDiagonalAbsorptionBudget =
  "Route: epsilon-gradient split is charged to available absorption margin, not to a sign property of pressure."
routeStatement routeLowerOrderPieceToCompositePressureTailBudget =
  "Route: C_epsilon lower-order remainder is forwarded to NSA6ErrorBudgetCompositeBoundary pressureTailBudgetRow."

record HarmonicPressureTailBudgetRouteRow : Set where
  field
    route :
      HarmonicPressureTailBudgetRoute
    routeText :
      String
    routeTextIsCanonical :
      routeText ≡ routeStatement route

routeLocalCZCoreToPressureCommutatorBudgetRow :
  HarmonicPressureTailBudgetRouteRow
routeLocalCZCoreToPressureCommutatorBudgetRow =
  record
    { route =
        routeLocalCZCoreToPressureCommutatorBudget
    ; routeText =
        routeStatement routeLocalCZCoreToPressureCommutatorBudget
    ; routeTextIsCanonical =
        refl
    }

routeCutoffDerivativeLeakageToLocalizationCutoffBudgetRow :
  HarmonicPressureTailBudgetRouteRow
routeCutoffDerivativeLeakageToLocalizationCutoffBudgetRow =
  record
    { route =
        routeCutoffDerivativeLeakageToLocalizationCutoffBudget
    ; routeText =
        routeStatement routeCutoffDerivativeLeakageToLocalizationCutoffBudget
    ; routeTextIsCanonical =
        refl
    }

routeHarmonicExteriorTailToPressureTailBudgetRow :
  HarmonicPressureTailBudgetRouteRow
routeHarmonicExteriorTailToPressureTailBudgetRow =
  record
    { route =
        routeHarmonicExteriorTailToPressureTailBudget
    ; routeText =
        routeStatement routeHarmonicExteriorTailToPressureTailBudget
    ; routeTextIsCanonical =
        refl
    }

routeAnnularMeanSubtractionResidualToPressureTailBudgetRow :
  HarmonicPressureTailBudgetRouteRow
routeAnnularMeanSubtractionResidualToPressureTailBudgetRow =
  record
    { route =
        routeAnnularMeanSubtractionResidualToPressureTailBudget
    ; routeText =
        routeStatement routeAnnularMeanSubtractionResidualToPressureTailBudget
    ; routeTextIsCanonical =
        refl
    }

routeEpsilonGradientPieceToOffDiagonalAbsorptionBudgetRow :
  HarmonicPressureTailBudgetRouteRow
routeEpsilonGradientPieceToOffDiagonalAbsorptionBudgetRow =
  record
    { route =
        routeEpsilonGradientPieceToOffDiagonalAbsorptionBudget
    ; routeText =
        routeStatement routeEpsilonGradientPieceToOffDiagonalAbsorptionBudget
    ; routeTextIsCanonical =
        refl
    }

routeLowerOrderPieceToCompositePressureTailBudgetRow :
  HarmonicPressureTailBudgetRouteRow
routeLowerOrderPieceToCompositePressureTailBudgetRow =
  record
    { route =
        routeLowerOrderPieceToCompositePressureTailBudget
    ; routeText =
        routeStatement routeLowerOrderPieceToCompositePressureTailBudget
    ; routeTextIsCanonical =
        refl
    }

canonicalHarmonicPressureTailBudgetRouteRows :
  List HarmonicPressureTailBudgetRouteRow
canonicalHarmonicPressureTailBudgetRouteRows =
  routeLocalCZCoreToPressureCommutatorBudgetRow
  ∷ routeCutoffDerivativeLeakageToLocalizationCutoffBudgetRow
  ∷ routeHarmonicExteriorTailToPressureTailBudgetRow
  ∷ routeAnnularMeanSubtractionResidualToPressureTailBudgetRow
  ∷ routeEpsilonGradientPieceToOffDiagonalAbsorptionBudgetRow
  ∷ routeLowerOrderPieceToCompositePressureTailBudgetRow
  ∷ []

harmonicPressureTailBudgetRouteRowCount : Nat
harmonicPressureTailBudgetRouteRowCount =
  listLength canonicalHarmonicPressureTailBudgetRouteRows

harmonicPressureTailBudgetRouteRowCountIs6 :
  harmonicPressureTailBudgetRouteRowCount ≡ 6
harmonicPressureTailBudgetRouteRowCountIs6 =
  refl

data HarmonicPressureTailFailClosedControl : Set where
  noPressureSignGovernance :
    HarmonicPressureTailFailClosedControl
  diagnosticHarnessIsProxyOnly :
    HarmonicPressureTailFailClosedControl
  commutatorBoundaryStillFalse :
    HarmonicPressureTailFailClosedControl
  localizationBoundaryStillFalse :
    HarmonicPressureTailFailClosedControl
  compositeBudgetStillFalse :
    HarmonicPressureTailFailClosedControl
  clayAndTerminalPromotionForbidden :
    HarmonicPressureTailFailClosedControl

canonicalHarmonicPressureTailFailClosedControls :
  List HarmonicPressureTailFailClosedControl
canonicalHarmonicPressureTailFailClosedControls =
  noPressureSignGovernance
  ∷ diagnosticHarnessIsProxyOnly
  ∷ commutatorBoundaryStillFalse
  ∷ localizationBoundaryStillFalse
  ∷ compositeBudgetStillFalse
  ∷ clayAndTerminalPromotionForbidden
  ∷ []

harmonicPressureTailFailClosedControlCount : Nat
harmonicPressureTailFailClosedControlCount =
  listLength canonicalHarmonicPressureTailFailClosedControls

harmonicPressureTailFailClosedControlCountIs6 :
  harmonicPressureTailFailClosedControlCount ≡ 6
harmonicPressureTailFailClosedControlCountIs6 =
  refl

------------------------------------------------------------------------
-- Required false flags.

harmonicPressureTailAbsorbed : Bool
harmonicPressureTailAbsorbed =
  false

pressureTailBudgetClosed : Bool
pressureTailBudgetClosed =
  false

localizationTheoremProved : Bool
localizationTheoremProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

noPressureSignClaimMade : Bool
noPressureSignClaimMade =
  true

harmonicPressureTailAbsorbedIsFalse :
  harmonicPressureTailAbsorbed ≡ false
harmonicPressureTailAbsorbedIsFalse =
  refl

pressureTailBudgetClosedIsFalse :
  pressureTailBudgetClosed ≡ false
pressureTailBudgetClosedIsFalse =
  refl

localizationTheoremProvedIsFalse :
  localizationTheoremProved ≡ false
localizationTheoremProvedIsFalse =
  refl

triadicCompensatedLeakageIdentityProvedIsFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
triadicCompensatedLeakageIdentityProvedIsFalse =
  refl

nsClayPromotedIsFalse :
  nsClayPromoted ≡ false
nsClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

noPressureSignClaimMadeIsTrue :
  noPressureSignClaimMade ≡ true
noPressureSignClaimMadeIsTrue =
  refl

importedCommutatorPressureTailStillFalse :
  Commutator.pressureTailAbsorbed ≡ false
importedCommutatorPressureTailStillFalse =
  refl

importedCommutatorLocalizationStillFalse :
  Commutator.localizationTheoremProved ≡ false
importedCommutatorLocalizationStillFalse =
  refl

importedTailHarnessAbsorptionTheoremStillFalse :
  TailHarness.pressureTailAbsorptionTheoremProved ≡ false
importedTailHarnessAbsorptionTheoremStillFalse =
  refl

importedTailHarnessTerminalStillFalse :
  TailHarness.terminalPromotion ≡ false
importedTailHarnessTerminalStillFalse =
  refl

importedLocalizationTriadicStillFalse :
  Localization.triadicCompensatedLeakageIdentityProved ≡ false
importedLocalizationTriadicStillFalse =
  refl

importedErrorBudgetPressureTailAvailableButUnclosed :
  ErrorBudget.aggregateErrorBudgetProved ≡ false
importedErrorBudgetPressureTailAvailableButUnclosed =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F summary.

controlO : String
controlO =
  "O: Lane 3 Curie boundary for harmonic pressure-tail absorption under NS A6 localization."

controlR : String
controlR =
  "R: Record theorem targets for harmonic pressure decomposition, exterior annulus kernel decay, Q_r mean subtraction, scale-separated tail absorption, epsilon-gradient split, lower-order pressure-tail budget routing, and no sign claim."

controlC : String
controlC =
  "C: Imports NSPressureCommutatorEstimateContractBoundary, NSPressureTailAbsorptionProxyHarnessResult, NSLocalizationPressureCommutatorBoundary, and NSA6ErrorBudgetCompositeBoundary; exports counts, rows, strings, canonical record, and false flags."

controlS : String
controlS =
  "S: harmonicPressureTailAbsorbed=false, pressureTailBudgetClosed=false, localizationTheoremProved=false, triadicCompensatedLeakageIdentityProved=false, nsClayPromoted=false, terminalPromotion=false."

controlL : String
controlL =
  "L: local CZ core and commutators route to pressureCommutatorBudget; cutoff leakage routes to localizationCutoffBudget; harmonic exterior tails and mean-subtraction residuals route to pressureTailBudget; epsilon-gradient split routes to absorption margin."

controlP : String
controlP =
  "P: Prove the analytic harmonic pressure decomposition and annular decay estimates before closing any pressure-tail budget."

controlG : String
controlG =
  "G: No sign claim is made for pressure or harmonic pressure; diagnostic harness evidence remains proxy-only and non-promotional."

controlF : String
controlF =
  "F: Missing PDE proof of harmonic pressure tail absorption, closed composite pressure-tail budget, localization theorem, A6 triadic compensated leakage identity, NS Clay proof, and terminal promotion."

canonicalORCSLPGFSummary : List String
canonicalORCSLPGFSummary =
  controlO
  ∷ controlR
  ∷ controlC
  ∷ controlS
  ∷ controlL
  ∷ controlP
  ∷ controlG
  ∷ controlF
  ∷ []

orcsLpgfSummaryCount : Nat
orcsLpgfSummaryCount =
  listLength canonicalORCSLPGFSummary

orcsLpgfSummaryCountIs8 :
  orcsLpgfSummaryCount ≡ 8
orcsLpgfSummaryCountIs8 =
  refl

------------------------------------------------------------------------
-- Canonical boundary record.

record NSHarmonicPressureTailAbsorptionEstimateBoundary : Set where
  field
    importedSupport :
      ImportedNSHarmonicPressureTailSupport
    theoremTargets :
      List HarmonicPressureTailTheoremTarget
    theoremTargetCountProof :
      harmonicPressureTailTheoremTargetCount ≡ 7
    theoremTargetRows :
      List HarmonicPressureTailTargetRow
    theoremTargetRowCountProof :
      harmonicPressureTailTargetRowCount ≡ 7
    budgetRoutes :
      List HarmonicPressureTailBudgetRoute
    budgetRouteCountProof :
      harmonicPressureTailBudgetRouteCount ≡ 6
    budgetRouteRows :
      List HarmonicPressureTailBudgetRouteRow
    budgetRouteRowCountProof :
      harmonicPressureTailBudgetRouteRowCount ≡ 6
    failClosedControls :
      List HarmonicPressureTailFailClosedControl
    failClosedControlCountProof :
      harmonicPressureTailFailClosedControlCount ≡ 6
    pressureTailBudgetRouteRow :
      ErrorBudget.NSA6ErrorBudgetTaxonomyRow
    pressureTailBudgetRouteRowIsCanonical :
      pressureTailBudgetRouteRow ≡ ErrorBudget.pressureTailBudgetRow
    noSignTarget :
      HarmonicPressureTailTheoremTarget
    noSignTargetIsCanonical :
      noSignTarget ≡ noSignClaim
    noPressureSignClaimMadeTrue :
      noPressureSignClaimMade ≡ true
    harmonicPressureTailAbsorbedFalse :
      harmonicPressureTailAbsorbed ≡ false
    pressureTailBudgetClosedFalse :
      pressureTailBudgetClosed ≡ false
    localizationTheoremProvedFalse :
      localizationTheoremProved ≡ false
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    nsClayPromotedFalse :
      nsClayPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    importedCommutatorPressureTailStillFalseProof :
      Commutator.pressureTailAbsorbed ≡ false
    importedTailHarnessAbsorptionTheoremStillFalseProof :
      TailHarness.pressureTailAbsorptionTheoremProved ≡ false
    importedLocalizationTriadicStillFalseProof :
      Localization.triadicCompensatedLeakageIdentityProved ≡ false
    importedErrorBudgetAggregateStillFalseProof :
      ErrorBudget.aggregateErrorBudgetProved ≡ false
    O :
      String
    R :
      String
    C :
      String
    S :
      String
    L :
      String
    P :
      String
    G :
      String
    F :
      String
    orcslpgf :
      List String
    orcslpgfCountProof :
      orcsLpgfSummaryCount ≡ 8

open NSHarmonicPressureTailAbsorptionEstimateBoundary public

canonicalNSHarmonicPressureTailAbsorptionEstimateBoundary :
  NSHarmonicPressureTailAbsorptionEstimateBoundary
canonicalNSHarmonicPressureTailAbsorptionEstimateBoundary =
  record
    { importedSupport =
        canonicalImportedNSHarmonicPressureTailSupport
    ; theoremTargets =
        canonicalHarmonicPressureTailTheoremTargets
    ; theoremTargetCountProof =
        refl
    ; theoremTargetRows =
        canonicalHarmonicPressureTailTargetRows
    ; theoremTargetRowCountProof =
        refl
    ; budgetRoutes =
        canonicalHarmonicPressureTailBudgetRoutes
    ; budgetRouteCountProof =
        refl
    ; budgetRouteRows =
        canonicalHarmonicPressureTailBudgetRouteRows
    ; budgetRouteRowCountProof =
        refl
    ; failClosedControls =
        canonicalHarmonicPressureTailFailClosedControls
    ; failClosedControlCountProof =
        refl
    ; pressureTailBudgetRouteRow =
        ErrorBudget.pressureTailBudgetRow
    ; pressureTailBudgetRouteRowIsCanonical =
        refl
    ; noSignTarget =
        noSignClaim
    ; noSignTargetIsCanonical =
        refl
    ; noPressureSignClaimMadeTrue =
        refl
    ; harmonicPressureTailAbsorbedFalse =
        refl
    ; pressureTailBudgetClosedFalse =
        refl
    ; localizationTheoremProvedFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedFalse =
        refl
    ; nsClayPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; importedCommutatorPressureTailStillFalseProof =
        refl
    ; importedTailHarnessAbsorptionTheoremStillFalseProof =
        refl
    ; importedLocalizationTriadicStillFalseProof =
        refl
    ; importedErrorBudgetAggregateStillFalseProof =
        refl
    ; O =
        controlO
    ; R =
        controlR
    ; C =
        controlC
    ; S =
        controlS
    ; L =
        controlL
    ; P =
        controlP
    ; G =
        controlG
    ; F =
        controlF
    ; orcslpgf =
        canonicalORCSLPGFSummary
    ; orcslpgfCountProof =
        refl
    }

------------------------------------------------------------------------
-- Explicit non-promotion eliminators.

harmonicPressureTailBoundaryDoesNotAbsorbTail :
  harmonicPressureTailAbsorbed ≡ true →
  ⊥
harmonicPressureTailBoundaryDoesNotAbsorbTail ()

harmonicPressureTailBoundaryDoesNotClosePressureTailBudget :
  pressureTailBudgetClosed ≡ true →
  ⊥
harmonicPressureTailBoundaryDoesNotClosePressureTailBudget ()

harmonicPressureTailBoundaryDoesNotProveLocalization :
  localizationTheoremProved ≡ true →
  ⊥
harmonicPressureTailBoundaryDoesNotProveLocalization ()

harmonicPressureTailBoundaryDoesNotProveTriadicLeakageIdentity :
  triadicCompensatedLeakageIdentityProved ≡ true →
  ⊥
harmonicPressureTailBoundaryDoesNotProveTriadicLeakageIdentity ()

harmonicPressureTailBoundaryDoesNotPromoteNSClay :
  nsClayPromoted ≡ true →
  ⊥
harmonicPressureTailBoundaryDoesNotPromoteNSClay ()

harmonicPressureTailBoundaryDoesNotPromoteTerminal :
  terminalPromotion ≡ true →
  ⊥
harmonicPressureTailBoundaryDoesNotPromoteTerminal ()
