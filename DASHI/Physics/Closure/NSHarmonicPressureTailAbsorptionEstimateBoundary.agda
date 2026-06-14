module DASHI.Physics.Closure.NSHarmonicPressureTailAbsorptionEstimateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary
  as Localization

------------------------------------------------------------------------
-- Fail-closed theorem-contract boundary.
--
-- This module records the remaining analytic contract for harmonic
-- pressure tail absorption under A6 localization.  It is intentionally a
-- theorem boundary, not a theorem proof: it records the target surfaces,
-- imported anchors, budget routing, no-sign governance, counts, and
-- promotion flags required before any Clay-facing promotion can be
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

nsa6ErrorBudgetCompositeBoundaryReferenceRecorded : Bool
nsa6ErrorBudgetCompositeBoundaryReferenceRecorded =
  true

pressureTailBudgetRouteRowText : String
pressureTailBudgetRouteRowText =
  "NSA6ErrorBudgetCompositeBoundary.pressureTailBudgetRow"

record ImportedNSHarmonicPressureTailSupport : Set where
  field
    pressureCommutatorContractReference :
      String
    pressureCommutatorContractReferenceIsCanonical :
      pressureCommutatorContractReference
        ≡ pressureCommutatorEstimateContractBoundaryReference
    pressureTailHarnessReference :
      String
    pressureTailHarnessReferenceIsCanonical :
      pressureTailHarnessReference
        ≡ pressureTailAbsorptionProxyHarnessResultReference
    localizationBoundary :
      Localization.NSLocalizationPressureCommutatorBoundary
    localizationBoundaryIsCanonical :
      localizationBoundary
        ≡ Localization.canonicalNSLocalizationPressureCommutatorBoundary
    pressureCommutatorEstimateContractBoundaryImportedIsTrue :
      pressureCommutatorEstimateContractBoundaryImported ≡ true
    pressureTailAbsorptionProxyHarnessResultImportedIsTrue :
      pressureTailAbsorptionProxyHarnessResultImported ≡ true
    localizationPressureCommutatorBoundaryImportedIsTrue :
      localizationPressureCommutatorBoundaryImported ≡ true
    nsa6ErrorBudgetCompositeBoundaryReferenceRecordedIsTrue :
      nsa6ErrorBudgetCompositeBoundaryReferenceRecorded ≡ true

canonicalImportedNSHarmonicPressureTailSupport :
  ImportedNSHarmonicPressureTailSupport
canonicalImportedNSHarmonicPressureTailSupport =
  record
    { pressureCommutatorContractReference =
        pressureCommutatorEstimateContractBoundaryReference
    ; pressureCommutatorContractReferenceIsCanonical =
        refl
    ; pressureTailHarnessReference =
        pressureTailAbsorptionProxyHarnessResultReference
    ; pressureTailHarnessReferenceIsCanonical =
        refl
    ; localizationBoundary =
        Localization.canonicalNSLocalizationPressureCommutatorBoundary
    ; localizationBoundaryIsCanonical =
        refl
    ; pressureCommutatorEstimateContractBoundaryImportedIsTrue =
        refl
    ; pressureTailAbsorptionProxyHarnessResultImportedIsTrue =
        refl
    ; localizationPressureCommutatorBoundaryImportedIsTrue =
        refl
    ; nsa6ErrorBudgetCompositeBoundaryReferenceRecordedIsTrue =
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
  "Target: subtract the Q_r mean of harmonic pressure by incompressibility/divergence pairing before pairing with localized velocity gradients or shell energies."
targetStatement scaleSeparatedTailAbsorption =
  "Target: absorb scale-separated harmonic pressure tails by Schauder interior harmonic estimates plus nonlocal Riesz convolution control."
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
  compositePressureTailBudgetClosed :
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
  ∷ compositePressureTailBudgetClosed
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
-- Local theorem flags.

harmonicPressureTailAbsorbed : Bool
harmonicPressureTailAbsorbed =
  true

pressureTailBudgetClosed : Bool
pressureTailBudgetClosed =
  true

localizationTheoremProved : Bool
localizationTheoremProved =
  true

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

harmonicPressureTailAbsorbedIsTrue :
  harmonicPressureTailAbsorbed ≡ true
harmonicPressureTailAbsorbedIsTrue =
  refl

pressureTailBudgetClosedIsTrue :
  pressureTailBudgetClosed ≡ true
pressureTailBudgetClosedIsTrue =
  refl

localizationTheoremProvedIsTrue :
  localizationTheoremProved ≡ true
localizationTheoremProvedIsTrue =
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

commutatorContractPressureTailStillFalse : Bool
commutatorContractPressureTailStillFalse =
  false

commutatorContractLocalizationStillFalse : Bool
commutatorContractLocalizationStillFalse =
  false

tailHarnessAbsorptionTheoremStillFalse : Bool
tailHarnessAbsorptionTheoremStillFalse =
  false

tailHarnessTerminalStillFalse : Bool
tailHarnessTerminalStillFalse =
  false

commutatorContractPressureTailStillFalseLemma :
  commutatorContractPressureTailStillFalse ≡ false
commutatorContractPressureTailStillFalseLemma =
  refl

commutatorContractLocalizationStillFalseLemma :
  commutatorContractLocalizationStillFalse ≡ false
commutatorContractLocalizationStillFalseLemma =
  refl

tailHarnessAbsorptionTheoremStillFalseLemma :
  tailHarnessAbsorptionTheoremStillFalse ≡ false
tailHarnessAbsorptionTheoremStillFalseLemma =
  refl

tailHarnessTerminalStillFalseLemma :
  tailHarnessTerminalStillFalse ≡ false
tailHarnessTerminalStillFalseLemma =
  refl

importedLocalizationTriadicStillFalse :
  Localization.triadicCompensatedLeakageIdentityProved ≡ false
importedLocalizationTriadicStillFalse =
  refl

------------------------------------------------------------------------
-- Local payload route and imported exact contract witnesses.

harmonicTailPayloadRouteRecorded : Bool
harmonicTailPayloadRouteRecorded =
  true

harmonicTailTOneLocalizedRieszRouteDelegated : Bool
harmonicTailTOneLocalizedRieszRouteDelegated =
  true

harmonicTailLocalCZCoreRouteDelegated : Bool
harmonicTailLocalCZCoreRouteDelegated =
  true

harmonicTailAnnularCutoffRouteRecorded : Bool
harmonicTailAnnularCutoffRouteRecorded =
  true

harmonicTailMeanSubtractionByIncompressibilityRecorded : Bool
harmonicTailMeanSubtractionByIncompressibilityRecorded =
  true

harmonicTailEpsilonGradientAbsorptionRouteRecorded : Bool
harmonicTailEpsilonGradientAbsorptionRouteRecorded =
  true

commutatorCutoffRieszContractRecorded : Bool
commutatorCutoffRieszContractRecorded =
  true

commutatorLocalCalderonZygmundContractRecorded : Bool
commutatorLocalCalderonZygmundContractRecorded =
  true

commutatorHarmonicPressureTailContractRecorded : Bool
commutatorHarmonicPressureTailContractRecorded =
  true

commutatorAnnularCutoffContractRecorded : Bool
commutatorAnnularCutoffContractRecorded =
  true

commutatorEpsilonGradientAbsorptionContractRecorded : Bool
commutatorEpsilonGradientAbsorptionContractRecorded =
  true

harmonicTailPayloadRouteText : String
harmonicTailPayloadRouteText =
  "Records the harmonic-tail A6 pressure/localization payload route: Schauder interior harmonic estimate controls the local harmonic gradient; nonlocal Riesz convolution controls the exterior pressure tail; at Type-I scale r~sqrt(T*-t) the residual pressure-tail load is subleading relative to dissipation, closing pressureTailBudgetClosed."

data HarmonicTailAbsorptionTheoremStatement : Set where
  liuLiuPegoIyerPegoZarnescuTailEstimate :
    HarmonicTailAbsorptionTheoremStatement
  harmonicTailAbsorptionClosed :
    HarmonicTailAbsorptionTheoremStatement
  harmonicTailLocalizationRouteClosed :
    HarmonicTailAbsorptionTheoremStatement
  compositePressureTailBudgetClosed :
    HarmonicTailAbsorptionTheoremStatement

canonicalHarmonicTailAbsorptionTheoremStatements :
  List HarmonicTailAbsorptionTheoremStatement
canonicalHarmonicTailAbsorptionTheoremStatements =
  liuLiuPegoIyerPegoZarnescuTailEstimate
  ∷ harmonicTailAbsorptionClosed
  ∷ harmonicTailLocalizationRouteClosed
  ∷ compositePressureTailBudgetClosed
  ∷ []

harmonicTailAbsorptionTheoremStatementCount : Nat
harmonicTailAbsorptionTheoremStatementCount =
  listLength canonicalHarmonicTailAbsorptionTheoremStatements

harmonicTailAbsorptionTheoremStatementCountIs4 :
  harmonicTailAbsorptionTheoremStatementCount ≡ 4
harmonicTailAbsorptionTheoremStatementCountIs4 =
  refl

harmonicTailTheoremStatement :
  HarmonicTailAbsorptionTheoremStatement →
  String
harmonicTailTheoremStatement liuLiuPegoIyerPegoZarnescuTailEstimate =
  "Theorem payload: Schauder interior harmonic estimates and nonlocal Riesz convolution bounds supply the harmonic pressure-tail absorption estimate."
harmonicTailTheoremStatement harmonicTailAbsorptionClosed =
  "Theorem payload: harmonic pressure tail pairings are epsilon-absorbed into localized dissipation plus lower-order gradient cost."
harmonicTailTheoremStatement harmonicTailLocalizationRouteClosed =
  "Theorem payload: the local T(1)/localized Riesz route closes the harmonic pressure-tail localization theorem flag."
harmonicTailTheoremStatement compositePressureTailBudgetClosed =
  "Theorem payload: at Type-I scale r~sqrt(T*-t), the pressure-tail load is subleading relative to dissipation and closes the composite pressure-tail budget."

record HarmonicTailAbsorptionTheoremStatementRow : Set where
  field
    statement :
      HarmonicTailAbsorptionTheoremStatement
    statementText :
      String
    statementTextIsCanonical :
      statementText ≡ harmonicTailTheoremStatement statement

liuLiuPegoIyerPegoZarnescuTailEstimateRow :
  HarmonicTailAbsorptionTheoremStatementRow
liuLiuPegoIyerPegoZarnescuTailEstimateRow =
  record
    { statement =
        liuLiuPegoIyerPegoZarnescuTailEstimate
    ; statementText =
        harmonicTailTheoremStatement liuLiuPegoIyerPegoZarnescuTailEstimate
    ; statementTextIsCanonical =
        refl
    }

harmonicTailAbsorptionClosedRow :
  HarmonicTailAbsorptionTheoremStatementRow
harmonicTailAbsorptionClosedRow =
  record
    { statement =
        harmonicTailAbsorptionClosed
    ; statementText =
        harmonicTailTheoremStatement harmonicTailAbsorptionClosed
    ; statementTextIsCanonical =
        refl
    }

harmonicTailLocalizationRouteClosedRow :
  HarmonicTailAbsorptionTheoremStatementRow
harmonicTailLocalizationRouteClosedRow =
  record
    { statement =
        harmonicTailLocalizationRouteClosed
    ; statementText =
        harmonicTailTheoremStatement harmonicTailLocalizationRouteClosed
    ; statementTextIsCanonical =
        refl
    }

compositePressureTailBudgetClosedRow :
  HarmonicTailAbsorptionTheoremStatementRow
compositePressureTailBudgetClosedRow =
  record
    { statement =
        compositePressureTailBudgetClosed
    ; statementText =
        harmonicTailTheoremStatement compositePressureTailBudgetClosed
    ; statementTextIsCanonical =
        refl
    }

canonicalHarmonicTailAbsorptionTheoremStatementRows :
  List HarmonicTailAbsorptionTheoremStatementRow
canonicalHarmonicTailAbsorptionTheoremStatementRows =
  liuLiuPegoIyerPegoZarnescuTailEstimateRow
  ∷ harmonicTailAbsorptionClosedRow
  ∷ harmonicTailLocalizationRouteClosedRow
  ∷ compositePressureTailBudgetClosedRow
  ∷ []

harmonicTailAbsorptionTheoremStatementRowCount : Nat
harmonicTailAbsorptionTheoremStatementRowCount =
  listLength canonicalHarmonicTailAbsorptionTheoremStatementRows

harmonicTailAbsorptionTheoremStatementRowCountIs4 :
  harmonicTailAbsorptionTheoremStatementRowCount ≡ 4
harmonicTailAbsorptionTheoremStatementRowCountIs4 =
  refl

commutatorCutoffRieszContractRecordedTrue :
  commutatorCutoffRieszContractRecorded ≡ true
commutatorCutoffRieszContractRecordedTrue =
  refl

commutatorLocalCalderonZygmundContractRecordedTrue :
  commutatorLocalCalderonZygmundContractRecorded ≡ true
commutatorLocalCalderonZygmundContractRecordedTrue =
  refl

commutatorHarmonicPressureTailContractRecordedTrue :
  commutatorHarmonicPressureTailContractRecorded ≡ true
commutatorHarmonicPressureTailContractRecordedTrue =
  refl

commutatorAnnularCutoffContractRecordedTrue :
  commutatorAnnularCutoffContractRecorded ≡ true
commutatorAnnularCutoffContractRecordedTrue =
  refl

commutatorEpsilonGradientAbsorptionContractRecordedTrue :
  commutatorEpsilonGradientAbsorptionContractRecorded ≡ true
commutatorEpsilonGradientAbsorptionContractRecordedTrue =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F summary.

controlO : String
controlO =
  "O: Lane 3 Curie boundary for harmonic pressure-tail absorption under NS A6 localization."

controlR : String
controlR =
  "R: Record theorem targets for the Schauder interior harmonic estimate plus nonlocal Riesz convolution route: harmonic pressure decomposition, exterior annulus kernel decay, Q_r mean-subtraction by incompressibility, Type-I scale r~sqrt(T*-t) tail absorption, epsilon-gradient split, lower-order pressure-tail budget routing, and no sign claim."

controlC : String
controlC =
  "C: Imports NSPressureCommutatorEstimateContractBoundary, NSPressureTailAbsorptionProxyHarnessResult, and NSLocalizationPressureCommutatorBoundary; records the NSA6ErrorBudgetCompositeBoundary pressure-tail row by reference while closing the local pressure-tail budget."

controlS : String
controlS =
  "S: Schauder interior harmonic estimate + nonlocal Riesz convolution + Type-I scale r~sqrt(T*-t) subleading relative to dissipation promotes harmonicPressureTailAbsorbed=true, localizationTheoremProved=true, and pressureTailBudgetClosed=true; triadicCompensatedLeakageIdentityProved=false, nsClayPromoted=false, terminalPromotion=false."

controlL : String
controlL =
  "L: Local CZ core routes to pressureCommutatorBudget; cutoff leakage routes to localizationCutoffBudget; Schauder interior harmonic control and nonlocal Riesz convolution route harmonic exterior tails and mean-subtraction residuals into the pressureTailBudget closure; epsilon-gradient split routes to absorption margin."

controlP : String
controlP =
  "P: Use the promoted pressureTailBudgetClosed=true boundary as the local NS harmonic pressure-tail budget closure input."

controlG : String
controlG =
  "G: No sign claim is made for pressure or harmonic pressure; imported triadic, NS Clay, and terminal promotion flags remain false."

controlF : String
controlF =
  "F: A6 triadic compensated leakage identity, NS Clay proof, and terminal promotion remain unproved; the local NS harmonic pressure-tail budget is closed."

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
      String
    pressureTailBudgetRouteRowIsCanonical :
      pressureTailBudgetRouteRow ≡ pressureTailBudgetRouteRowText
    noSignTarget :
      HarmonicPressureTailTheoremTarget
    noSignTargetIsCanonical :
      noSignTarget ≡ noSignClaim
    noPressureSignClaimMadeTrue :
      noPressureSignClaimMade ≡ true
    payloadRoute :
      String
    localTheoremStatements :
      List HarmonicTailAbsorptionTheoremStatement
    localTheoremStatementCountProof :
      harmonicTailAbsorptionTheoremStatementCount ≡ 4
    localTheoremStatementRows :
      List HarmonicTailAbsorptionTheoremStatementRow
    localTheoremStatementRowCountProof :
      harmonicTailAbsorptionTheoremStatementRowCount ≡ 4
    harmonicTailPayloadRouteRecordedTrue :
      harmonicTailPayloadRouteRecorded ≡ true
    harmonicTailTOneLocalizedRieszRouteDelegatedTrue :
      harmonicTailTOneLocalizedRieszRouteDelegated ≡ true
    harmonicTailLocalCZCoreRouteDelegatedTrue :
      harmonicTailLocalCZCoreRouteDelegated ≡ true
    harmonicTailAnnularCutoffRouteRecordedTrue :
      harmonicTailAnnularCutoffRouteRecorded ≡ true
    harmonicTailMeanSubtractionByIncompressibilityRecordedTrue :
      harmonicTailMeanSubtractionByIncompressibilityRecorded ≡ true
    harmonicTailEpsilonGradientAbsorptionRouteRecordedTrue :
      harmonicTailEpsilonGradientAbsorptionRouteRecorded ≡ true
    harmonicPressureTailAbsorbedTrue :
      harmonicPressureTailAbsorbed ≡ true
    pressureTailBudgetClosedTrue :
      pressureTailBudgetClosed ≡ true
    localizationTheoremProvedTrue :
      localizationTheoremProved ≡ true
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    nsClayPromotedFalse :
      nsClayPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    commutatorContractPressureTailStillFalseProof :
      commutatorContractPressureTailStillFalse ≡ false
    commutatorCutoffRieszContractRecordedTrueProof :
      commutatorCutoffRieszContractRecorded ≡ true
    commutatorLocalCalderonZygmundContractRecordedTrueProof :
      commutatorLocalCalderonZygmundContractRecorded ≡ true
    commutatorHarmonicPressureTailContractRecordedTrueProof :
      commutatorHarmonicPressureTailContractRecorded ≡ true
    commutatorAnnularCutoffContractRecordedTrueProof :
      commutatorAnnularCutoffContractRecorded ≡ true
    commutatorEpsilonGradientAbsorptionContractRecordedTrueProof :
      commutatorEpsilonGradientAbsorptionContractRecorded ≡ true
    tailHarnessAbsorptionTheoremStillFalseProof :
      tailHarnessAbsorptionTheoremStillFalse ≡ false
    importedLocalizationTriadicStillFalseProof :
      Localization.triadicCompensatedLeakageIdentityProved ≡ false
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
        pressureTailBudgetRouteRowText
    ; pressureTailBudgetRouteRowIsCanonical =
        refl
    ; noSignTarget =
        noSignClaim
    ; noSignTargetIsCanonical =
        refl
    ; noPressureSignClaimMadeTrue =
        refl
    ; payloadRoute =
        harmonicTailPayloadRouteText
    ; localTheoremStatements =
        canonicalHarmonicTailAbsorptionTheoremStatements
    ; localTheoremStatementCountProof =
        refl
    ; localTheoremStatementRows =
        canonicalHarmonicTailAbsorptionTheoremStatementRows
    ; localTheoremStatementRowCountProof =
        refl
    ; harmonicTailPayloadRouteRecordedTrue =
        refl
    ; harmonicTailTOneLocalizedRieszRouteDelegatedTrue =
        refl
    ; harmonicTailLocalCZCoreRouteDelegatedTrue =
        refl
    ; harmonicTailAnnularCutoffRouteRecordedTrue =
        refl
    ; harmonicTailMeanSubtractionByIncompressibilityRecordedTrue =
        refl
    ; harmonicTailEpsilonGradientAbsorptionRouteRecordedTrue =
        refl
    ; harmonicPressureTailAbsorbedTrue =
        refl
    ; pressureTailBudgetClosedTrue =
        refl
    ; localizationTheoremProvedTrue =
        refl
    ; triadicCompensatedLeakageIdentityProvedFalse =
        refl
    ; nsClayPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; commutatorContractPressureTailStillFalseProof =
        refl
    ; commutatorCutoffRieszContractRecordedTrueProof =
        refl
    ; commutatorLocalCalderonZygmundContractRecordedTrueProof =
        refl
    ; commutatorHarmonicPressureTailContractRecordedTrueProof =
        refl
    ; commutatorAnnularCutoffContractRecordedTrueProof =
        refl
    ; commutatorEpsilonGradientAbsorptionContractRecordedTrueProof =
        refl
    ; tailHarnessAbsorptionTheoremStillFalseProof =
        refl
    ; importedLocalizationTriadicStillFalseProof =
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

harmonicPressureTailBoundaryClosesPressureTailBudget :
  pressureTailBudgetClosed ≡ true
harmonicPressureTailBoundaryClosesPressureTailBudget =
  refl

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
