module DASHI.Physics.Closure.NSPressureLocalizationSubBudgetCompositeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary
  as ErrorBudget
import DASHI.Physics.Closure.NSCutoffRieszCommutatorKernelProxyHarnessResult
  as CutoffRiesz
import DASHI.Physics.Closure.NSHarmonicPressureTailAbsorptionEstimateBoundary
  as HarmonicTail
import DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary
  as Contract
import DASHI.Physics.Closure.NSPressureTailAbsorptionProxyHarnessResult
  as TailProxy

------------------------------------------------------------------------
-- NS A6 pressure/localization sub-budget composite boundary.
--
-- This module is the narrow pressure/localization budget surface under
-- NSA6ErrorBudgetCompositeBoundary.  It composes the theorem-contract and
-- diagnostic receipts for:
--
--   * cutoff/Riesz commutator control,
--   * local Calderon-Zygmund pressure core,
--   * harmonic pressure tail,
--   * pressure-tail proxy evidence,
--   * annular cutoff leakage,
--   * epsilon-gradient absorption,
--   * Abel recentering / lower-order routing.
--
-- It is fail-closed.  The composite records ownership, routing, and
-- governance only.  It does not prove the pressure sub-budget, the
-- localization theorem, A6, residual nonpositivity, NS Clay, or terminal
-- promotion.

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

cutoffRieszCommutatorKernelProxyHarnessResultReference : String
cutoffRieszCommutatorKernelProxyHarnessResultReference =
  "DASHI.Physics.Closure.NSCutoffRieszCommutatorKernelProxyHarnessResult"

harmonicPressureTailAbsorptionEstimateBoundaryReference : String
harmonicPressureTailAbsorptionEstimateBoundaryReference =
  "DASHI.Physics.Closure.NSHarmonicPressureTailAbsorptionEstimateBoundary"

nsa6ErrorBudgetCompositeBoundaryReference : String
nsa6ErrorBudgetCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary"

pressureCommutatorEstimateContractBoundaryImported : Bool
pressureCommutatorEstimateContractBoundaryImported =
  true

pressureTailAbsorptionProxyHarnessResultImported : Bool
pressureTailAbsorptionProxyHarnessResultImported =
  true

cutoffRieszCommutatorKernelProxyHarnessResultImported : Bool
cutoffRieszCommutatorKernelProxyHarnessResultImported =
  true

harmonicPressureTailAbsorptionEstimateBoundaryImported : Bool
harmonicPressureTailAbsorptionEstimateBoundaryImported =
  true

nsa6ErrorBudgetCompositeBoundaryImported : Bool
nsa6ErrorBudgetCompositeBoundaryImported =
  true

record ImportedNSPressureLocalizationSubBudgetSupport : Set where
  field
    pressureCommutatorContract :
      Contract.NSPressureCommutatorEstimateContractBoundary
    pressureCommutatorContractIsCanonical :
      pressureCommutatorContract
        ≡ Contract.canonicalNSPressureCommutatorEstimateContractBoundary
    pressureTailProxy :
      TailProxy.NSPressureTailAbsorptionProxyHarnessResult
    pressureTailProxyIsCanonical :
      pressureTailProxy
        ≡ TailProxy.canonicalNSPressureTailAbsorptionProxyHarnessResult
    cutoffRieszProxy :
      CutoffRiesz.NSCutoffRieszCommutatorKernelProxyHarnessResult
    cutoffRieszProxyIsCanonical :
      cutoffRieszProxy
        ≡ CutoffRiesz.canonicalNSCutoffRieszCommutatorKernelProxyHarnessResult
    harmonicPressureTailBoundary :
      HarmonicTail.NSHarmonicPressureTailAbsorptionEstimateBoundary
    harmonicPressureTailBoundaryIsCanonical :
      harmonicPressureTailBoundary
        ≡ HarmonicTail.canonicalNSHarmonicPressureTailAbsorptionEstimateBoundary
    errorBudgetComposite :
      ErrorBudget.NSA6ErrorBudgetCompositeBoundary
    errorBudgetCompositeIsCanonical :
      errorBudgetComposite
        ≡ ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    pressureCommutatorEstimateContractBoundaryImportedIsTrue :
      pressureCommutatorEstimateContractBoundaryImported ≡ true
    pressureTailAbsorptionProxyHarnessResultImportedIsTrue :
      pressureTailAbsorptionProxyHarnessResultImported ≡ true
    cutoffRieszCommutatorKernelProxyHarnessResultImportedIsTrue :
      cutoffRieszCommutatorKernelProxyHarnessResultImported ≡ true
    harmonicPressureTailAbsorptionEstimateBoundaryImportedIsTrue :
      harmonicPressureTailAbsorptionEstimateBoundaryImported ≡ true
    nsa6ErrorBudgetCompositeBoundaryImportedIsTrue :
      nsa6ErrorBudgetCompositeBoundaryImported ≡ true
    importedContractKeepsPressureCommutatorFalse :
      Contract.pressureCommutatorEstimateProved ≡ false
    importedContractKeepsLocalizationFalse :
      Contract.localizationTheoremProved ≡ false
    importedContractKeepsA6False :
      Contract.triadicCompensatedLeakageIdentityProved ≡ false
    importedTailProxyKeepsTailTheoremFalse :
      TailProxy.pressureTailAbsorptionTheoremProved ≡ false
    importedTailProxyKeepsA6False :
      TailProxy.A6Proved ≡ false
    importedCutoffRieszKeepsCommutatorFalse :
      CutoffRiesz.cutoffRieszCommutatorEstimateProved ≡ false
    importedCutoffRieszKeepsLocalizationFalse :
      CutoffRiesz.localizationTheoremProved ≡ false
    importedHarmonicTailBudgetClosed :
      HarmonicTail.pressureTailBudgetClosed ≡ true
    importedHarmonicTailLocalizationNowTrue :
      HarmonicTail.localizationTheoremProved ≡ true
    importedHarmonicTailKeepsA6False :
      HarmonicTail.triadicCompensatedLeakageIdentityProved ≡ false
    importedErrorBudgetAggregatePromoted :
      ErrorBudget.aggregateErrorBudgetProved ≡ true
    importedErrorBudgetKeepsResidualFalse :
      ErrorBudget.residualDepletionProved ≡ false
    importedErrorBudgetKeepsNSClayFalse :
      ErrorBudget.nsClayPromoted ≡ false
    importedErrorBudgetKeepsTerminalFalse :
      ErrorBudget.terminalPromotionPromoted ≡ false

canonicalImportedNSPressureLocalizationSubBudgetSupport :
  ImportedNSPressureLocalizationSubBudgetSupport
canonicalImportedNSPressureLocalizationSubBudgetSupport =
  record
    { pressureCommutatorContract =
        Contract.canonicalNSPressureCommutatorEstimateContractBoundary
    ; pressureCommutatorContractIsCanonical =
        refl
    ; pressureTailProxy =
        TailProxy.canonicalNSPressureTailAbsorptionProxyHarnessResult
    ; pressureTailProxyIsCanonical =
        refl
    ; cutoffRieszProxy =
        CutoffRiesz.canonicalNSCutoffRieszCommutatorKernelProxyHarnessResult
    ; cutoffRieszProxyIsCanonical =
        refl
    ; harmonicPressureTailBoundary =
        HarmonicTail.canonicalNSHarmonicPressureTailAbsorptionEstimateBoundary
    ; harmonicPressureTailBoundaryIsCanonical =
        refl
    ; errorBudgetComposite =
        ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    ; errorBudgetCompositeIsCanonical =
        refl
    ; pressureCommutatorEstimateContractBoundaryImportedIsTrue =
        refl
    ; pressureTailAbsorptionProxyHarnessResultImportedIsTrue =
        refl
    ; cutoffRieszCommutatorKernelProxyHarnessResultImportedIsTrue =
        refl
    ; harmonicPressureTailAbsorptionEstimateBoundaryImportedIsTrue =
        refl
    ; nsa6ErrorBudgetCompositeBoundaryImportedIsTrue =
        refl
    ; importedContractKeepsPressureCommutatorFalse =
        refl
    ; importedContractKeepsLocalizationFalse =
        refl
    ; importedContractKeepsA6False =
        refl
    ; importedTailProxyKeepsTailTheoremFalse =
        refl
    ; importedTailProxyKeepsA6False =
        refl
    ; importedCutoffRieszKeepsCommutatorFalse =
        refl
    ; importedCutoffRieszKeepsLocalizationFalse =
        refl
    ; importedHarmonicTailBudgetClosed =
        refl
    ; importedHarmonicTailLocalizationNowTrue =
        refl
    ; importedHarmonicTailKeepsA6False =
        refl
    ; importedErrorBudgetAggregatePromoted =
        refl
    ; importedErrorBudgetKeepsResidualFalse =
        refl
    ; importedErrorBudgetKeepsNSClayFalse =
        refl
    ; importedErrorBudgetKeepsTerminalFalse =
        refl
    }

------------------------------------------------------------------------
-- Pressure/localization sub-budget rows.

data NSPressureLocalizationSubBudgetLine : Set where
  cutoffRieszCommutatorBudget :
    NSPressureLocalizationSubBudgetLine
  localCalderonZygmundCoreBudget :
    NSPressureLocalizationSubBudgetLine
  harmonicPressureTailBudget :
    NSPressureLocalizationSubBudgetLine
  pressureTailProxyBudget :
    NSPressureLocalizationSubBudgetLine
  annularCutoffBudget :
    NSPressureLocalizationSubBudgetLine
  epsilonGradientAbsorptionBudget :
    NSPressureLocalizationSubBudgetLine
  abelRecenteringLowerOrderRoutingBudget :
    NSPressureLocalizationSubBudgetLine

canonicalNSPressureLocalizationSubBudgetLines :
  List NSPressureLocalizationSubBudgetLine
canonicalNSPressureLocalizationSubBudgetLines =
  cutoffRieszCommutatorBudget
  ∷ localCalderonZygmundCoreBudget
  ∷ harmonicPressureTailBudget
  ∷ pressureTailProxyBudget
  ∷ annularCutoffBudget
  ∷ epsilonGradientAbsorptionBudget
  ∷ abelRecenteringLowerOrderRoutingBudget
  ∷ []

nsPressureLocalizationSubBudgetLineCount : Nat
nsPressureLocalizationSubBudgetLineCount =
  listLength canonicalNSPressureLocalizationSubBudgetLines

nsPressureLocalizationSubBudgetLineCountIs7 :
  nsPressureLocalizationSubBudgetLineCount ≡ 7
nsPressureLocalizationSubBudgetLineCountIs7 =
  refl

data NSPressureLocalizationOwner : Set where
  owner-NSPressureCommutatorEstimateContractBoundary :
    NSPressureLocalizationOwner
  owner-NSCutoffRieszCommutatorKernelProxyHarnessResult :
    NSPressureLocalizationOwner
  owner-NSHarmonicPressureTailAbsorptionEstimateBoundary :
    NSPressureLocalizationOwner
  owner-NSPressureTailAbsorptionProxyHarnessResult :
    NSPressureLocalizationOwner
  owner-NSA6ErrorBudgetCompositeBoundary :
    NSPressureLocalizationOwner

ownerOfSubBudget :
  NSPressureLocalizationSubBudgetLine →
  NSPressureLocalizationOwner
ownerOfSubBudget cutoffRieszCommutatorBudget =
  owner-NSCutoffRieszCommutatorKernelProxyHarnessResult
ownerOfSubBudget localCalderonZygmundCoreBudget =
  owner-NSPressureCommutatorEstimateContractBoundary
ownerOfSubBudget harmonicPressureTailBudget =
  owner-NSHarmonicPressureTailAbsorptionEstimateBoundary
ownerOfSubBudget pressureTailProxyBudget =
  owner-NSPressureTailAbsorptionProxyHarnessResult
ownerOfSubBudget annularCutoffBudget =
  owner-NSPressureCommutatorEstimateContractBoundary
ownerOfSubBudget epsilonGradientAbsorptionBudget =
  owner-NSPressureCommutatorEstimateContractBoundary
ownerOfSubBudget abelRecenteringLowerOrderRoutingBudget =
  owner-NSA6ErrorBudgetCompositeBoundary

data NSA6CompositeRoute : Set where
  route-pressureCommutatorBudget :
    NSA6CompositeRoute
  route-pressureTailBudget :
    NSA6CompositeRoute
  route-localizationCutoffBudget :
    NSA6CompositeRoute
  route-offDiagonalAbsorptionBudget :
    NSA6CompositeRoute
  route-abelTailRecenteringBudget :
    NSA6CompositeRoute

routeOfSubBudget :
  NSPressureLocalizationSubBudgetLine →
  NSA6CompositeRoute
routeOfSubBudget cutoffRieszCommutatorBudget =
  route-pressureCommutatorBudget
routeOfSubBudget localCalderonZygmundCoreBudget =
  route-pressureCommutatorBudget
routeOfSubBudget harmonicPressureTailBudget =
  route-pressureTailBudget
routeOfSubBudget pressureTailProxyBudget =
  route-pressureTailBudget
routeOfSubBudget annularCutoffBudget =
  route-localizationCutoffBudget
routeOfSubBudget epsilonGradientAbsorptionBudget =
  route-offDiagonalAbsorptionBudget
routeOfSubBudget abelRecenteringLowerOrderRoutingBudget =
  route-abelTailRecenteringBudget

subBudgetDescription :
  NSPressureLocalizationSubBudgetLine →
  String
subBudgetDescription cutoffRieszCommutatorBudget =
  "Cutoff/Riesz commutator: [P_j,phi] R_i R_l kernel cancellation, dyadic moment gain, annular separation, and shell recentering diagnostics before the PDE commutator theorem."
subBudgetDescription localCalderonZygmundCoreBudget =
  "Local CZ core: pressure reconstructed by local Calderon-Zygmund/Riesz operators after cylinder mean subtraction, with no favorable pressure sign claim."
subBudgetDescription harmonicPressureTailBudget =
  "Harmonic tail: exterior pressure split, Q_r mean subtraction, annular kernel decay, and scale-separated absorption into the pressure-tail budget."
subBudgetDescription pressureTailProxyBudget =
  "Pressure-tail proxy: compact/Schwartz/localized diagnostic split versus harmonic-tail, annular-plateau, and nonabsorbed-gradient bad profiles."
subBudgetDescription annularCutoffBudget =
  "Annular cutoff: cutoff derivative, boundary annulus, nearby-source, and core-touching errors routed to localization-cutoff or lower-order budgets."
subBudgetDescription epsilonGradientAbsorptionBudget =
  "Epsilon-gradient absorption: commutator and pressure-tail pairings split into epsilon localized gradient dissipation plus controlled lower-order residuals."
subBudgetDescription abelRecenteringLowerOrderRoutingBudget =
  "Abel recentering and lower order: shell recenter drift, Abel endpoint/tail terms, pressure average residuals, and lower-order routing into the A6 composite budget."

record NSPressureLocalizationSubBudgetRow : Set where
  field
    subBudget :
      NSPressureLocalizationSubBudgetLine
    owner :
      NSPressureLocalizationOwner
    ownerIsAssigned :
      ownerOfSubBudget subBudget ≡ owner
    a6CompositeRoute :
      NSA6CompositeRoute
    routeIsAssigned :
      routeOfSubBudget subBudget ≡ a6CompositeRoute
    description :
      String
    descriptionIsCanonical :
      description ≡ subBudgetDescription subBudget

cutoffRieszCommutatorBudgetRow :
  NSPressureLocalizationSubBudgetRow
cutoffRieszCommutatorBudgetRow =
  record
    { subBudget =
        cutoffRieszCommutatorBudget
    ; owner =
        owner-NSCutoffRieszCommutatorKernelProxyHarnessResult
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-pressureCommutatorBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription cutoffRieszCommutatorBudget
    ; descriptionIsCanonical =
        refl
    }

localCalderonZygmundCoreBudgetRow :
  NSPressureLocalizationSubBudgetRow
localCalderonZygmundCoreBudgetRow =
  record
    { subBudget =
        localCalderonZygmundCoreBudget
    ; owner =
        owner-NSPressureCommutatorEstimateContractBoundary
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-pressureCommutatorBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription localCalderonZygmundCoreBudget
    ; descriptionIsCanonical =
        refl
    }

harmonicPressureTailBudgetRow :
  NSPressureLocalizationSubBudgetRow
harmonicPressureTailBudgetRow =
  record
    { subBudget =
        harmonicPressureTailBudget
    ; owner =
        owner-NSHarmonicPressureTailAbsorptionEstimateBoundary
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-pressureTailBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription harmonicPressureTailBudget
    ; descriptionIsCanonical =
        refl
    }

pressureTailProxyBudgetRow :
  NSPressureLocalizationSubBudgetRow
pressureTailProxyBudgetRow =
  record
    { subBudget =
        pressureTailProxyBudget
    ; owner =
        owner-NSPressureTailAbsorptionProxyHarnessResult
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-pressureTailBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription pressureTailProxyBudget
    ; descriptionIsCanonical =
        refl
    }

annularCutoffBudgetRow :
  NSPressureLocalizationSubBudgetRow
annularCutoffBudgetRow =
  record
    { subBudget =
        annularCutoffBudget
    ; owner =
        owner-NSPressureCommutatorEstimateContractBoundary
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-localizationCutoffBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription annularCutoffBudget
    ; descriptionIsCanonical =
        refl
    }

epsilonGradientAbsorptionBudgetRow :
  NSPressureLocalizationSubBudgetRow
epsilonGradientAbsorptionBudgetRow =
  record
    { subBudget =
        epsilonGradientAbsorptionBudget
    ; owner =
        owner-NSPressureCommutatorEstimateContractBoundary
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-offDiagonalAbsorptionBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription epsilonGradientAbsorptionBudget
    ; descriptionIsCanonical =
        refl
    }

abelRecenteringLowerOrderRoutingBudgetRow :
  NSPressureLocalizationSubBudgetRow
abelRecenteringLowerOrderRoutingBudgetRow =
  record
    { subBudget =
        abelRecenteringLowerOrderRoutingBudget
    ; owner =
        owner-NSA6ErrorBudgetCompositeBoundary
    ; ownerIsAssigned =
        refl
    ; a6CompositeRoute =
        route-abelTailRecenteringBudget
    ; routeIsAssigned =
        refl
    ; description =
        subBudgetDescription abelRecenteringLowerOrderRoutingBudget
    ; descriptionIsCanonical =
        refl
    }

canonicalNSPressureLocalizationSubBudgetRows :
  List NSPressureLocalizationSubBudgetRow
canonicalNSPressureLocalizationSubBudgetRows =
  cutoffRieszCommutatorBudgetRow
  ∷ localCalderonZygmundCoreBudgetRow
  ∷ harmonicPressureTailBudgetRow
  ∷ pressureTailProxyBudgetRow
  ∷ annularCutoffBudgetRow
  ∷ epsilonGradientAbsorptionBudgetRow
  ∷ abelRecenteringLowerOrderRoutingBudgetRow
  ∷ []

nsPressureLocalizationSubBudgetRowCount : Nat
nsPressureLocalizationSubBudgetRowCount =
  listLength canonicalNSPressureLocalizationSubBudgetRows

nsPressureLocalizationSubBudgetRowCountIs7 :
  nsPressureLocalizationSubBudgetRowCount ≡ 7
nsPressureLocalizationSubBudgetRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Composite blockers and governance.

data NSPressureLocalizationSubBudgetBlocker : Set where
  missingCutoffRieszCommutatorKernelEstimate :
    NSPressureLocalizationSubBudgetBlocker
  missingLocalCalderonZygmundPressureCoreEstimate :
    NSPressureLocalizationSubBudgetBlocker
  missingHarmonicPressureTailDecayAndAbsorption :
    NSPressureLocalizationSubBudgetBlocker
  missingPressureTailProxyToPDETransfer :
    NSPressureLocalizationSubBudgetBlocker
  missingAnnularCutoffBoundaryEstimate :
    NSPressureLocalizationSubBudgetBlocker
  missingEpsilonGradientAbsorptionInequality :
    NSPressureLocalizationSubBudgetBlocker
  missingAbelRecenteringLowerOrderClosure :
    NSPressureLocalizationSubBudgetBlocker
  missingAggregatePressureSubBudgetClosure :
    NSPressureLocalizationSubBudgetBlocker

canonicalNSPressureLocalizationSubBudgetBlockers :
  List NSPressureLocalizationSubBudgetBlocker
canonicalNSPressureLocalizationSubBudgetBlockers =
  missingCutoffRieszCommutatorKernelEstimate
  ∷ missingLocalCalderonZygmundPressureCoreEstimate
  ∷ missingHarmonicPressureTailDecayAndAbsorption
  ∷ missingPressureTailProxyToPDETransfer
  ∷ missingAnnularCutoffBoundaryEstimate
  ∷ missingEpsilonGradientAbsorptionInequality
  ∷ missingAbelRecenteringLowerOrderClosure
  ∷ missingAggregatePressureSubBudgetClosure
  ∷ []

nsPressureLocalizationSubBudgetBlockerCount : Nat
nsPressureLocalizationSubBudgetBlockerCount =
  listLength canonicalNSPressureLocalizationSubBudgetBlockers

nsPressureLocalizationSubBudgetBlockerCountIs8 :
  nsPressureLocalizationSubBudgetBlockerCount ≡ 8
nsPressureLocalizationSubBudgetBlockerCountIs8 =
  refl

data NSPressureLocalizationNonClaimGuard : Set where
  noPressureSignClaim :
    NSPressureLocalizationNonClaimGuard
  noPointwisePressurePositivityClaim :
    NSPressureLocalizationNonClaimGuard
  noCutoffRieszTheoremClaim :
    NSPressureLocalizationNonClaimGuard
  noHarmonicTailTheoremClaim :
    NSPressureLocalizationNonClaimGuard
  noPressureTailProxyPromotion :
    NSPressureLocalizationNonClaimGuard
  noLocalizationTheoremClaim :
    NSPressureLocalizationNonClaimGuard
  noA6OrResidualClaim :
    NSPressureLocalizationNonClaimGuard
  noClayOrTerminalPromotion :
    NSPressureLocalizationNonClaimGuard

canonicalNSPressureLocalizationNonClaimGuards :
  List NSPressureLocalizationNonClaimGuard
canonicalNSPressureLocalizationNonClaimGuards =
  noPressureSignClaim
  ∷ noPointwisePressurePositivityClaim
  ∷ noCutoffRieszTheoremClaim
  ∷ noHarmonicTailTheoremClaim
  ∷ noPressureTailProxyPromotion
  ∷ noLocalizationTheoremClaim
  ∷ noA6OrResidualClaim
  ∷ noClayOrTerminalPromotion
  ∷ []

nsPressureLocalizationNonClaimGuardCount : Nat
nsPressureLocalizationNonClaimGuardCount =
  listLength canonicalNSPressureLocalizationNonClaimGuards

nsPressureLocalizationNonClaimGuardCountIs8 :
  nsPressureLocalizationNonClaimGuardCount ≡ 8
nsPressureLocalizationNonClaimGuardCountIs8 =
  refl

pressureSubBudgetClosed : Bool
pressureSubBudgetClosed =
  false

localizationTheoremProved : Bool
localizationTheoremProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

residualNonPositiveProved : Bool
residualNonPositiveProved =
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

pressureSubBudgetClosedIsFalse :
  pressureSubBudgetClosed ≡ false
pressureSubBudgetClosedIsFalse =
  refl

localizationTheoremProvedIsFalse :
  localizationTheoremProved ≡ false
localizationTheoremProvedIsFalse =
  refl

triadicCompensatedLeakageIdentityProvedIsFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
triadicCompensatedLeakageIdentityProvedIsFalse =
  refl

residualNonPositiveProvedIsFalse :
  residualNonPositiveProved ≡ false
residualNonPositiveProvedIsFalse =
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

canonicalNSPressureLocalizationSubBudgetSummary : String
canonicalNSPressureLocalizationSubBudgetSummary =
  "Records the NS A6 pressure/localization sub-budget composite: cutoff/Riesz commutator, local CZ core, harmonic pressure tail, pressure-tail proxy, annular cutoff, epsilon-gradient absorption, and Abel recentering/lower-order routing. All theorem and promotion flags remain false."

canonicalORCSLPGFSummary : String
canonicalORCSLPGFSummary =
  "O Lane 1 Noether pressure/localization sub-budget composite; R compose the imported A6 pressure surfaces into one fail-closed pressure sub-budget; C imports NSPressureCommutatorEstimateContractBoundary, NSPressureTailAbsorptionProxyHarnessResult, NSCutoffRieszCommutatorKernelProxyHarnessResult, NSHarmonicPressureTailAbsorptionEstimateBoundary, and NSA6ErrorBudgetCompositeBoundary; S pressureSubBudgetClosed=false, localizationTheoremProved=false, triadicCompensatedLeakageIdentityProved=false, residualNonPositiveProved=false, nsClayPromoted=false, terminalPromotion=false; L each row routes to pressureCommutatorBudget, pressureTailBudget, localizationCutoffBudget, offDiagonalAbsorptionBudget, or abelTailRecenteringBudget before A6; P prove each row as a real PDE estimate before attempting aggregate A6; G diagnostics and boundaries do not promote; F pressure sub-budget, localization, A6, residual nonpositivity, NS Clay, and terminal promotion remain open."

data ORCSLPGFRow : Set where
  O-laneOneNoetherPressureLocalizationSubBudget :
    ORCSLPGFRow
  R-composeImportedPressureSurfaces :
    ORCSLPGFRow
  C-fiveImportedA6PressureAnchors :
    ORCSLPGFRow
  S-allTheoremPromotionFlagsFalse :
    ORCSLPGFRow
  L-subBudgetsRouteIntoA6CompositeBudget :
    ORCSLPGFRow
  P-proveRowsBeforeAggregateA6 :
    ORCSLPGFRow
  G-diagnosticsAndBoundariesDoNotPromote :
    ORCSLPGFRow
  F-pressureLocalizationTheoremsRemainOpen :
    ORCSLPGFRow

canonicalORCSLPGFRows : List ORCSLPGFRow
canonicalORCSLPGFRows =
  O-laneOneNoetherPressureLocalizationSubBudget
  ∷ R-composeImportedPressureSurfaces
  ∷ C-fiveImportedA6PressureAnchors
  ∷ S-allTheoremPromotionFlagsFalse
  ∷ L-subBudgetsRouteIntoA6CompositeBudget
  ∷ P-proveRowsBeforeAggregateA6
  ∷ G-diagnosticsAndBoundariesDoNotPromote
  ∷ F-pressureLocalizationTheoremsRemainOpen
  ∷ []

orcsLpgfRowCount : Nat
orcsLpgfRowCount =
  listLength canonicalORCSLPGFRows

orcsLpgfRowCountIs8 :
  orcsLpgfRowCount ≡ 8
orcsLpgfRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Canonical composite boundary.

data NSPressureLocalizationSubBudgetCompositeStatus : Set where
  nsPressureLocalizationSubBudgetCompositeBoundaryRecorded_noPromotion :
    NSPressureLocalizationSubBudgetCompositeStatus

record NSPressureLocalizationSubBudgetCompositeBoundary : Set where
  field
    status :
      NSPressureLocalizationSubBudgetCompositeStatus
    statusIsCanonical :
      status
        ≡ nsPressureLocalizationSubBudgetCompositeBoundaryRecorded_noPromotion
    importedSupport :
      ImportedNSPressureLocalizationSubBudgetSupport
    subBudgetLines :
      List NSPressureLocalizationSubBudgetLine
    subBudgetLineCountProof :
      nsPressureLocalizationSubBudgetLineCount ≡ 7
    subBudgetRows :
      List NSPressureLocalizationSubBudgetRow
    subBudgetRowCountProof :
      nsPressureLocalizationSubBudgetRowCount ≡ 7
    blockers :
      List NSPressureLocalizationSubBudgetBlocker
    blockerCountProof :
      nsPressureLocalizationSubBudgetBlockerCount ≡ 8
    nonClaimGuards :
      List NSPressureLocalizationNonClaimGuard
    nonClaimGuardCountProof :
      nsPressureLocalizationNonClaimGuardCount ≡ 8
    orcsLpgfRows :
      List ORCSLPGFRow
    orcsLpgfRowCountProof :
      orcsLpgfRowCount ≡ 8
    summary :
      String
    summaryIsCanonical :
      summary ≡ canonicalNSPressureLocalizationSubBudgetSummary
    orcsLpgfSummary :
      String
    pressureSubBudgetClosedBoundaryIsFalse :
      pressureSubBudgetClosed ≡ false
    localizationTheoremProvedBoundaryIsFalse :
      localizationTheoremProved ≡ false
    triadicCompensatedLeakageIdentityProvedBoundaryIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualNonPositiveProvedBoundaryIsFalse :
      residualNonPositiveProved ≡ false
    nsClayPromotedBoundaryIsFalse :
      nsClayPromoted ≡ false
    terminalPromotionBoundaryIsFalse :
      terminalPromotion ≡ false
    noPressureSignClaimMadeBoundaryIsTrue :
      noPressureSignClaimMade ≡ true

canonicalNSPressureLocalizationSubBudgetCompositeBoundary :
  NSPressureLocalizationSubBudgetCompositeBoundary
canonicalNSPressureLocalizationSubBudgetCompositeBoundary =
  record
    { status =
        nsPressureLocalizationSubBudgetCompositeBoundaryRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedNSPressureLocalizationSubBudgetSupport
    ; subBudgetLines =
        canonicalNSPressureLocalizationSubBudgetLines
    ; subBudgetLineCountProof =
        refl
    ; subBudgetRows =
        canonicalNSPressureLocalizationSubBudgetRows
    ; subBudgetRowCountProof =
        refl
    ; blockers =
        canonicalNSPressureLocalizationSubBudgetBlockers
    ; blockerCountProof =
        refl
    ; nonClaimGuards =
        canonicalNSPressureLocalizationNonClaimGuards
    ; nonClaimGuardCountProof =
        refl
    ; orcsLpgfRows =
        canonicalORCSLPGFRows
    ; orcsLpgfRowCountProof =
        refl
    ; summary =
        canonicalNSPressureLocalizationSubBudgetSummary
    ; summaryIsCanonical =
        refl
    ; orcsLpgfSummary =
        canonicalORCSLPGFSummary
    ; pressureSubBudgetClosedBoundaryIsFalse =
        refl
    ; localizationTheoremProvedBoundaryIsFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedBoundaryIsFalse =
        refl
    ; residualNonPositiveProvedBoundaryIsFalse =
        refl
    ; nsClayPromotedBoundaryIsFalse =
        refl
    ; terminalPromotionBoundaryIsFalse =
        refl
    ; noPressureSignClaimMadeBoundaryIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: composite bookkeeping is not theorem closure.

postulate
  nsPressureLocalizationSubBudgetCompositeDoesNotClosePressureSubBudget :
    pressureSubBudgetClosed ≡ true →
    ⊥

  nsPressureLocalizationSubBudgetCompositeDoesNotProveLocalization :
    localizationTheoremProved ≡ true →
    ⊥

  nsPressureLocalizationSubBudgetCompositeDoesNotProveTriadicLeakage :
    triadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  nsPressureLocalizationSubBudgetCompositeDoesNotProveResidualNonPositive :
    residualNonPositiveProved ≡ true →
    ⊥

  nsPressureLocalizationSubBudgetCompositeDoesNotPromoteNSClay :
    nsClayPromoted ≡ true →
    ⊥

  nsPressureLocalizationSubBudgetCompositeDoesNotPromoteTerminal :
    terminalPromotion ≡ true →
    ⊥
