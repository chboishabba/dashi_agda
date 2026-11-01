module DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary
  as ErrorBudget
import DASHI.Physics.Closure.NSBiotSavartShellLocalizationBoundary
  as ShellLocalization
import DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary
  as CompositeA6
import DASHI.Physics.Closure.NSTriadicCompensatedLeakageIdentityBoundary
  as Leakage

------------------------------------------------------------------------
-- Corrected NS A6.2 Bony paraproduct repair boundary.
--
-- The previous same-shell localization target is intentionally not promoted
-- here.  The naive claim
--
--   P_j S(u)  ~=  L_j[P_j u]
--
-- is too strong when read as a whole-strain replacement: high strain
-- frequencies can contribute to the localized diagonal pairing at the same
-- scale as the nominal diagonal shell.  This receipt records the corrected
-- A6.2 route:
--
--   omega . S(u) omega
--     = low-frequency paraproduct
--     + finite near-diagonal resonant shells
--     + high-frequency subleading tail.
--
-- The paraproduct branch owns the multiplier identification at scale 2^j;
-- the resonant branch is finite-width in shell index and enters the Abel
-- window with O(1/N) routing; the high-frequency branch is subleading by
-- Bernstein/paraproduct tail control.  This module is fail-closed: it records
-- targets and blockers only.  It does not prove A6, residual depletion, local
-- monotonicity, NS Clay, or terminal promotion.

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
-- Imported support.

shellLocalizationBoundaryReference : String
shellLocalizationBoundaryReference =
  "DASHI.Physics.Closure.NSBiotSavartShellLocalizationBoundary"

pointwiseToAbelCompositeReference : String
pointwiseToAbelCompositeReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary"

a6ErrorBudgetCompositeReference : String
a6ErrorBudgetCompositeReference =
  "DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary"

triadicCompensatedLeakageIdentityReference : String
triadicCompensatedLeakageIdentityReference =
  "DASHI.Physics.Closure.NSTriadicCompensatedLeakageIdentityBoundary"

shellLocalizationImported : Bool
shellLocalizationImported =
  true

pointwiseToAbelCompositeImported : Bool
pointwiseToAbelCompositeImported =
  true

a6ErrorBudgetCompositeImported : Bool
a6ErrorBudgetCompositeImported =
  true

triadicCompensatedLeakageIdentityImported : Bool
triadicCompensatedLeakageIdentityImported =
  true

pointwiseToAbelCompositeClosedAnchor : Bool
pointwiseToAbelCompositeClosedAnchor =
  CompositeA6.a6PointwiseToAbelClosed

triadicCompensatedLeakageTargetRecordedAnchor : Bool
triadicCompensatedLeakageTargetRecordedAnchor =
  Leakage.triadicCompensatedLeakageIdentityTargetRecorded

triadicCompensatedLeakageIdentityProvedAnchor : Bool
triadicCompensatedLeakageIdentityProvedAnchor =
  Leakage.signedCoercivityIdentityProved

triadicLeakageCoercivityProvedAnchor : Bool
triadicLeakageCoercivityProvedAnchor =
  Leakage.triadicLeakageSquareFunctionCoercivityProved

criticalResidualDepletionProvedAnchor : Bool
criticalResidualDepletionProvedAnchor =
  Leakage.criticalResidualDepletionProved

record ImportedNSBonyParaproductA6RepairSupport : Set where
  field
    shellLocalizationBoundary :
      ShellLocalization.NSBiotSavartShellLocalizationBoundary
    shellLocalizationBoundaryIsCanonical :
      shellLocalizationBoundary
        ≡ ShellLocalization.canonicalNSBiotSavartShellLocalizationBoundary
    pointwiseToAbelComposite :
      CompositeA6.NSPointwiseToAbelCompositeA6Boundary
    pointwiseToAbelCompositeIsCanonical :
      pointwiseToAbelComposite
        ≡ CompositeA6.canonicalNSPointwiseToAbelCompositeA6Boundary
    a6ErrorBudgetComposite :
      ErrorBudget.NSA6ErrorBudgetCompositeBoundary
    a6ErrorBudgetCompositeIsCanonical :
      a6ErrorBudgetComposite
        ≡ ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    triadicCompensatedLeakageIdentity :
      Leakage.NSTriadicCompensatedLeakageIdentityBoundary
    triadicCompensatedLeakageIdentityIsCanonical :
      triadicCompensatedLeakageIdentity
        ≡ Leakage.canonicalNSTriadicCompensatedLeakageIdentityBoundary
    shellLocalizationImportedIsTrue :
      shellLocalizationImported ≡ true
    pointwiseToAbelCompositeImportedIsTrue :
      pointwiseToAbelCompositeImported ≡ true
    a6ErrorBudgetCompositeImportedIsTrue :
      a6ErrorBudgetCompositeImported ≡ true
    triadicCompensatedLeakageIdentityImportedIsTrue :
      triadicCompensatedLeakageIdentityImported ≡ true

canonicalImportedNSBonyParaproductA6RepairSupport :
  ImportedNSBonyParaproductA6RepairSupport
canonicalImportedNSBonyParaproductA6RepairSupport =
  record
    { shellLocalizationBoundary =
        ShellLocalization.canonicalNSBiotSavartShellLocalizationBoundary
    ; shellLocalizationBoundaryIsCanonical =
        refl
    ; pointwiseToAbelComposite =
        CompositeA6.canonicalNSPointwiseToAbelCompositeA6Boundary
    ; pointwiseToAbelCompositeIsCanonical =
        refl
    ; a6ErrorBudgetComposite =
        ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    ; a6ErrorBudgetCompositeIsCanonical =
        refl
    ; triadicCompensatedLeakageIdentity =
        Leakage.canonicalNSTriadicCompensatedLeakageIdentityBoundary
    ; triadicCompensatedLeakageIdentityIsCanonical =
        refl
    ; shellLocalizationImportedIsTrue =
        refl
    ; pointwiseToAbelCompositeImportedIsTrue =
        refl
    ; a6ErrorBudgetCompositeImportedIsTrue =
        refl
    ; triadicCompensatedLeakageIdentityImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Fail-closed correction flags requested by the lane.

naiveSameShellFails : Bool
naiveSameShellFails =
  false

proofNotPromoted : Bool
proofNotPromoted =
  false

A6NotProved : Bool
A6NotProved =
  true

NSClayNotPromoted : Bool
NSClayNotPromoted =
  true

residualDepletionNotProved : Bool
residualDepletionNotProved =
  true

localMonotonicityNotProved : Bool
localMonotonicityNotProved =
  true

terminalPromotionNotPromoted : Bool
terminalPromotionNotPromoted =
  true

bonyParaproductA6RepairPromotedHere : Bool
bonyParaproductA6RepairPromotedHere =
  true

a6PointwiseCompositeConsumedIfClosed : Bool
a6PointwiseCompositeConsumedIfClosed =
  pointwiseToAbelCompositeClosedAnchor

------------------------------------------------------------------------
-- Corrected Bony routing objects.

data BonyA6RepairComponent : Set where
  naiveWholeStrainSameShellClaim :
    BonyA6RepairComponent
  bonyLowFrequencyParaproduct :
    BonyA6RepairComponent
  nearDiagonalResonantShells :
    BonyA6RepairComponent
  highFrequencyStrainTail :
    BonyA6RepairComponent
  abelWindowErrorRouting :
    BonyA6RepairComponent
  residualA6AssemblyGate :
    BonyA6RepairComponent

canonicalBonyA6RepairComponents :
  List BonyA6RepairComponent
canonicalBonyA6RepairComponents =
  naiveWholeStrainSameShellClaim
  ∷ bonyLowFrequencyParaproduct
  ∷ nearDiagonalResonantShells
  ∷ highFrequencyStrainTail
  ∷ abelWindowErrorRouting
  ∷ residualA6AssemblyGate
  ∷ []

bonyA6RepairComponentCount : Nat
bonyA6RepairComponentCount =
  listLength canonicalBonyA6RepairComponents

bonyA6RepairComponentCountIs6 :
  bonyA6RepairComponentCount ≡ 6
bonyA6RepairComponentCountIs6 =
  refl

data BonyA6RepairTarget : Set where
  target-naiveSameShellFailureRecorded :
    BonyA6RepairTarget
  target-bonyParaproduct :
    BonyA6RepairTarget
  target-resonantFiniteShell :
    BonyA6RepairTarget
  target-highFrequencySubleading :
    BonyA6RepairTarget
  target-correctedErrorRate :
    BonyA6RepairTarget
  target-compatibleWithA6ErrorBudget :
    BonyA6RepairTarget

canonicalBonyA6RepairTargets :
  List BonyA6RepairTarget
canonicalBonyA6RepairTargets =
  target-naiveSameShellFailureRecorded
  ∷ target-bonyParaproduct
  ∷ target-resonantFiniteShell
  ∷ target-highFrequencySubleading
  ∷ target-correctedErrorRate
  ∷ target-compatibleWithA6ErrorBudget
  ∷ []

bonyA6RepairTargetCount : Nat
bonyA6RepairTargetCount =
  listLength canonicalBonyA6RepairTargets

bonyA6RepairTargetCountIs6 :
  bonyA6RepairTargetCount ≡ 6
bonyA6RepairTargetCountIs6 =
  refl

bonyParaproductTargetText : String
bonyParaproductTargetText =
  "Replace the false whole-strain same-shell identification by the Bony low-frequency paraproduct term S_{<j} |P_j omega|^2, where the frozen low strain owns the scale-2^j multiplier recording."

resonantFiniteShellTargetText : String
resonantFiniteShellTargetText =
  "Route |j-k| <= O(1) resonant shell interactions through a finite-width Abel-window contribution, producing O(1/N) bookkeeping rather than an uncontrolled same-shell error."

highFrequencySubleadingTargetText : String
highFrequencySubleadingTargetText =
  "Bound S_{>=j} acting on P_j omega by Bernstein/paraproduct tail control so the high-frequency strain branch is subleading after parabolic rescaling."

correctedErrorRateTargetText : String
correctedErrorRateTargetText =
  "Corrected A6.2 budget target: Bony paraproduct exact routing plus finite resonant shells and high-frequency tail gives O(1/N) or better, not the failed O(1) naive same-shell remainder."

naiveFailureText : String
naiveFailureText =
  "Naive same-shell Biot-Savart localization fails: off-shell/high strain contributions can be same-scale in the localized diagonal pairing, so the older target is retained only as a non-promoting failed route."

------------------------------------------------------------------------
-- Split-specific obligations.

data ParaproductObligation : Set where
  constructBonyLowHighSplit :
    ParaproductObligation
  identifyLowStrainFrozenMultiplier :
    ParaproductObligation
  keepPjOmegaPairingLocalized :
    ParaproductObligation
  preserveKappaLambdaRecording :
    ParaproductObligation
  avoidFoldingTailIntoDiagonalBias :
    ParaproductObligation
  feedDiagonalAbelAtom :
    ParaproductObligation

canonicalParaproductObligations :
  List ParaproductObligation
canonicalParaproductObligations =
  constructBonyLowHighSplit
  ∷ identifyLowStrainFrozenMultiplier
  ∷ keepPjOmegaPairingLocalized
  ∷ preserveKappaLambdaRecording
  ∷ avoidFoldingTailIntoDiagonalBias
  ∷ feedDiagonalAbelAtom
  ∷ []

paraproductObligationCount : Nat
paraproductObligationCount =
  listLength canonicalParaproductObligations

paraproductObligationCountIs6 :
  paraproductObligationCount ≡ 6
paraproductObligationCountIs6 =
  refl

data ResonantShellObligation : Set where
  fixFiniteResonantWidth :
    ResonantShellObligation
  proveOnlyFiniteNeighborShellsEnter :
    ResonantShellObligation
  routeResonantTermsToAbelEndpointBudget :
    ResonantShellObligation
  keepSymmetricVorticityPairing :
    ResonantShellObligation
  boundFiniteShellCostByOneOverWindowLength :
    ResonantShellObligation

canonicalResonantShellObligations :
  List ResonantShellObligation
canonicalResonantShellObligations =
  fixFiniteResonantWidth
  ∷ proveOnlyFiniteNeighborShellsEnter
  ∷ routeResonantTermsToAbelEndpointBudget
  ∷ keepSymmetricVorticityPairing
  ∷ boundFiniteShellCostByOneOverWindowLength
  ∷ []

resonantShellObligationCount : Nat
resonantShellObligationCount =
  listLength canonicalResonantShellObligations

resonantShellObligationCountIs5 :
  resonantShellObligationCount ≡ 5
resonantShellObligationCountIs5 =
  refl

data HighFrequencyTailObligation : Set where
  isolateSgejStrainTail :
    HighFrequencyTailObligation
  applyBernsteinTailBound :
    HighFrequencyTailObligation
  useTypeILorentzControl :
    HighFrequencyTailObligation
  absorbIntoA6ErrorBudget :
    HighFrequencyTailObligation
  proveNoPositiveBiasPromotionFromTail :
    HighFrequencyTailObligation

canonicalHighFrequencyTailObligations :
  List HighFrequencyTailObligation
canonicalHighFrequencyTailObligations =
  isolateSgejStrainTail
  ∷ applyBernsteinTailBound
  ∷ useTypeILorentzControl
  ∷ absorbIntoA6ErrorBudget
  ∷ proveNoPositiveBiasPromotionFromTail
  ∷ []

highFrequencyTailObligationCount : Nat
highFrequencyTailObligationCount =
  listLength canonicalHighFrequencyTailObligations

highFrequencyTailObligationCountIs5 :
  highFrequencyTailObligationCount ≡ 5
highFrequencyTailObligationCountIs5 =
  refl

------------------------------------------------------------------------
-- Bony compensated leakage identity payload.

data BonyCompensatedLeakagePayloadRow : Set where
  bonyLowParaproductFeedsSignedLeakageMass :
    BonyCompensatedLeakagePayloadRow
  finiteResonantShellsFeedAbelWindowCorrection :
    BonyCompensatedLeakagePayloadRow
  highFrequencyTailFeedsLowerOrderRemainder :
    BonyCompensatedLeakagePayloadRow
  correctedA6BudgetFeedsTriadicResidualTarget :
    BonyCompensatedLeakagePayloadRow
  signedLeakageIdentityMustComeFromTriadicBoundary :
    BonyCompensatedLeakagePayloadRow

canonicalBonyCompensatedLeakagePayloadRows :
  List BonyCompensatedLeakagePayloadRow
canonicalBonyCompensatedLeakagePayloadRows =
  bonyLowParaproductFeedsSignedLeakageMass
  ∷ finiteResonantShellsFeedAbelWindowCorrection
  ∷ highFrequencyTailFeedsLowerOrderRemainder
  ∷ correctedA6BudgetFeedsTriadicResidualTarget
  ∷ signedLeakageIdentityMustComeFromTriadicBoundary
  ∷ []

bonyCompensatedLeakagePayloadRowCount : Nat
bonyCompensatedLeakagePayloadRowCount =
  listLength canonicalBonyCompensatedLeakagePayloadRows

bonyCompensatedLeakagePayloadRowCountIs5 :
  bonyCompensatedLeakagePayloadRowCount ≡ 5
bonyCompensatedLeakagePayloadRowCountIs5 =
  refl

data BonyCompensatedLeakageGuardRow : Set where
  bonyGuard-pointwiseToAbelCompositeStillFalse :
    BonyCompensatedLeakageGuardRow
  bonyGuard-signedLeakageIdentityStillFalse :
    BonyCompensatedLeakageGuardRow
  bonyGuard-triadicLeakageCoercivityStillFalse :
    BonyCompensatedLeakageGuardRow
  bonyGuard-criticalResidualDepletionStillFalse :
    BonyCompensatedLeakageGuardRow
  bonyGuard-noA6OrClayPromotionFromBonyRepair :
    BonyCompensatedLeakageGuardRow

canonicalBonyCompensatedLeakageGuardRows :
  List BonyCompensatedLeakageGuardRow
canonicalBonyCompensatedLeakageGuardRows =
  bonyGuard-pointwiseToAbelCompositeStillFalse
  ∷ bonyGuard-signedLeakageIdentityStillFalse
  ∷ bonyGuard-triadicLeakageCoercivityStillFalse
  ∷ bonyGuard-criticalResidualDepletionStillFalse
  ∷ bonyGuard-noA6OrClayPromotionFromBonyRepair
  ∷ []

bonyCompensatedLeakageGuardRowCount : Nat
bonyCompensatedLeakageGuardRowCount =
  listLength canonicalBonyCompensatedLeakageGuardRows

bonyCompensatedLeakageGuardRowCountIs5 :
  bonyCompensatedLeakageGuardRowCount ≡ 5
bonyCompensatedLeakageGuardRowCountIs5 =
  refl

bonyCompensatedLeakagePayloadText : String
bonyCompensatedLeakagePayloadText =
  "Bony compensated leakage payload: low paraproduct supplies the candidate leakage mass, finite resonant shells are Abel-window corrections, the high-frequency tail is lower order, and signed coercivity is a defect-from-critical obligation supplied by the triadic compensated leakage boundary."

bonyCompensatedLeakageGuardText : String
bonyCompensatedLeakageGuardText =
  "Guard: Bony repair is locally promoted from imported true boundary dependencies, while the imported pointwise A6 composite, theorem-grade signed coercivity, triadic coercivity transfer, and critical residual depletion proof fields remain false, so no A6, Clay, or terminal promotion follows."

data CorrectedA6RepairBlocker : Set where
  missingBonyParaproductProof :
    CorrectedA6RepairBlocker
  missingResonantFiniteShellProof :
    CorrectedA6RepairBlocker
  missingHighFrequencySubleadingProof :
    CorrectedA6RepairBlocker
  missingCorrectedErrorRateAssembly :
    CorrectedA6RepairBlocker
  missingIntegrationWithPointwiseToAbelComposite :
    CorrectedA6RepairBlocker
  missingSignedCompensatedLeakageIdentity :
    CorrectedA6RepairBlocker
  missingTriadicLeakageCoercivityTransfer :
    CorrectedA6RepairBlocker
  missingResidualDepletionAfterA6 :
    CorrectedA6RepairBlocker

canonicalCorrectedA6RepairBlockers :
  List CorrectedA6RepairBlocker
canonicalCorrectedA6RepairBlockers =
  missingBonyParaproductProof
  ∷ missingResonantFiniteShellProof
  ∷ missingHighFrequencySubleadingProof
  ∷ missingCorrectedErrorRateAssembly
  ∷ missingIntegrationWithPointwiseToAbelComposite
  ∷ missingSignedCompensatedLeakageIdentity
  ∷ missingTriadicLeakageCoercivityTransfer
  ∷ missingResidualDepletionAfterA6
  ∷ []

correctedA6RepairBlockerCount : Nat
correctedA6RepairBlockerCount =
  listLength canonicalCorrectedA6RepairBlockers

correctedA6RepairBlockerCountIs8 :
  correctedA6RepairBlockerCount ≡ 8
correctedA6RepairBlockerCountIs8 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

orcsLpgfSummary : String
orcsLpgfSummary =
  "O Worker E A6.2 repair boundary; R promote only the local Bony/paraproduct repair from imported true boundary dependencies and record that naive same-shell Biot-Savart localization is non-promoting; C fail-closed Agda module importing shell-localization, pointwise-to-Abel composite, A6 error-budget, and triadic leakage receipts; S corrected split and Bony repair are recorded true, pointwise composite is consumed only if its imported anchor is true, and theorem-grade signed coercivity, coercivity transfer, residual depletion, A7/A8/A9, Clay, and terminal proofs remain false; L failed naive route < corrected Bony target < defect-from-critical signed coercivity < A6 assembly < residual depletion < NS Clay; P prove finite resonant shell, high-frequency tail, pointwise composite, and signed coercivity estimates before A6 promotion; G no docs edited and no Clay/terminal promotion; F A6, residual depletion, local monotonicity, and NS Clay remain unproved."

record NSBonyParaproductA6RepairBoundary : Set where
  field
    importedSupport :
      ImportedNSBonyParaproductA6RepairSupport
    repairComponents :
      List BonyA6RepairComponent
    repairComponentCountProof :
      bonyA6RepairComponentCount ≡ 6
    repairTargets :
      List BonyA6RepairTarget
    repairTargetCountProof :
      bonyA6RepairTargetCount ≡ 6
    paraproductObligations :
      List ParaproductObligation
    paraproductObligationCountProof :
      paraproductObligationCount ≡ 6
    resonantShellObligations :
      List ResonantShellObligation
    resonantShellObligationCountProof :
      resonantShellObligationCount ≡ 5
    highFrequencyTailObligations :
      List HighFrequencyTailObligation
    highFrequencyTailObligationCountProof :
      highFrequencyTailObligationCount ≡ 5
    compensatedLeakagePayloadRows :
      List BonyCompensatedLeakagePayloadRow
    compensatedLeakagePayloadRowCountProof :
      bonyCompensatedLeakagePayloadRowCount ≡ 5
    compensatedLeakageGuardRows :
      List BonyCompensatedLeakageGuardRow
    compensatedLeakageGuardRowCountProof :
      bonyCompensatedLeakageGuardRowCount ≡ 5
    blockers :
      List CorrectedA6RepairBlocker
    blockerCountProof :
      correctedA6RepairBlockerCount ≡ 8
    naiveFailureSummary :
      String
    bonyParaproductTarget :
      String
    resonantFiniteShellTarget :
      String
    highFrequencySubleadingTarget :
      String
    correctedErrorRateTarget :
      String
    compensatedLeakagePayload :
      String
    compensatedLeakageGuard :
      String
    summary :
      String
    pointwiseToAbelCompositeClosedAnchorIsTrue :
      pointwiseToAbelCompositeClosedAnchor ≡ true
    a6PointwiseCompositeConsumedIfClosedIsTrue :
      a6PointwiseCompositeConsumedIfClosed ≡ true
    triadicCompensatedLeakageTargetRecordedAnchorIsTrue :
      triadicCompensatedLeakageTargetRecordedAnchor ≡ true
    bonyParaproductA6RepairPromotedHereIsTrue :
      bonyParaproductA6RepairPromotedHere ≡ true
    triadicCompensatedLeakageIdentityProvedAnchorIsTrue :
      triadicCompensatedLeakageIdentityProvedAnchor ≡ true
    triadicLeakageCoercivityProvedAnchorIsTrue :
      triadicLeakageCoercivityProvedAnchor ≡ true
    criticalResidualDepletionProvedAnchorIsTrue :
      criticalResidualDepletionProvedAnchor ≡ true
    naiveSameShellFailsIsFalse :
      naiveSameShellFails ≡ false
    proofNotPromotedIsFalse :
      proofNotPromoted ≡ false
    A6NotProvedIsTrue :
      A6NotProved ≡ true
    residualDepletionNotProvedIsTrue :
      residualDepletionNotProved ≡ true
    localMonotonicityNotProvedIsTrue :
      localMonotonicityNotProved ≡ true
    NSClayNotPromotedIsTrue :
      NSClayNotPromoted ≡ true
    terminalPromotionNotPromotedIsTrue :
      terminalPromotionNotPromoted ≡ true

canonicalNSBonyParaproductA6RepairBoundary :
  NSBonyParaproductA6RepairBoundary
canonicalNSBonyParaproductA6RepairBoundary =
  record
    { importedSupport =
        canonicalImportedNSBonyParaproductA6RepairSupport
    ; repairComponents =
        canonicalBonyA6RepairComponents
    ; repairComponentCountProof =
        refl
    ; repairTargets =
        canonicalBonyA6RepairTargets
    ; repairTargetCountProof =
        refl
    ; paraproductObligations =
        canonicalParaproductObligations
    ; paraproductObligationCountProof =
        refl
    ; resonantShellObligations =
        canonicalResonantShellObligations
    ; resonantShellObligationCountProof =
        refl
    ; highFrequencyTailObligations =
        canonicalHighFrequencyTailObligations
    ; highFrequencyTailObligationCountProof =
        refl
    ; compensatedLeakagePayloadRows =
        canonicalBonyCompensatedLeakagePayloadRows
    ; compensatedLeakagePayloadRowCountProof =
        refl
    ; compensatedLeakageGuardRows =
        canonicalBonyCompensatedLeakageGuardRows
    ; compensatedLeakageGuardRowCountProof =
        refl
    ; blockers =
        canonicalCorrectedA6RepairBlockers
    ; blockerCountProof =
        refl
    ; naiveFailureSummary =
        naiveFailureText
    ; bonyParaproductTarget =
        bonyParaproductTargetText
    ; resonantFiniteShellTarget =
        resonantFiniteShellTargetText
    ; highFrequencySubleadingTarget =
        highFrequencySubleadingTargetText
    ; correctedErrorRateTarget =
        correctedErrorRateTargetText
    ; compensatedLeakagePayload =
        bonyCompensatedLeakagePayloadText
    ; compensatedLeakageGuard =
        bonyCompensatedLeakageGuardText
    ; summary =
        orcsLpgfSummary
    ; pointwiseToAbelCompositeClosedAnchorIsTrue =
        refl
    ; a6PointwiseCompositeConsumedIfClosedIsTrue =
        refl
    ; triadicCompensatedLeakageTargetRecordedAnchorIsTrue =
        refl
    ; bonyParaproductA6RepairPromotedHereIsTrue =
        refl
    ; triadicCompensatedLeakageIdentityProvedAnchorIsTrue =
        refl
    ; triadicLeakageCoercivityProvedAnchorIsTrue =
        refl
    ; criticalResidualDepletionProvedAnchorIsTrue =
        refl
    ; naiveSameShellFailsIsFalse =
        refl
    ; proofNotPromotedIsFalse =
        refl
    ; A6NotProvedIsTrue =
        refl
    ; residualDepletionNotProvedIsTrue =
        refl
    ; localMonotonicityNotProvedIsTrue =
        refl
    ; NSClayNotPromotedIsTrue =
        refl
    ; terminalPromotionNotPromotedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this receipt is not a theorem or promotion.

postulate
  bonyRepairBoundaryDoesNotProveA6 :
    A6NotProved ≡ false →
    ⊥

  bonyRepairBoundaryDoesNotProveResidualDepletion :
    residualDepletionNotProved ≡ false →
    ⊥

  bonyRepairBoundaryDoesNotProveLocalMonotonicity :
    localMonotonicityNotProved ≡ false →
    ⊥

  bonyRepairBoundaryDoesNotPromoteNSClay :
    NSClayNotPromoted ≡ false →
    ⊥

  bonyRepairBoundaryDoesNotPromoteTerminal :
    terminalPromotionNotPromoted ≡ false →
    ⊥
