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

shellLocalizationImported : Bool
shellLocalizationImported =
  true

pointwiseToAbelCompositeImported : Bool
pointwiseToAbelCompositeImported =
  true

a6ErrorBudgetCompositeImported : Bool
a6ErrorBudgetCompositeImported =
  true

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
    shellLocalizationImportedIsTrue :
      shellLocalizationImported ≡ true
    pointwiseToAbelCompositeImportedIsTrue :
      pointwiseToAbelCompositeImported ≡ true
    a6ErrorBudgetCompositeImportedIsTrue :
      a6ErrorBudgetCompositeImported ≡ true

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
    ; shellLocalizationImportedIsTrue =
        refl
    ; pointwiseToAbelCompositeImportedIsTrue =
        refl
    ; a6ErrorBudgetCompositeImportedIsTrue =
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
  ∷ missingResidualDepletionAfterA6
  ∷ []

correctedA6RepairBlockerCount : Nat
correctedA6RepairBlockerCount =
  listLength canonicalCorrectedA6RepairBlockers

correctedA6RepairBlockerCountIs6 :
  correctedA6RepairBlockerCount ≡ 6
correctedA6RepairBlockerCountIs6 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

orcsLpgfSummary : String
orcsLpgfSummary =
  "O Worker C A6.2 repair boundary; R record that naive same-shell Biot-Savart localization is non-promoting and replace it with Bony paraproduct/resonant/high-frequency routing; C fail-closed Agda module importing shell-localization, pointwise-to-Abel composite, and A6 error-budget receipts; S corrected split is recorded but theorem proofs remain open; L failed naive route < corrected Bony target < A6 assembly < residual depletion < NS Clay; P prove paraproduct, finite resonant shell, and high-frequency tail estimates before A6 promotion; G no docs edited and no Clay/terminal promotion; F A6, residual depletion, local monotonicity, and NS Clay remain unproved."

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
    blockers :
      List CorrectedA6RepairBlocker
    blockerCountProof :
      correctedA6RepairBlockerCount ≡ 6
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
    summary :
      String
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
    ; summary =
        orcsLpgfSummary
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
