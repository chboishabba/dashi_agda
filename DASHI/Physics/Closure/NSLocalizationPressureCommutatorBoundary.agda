module DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary
  as OffDiagonal
import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as PointwiseToAbel

------------------------------------------------------------------------
-- NS A6 localization / pressure commutator boundary.
--
-- This module is a narrow fail-closed child boundary under
-- NSPointwiseToAbelAveragingBoundary.  It records the analytic controls
-- needed to replace the localized pointwise stretching density
--
--   omega . S omega
--
-- by an Abel/shell mean when cutoff localization, Leray pressure
-- reconstruction, pressure commutators, boundary/cutoff defects, and
-- pressure tails are present.
--
-- The receipt deliberately does not prove the localized cutoff theorem,
-- does not prove the Leray pressure commutator theorem, does not prove A6,
-- does not prove residual depletion, does not prove NS Clay, and does not
-- promote a terminal claim.

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
-- Imported parent and sibling support anchors.

pointwiseToAbelBoundaryReference : String
pointwiseToAbelBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

offDiagonalAbsorptionBoundaryReference : String
offDiagonalAbsorptionBoundaryReference =
  "DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary"

pointwiseToAbelBoundaryImported : Bool
pointwiseToAbelBoundaryImported =
  true

offDiagonalAbsorptionBoundaryImported : Bool
offDiagonalAbsorptionBoundaryImported =
  true

record ImportedLocalizationPressureCommutatorSupport : Set where
  field
    pointwiseToAbelBoundary :
      PointwiseToAbel.NSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    offDiagonalAbsorptionBoundary :
      OffDiagonal.NSOffDiagonalShellAbsorptionBoundary
    offDiagonalAbsorptionBoundaryIsCanonical :
      offDiagonalAbsorptionBoundary
        ≡ OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    pointwiseToAbelBoundaryImportedIsTrue :
      pointwiseToAbelBoundaryImported ≡ true
    offDiagonalAbsorptionBoundaryImportedIsTrue :
      offDiagonalAbsorptionBoundaryImported ≡ true

canonicalImportedLocalizationPressureCommutatorSupport :
  ImportedLocalizationPressureCommutatorSupport
canonicalImportedLocalizationPressureCommutatorSupport =
  record
    { pointwiseToAbelBoundary =
        PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; offDiagonalAbsorptionBoundary =
        OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    ; offDiagonalAbsorptionBoundaryIsCanonical =
        refl
    ; pointwiseToAbelBoundaryImportedIsTrue =
        refl
    ; offDiagonalAbsorptionBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Localized cutoff objects.

data LocalizedCutoffObject : Set where
  parabolicCylinder-Qr :
    LocalizedCutoffObject
  spatialCutoff-phi-r :
    LocalizedCutoffObject
  timeCutoff-eta-r :
    LocalizedCutoffObject
  cutoffGradient-rMinusOne :
    LocalizedCutoffObject
  cutoffLaplacian-rMinusTwo :
    LocalizedCutoffObject
  dyadicShellProjection-Pj :
    LocalizedCutoffObject
  localizedVorticityShell-PjOmegaPhi :
    LocalizedCutoffObject
  localizedPressurePotential-pPhi :
    LocalizedCutoffObject
  exteriorTailAnnulus-QtwoRMinusQr :
    LocalizedCutoffObject

canonicalLocalizedCutoffObjects : List LocalizedCutoffObject
canonicalLocalizedCutoffObjects =
  parabolicCylinder-Qr
  ∷ spatialCutoff-phi-r
  ∷ timeCutoff-eta-r
  ∷ cutoffGradient-rMinusOne
  ∷ cutoffLaplacian-rMinusTwo
  ∷ dyadicShellProjection-Pj
  ∷ localizedVorticityShell-PjOmegaPhi
  ∷ localizedPressurePotential-pPhi
  ∷ exteriorTailAnnulus-QtwoRMinusQr
  ∷ []

localizedCutoffObjectCount : Nat
localizedCutoffObjectCount =
  listLength canonicalLocalizedCutoffObjects

localizedCutoffObjectCountIs9 :
  localizedCutoffObjectCount ≡ 9
localizedCutoffObjectCountIs9 =
  refl

localizedCutoffTheoremTargetText : String
localizedCutoffTheoremTargetText =
  "Localized cutoff theorem: cutoff, shell projection, and parabolic localization errors are lower-order or epsilon-absorbed before omega.Somega is replaced by the Abel/shell mean"

data LocalizedCutoffRequirement : Set where
  cutoffEqualsOneOnCoreQr :
    LocalizedCutoffRequirement
  derivativesScaleAtParabolicRate :
    LocalizedCutoffRequirement
  dyadicProjectionCutoffCommutatorBounded :
    LocalizedCutoffRequirement
  derivativeOnCutoffGivesLowerOrderEnergy :
    LocalizedCutoffRequirement
  timeCutoffErrorFeedsLocalEnergy :
    LocalizedCutoffRequirement
  cutoffDoesNotDistortAbelShellWeights :
    LocalizedCutoffRequirement
  boundaryAnnulusRecordedAsTailNotCore :
    LocalizedCutoffRequirement
  noPointwiseSignClaimAfterLocalization :
    LocalizedCutoffRequirement

canonicalLocalizedCutoffRequirements :
  List LocalizedCutoffRequirement
canonicalLocalizedCutoffRequirements =
  cutoffEqualsOneOnCoreQr
  ∷ derivativesScaleAtParabolicRate
  ∷ dyadicProjectionCutoffCommutatorBounded
  ∷ derivativeOnCutoffGivesLowerOrderEnergy
  ∷ timeCutoffErrorFeedsLocalEnergy
  ∷ cutoffDoesNotDistortAbelShellWeights
  ∷ boundaryAnnulusRecordedAsTailNotCore
  ∷ noPointwiseSignClaimAfterLocalization
  ∷ []

localizedCutoffRequirementCount : Nat
localizedCutoffRequirementCount =
  listLength canonicalLocalizedCutoffRequirements

localizedCutoffRequirementCountIs8 :
  localizedCutoffRequirementCount ≡ 8
localizedCutoffRequirementCountIs8 =
  refl

------------------------------------------------------------------------
-- Leray pressure reconstruction and commutator taxonomy.

data LerayPressureReconstructionStep : Set where
  reconstructPressureByRieszRieszOfUiUj :
    LerayPressureReconstructionStep
  splitLocalPressureIntoCoreAndHarmonicTail :
    LerayPressureReconstructionStep
  commuteLerayProjectionPastCutoff :
    LerayPressureReconstructionStep
  commuteDyadicProjectionPastPressureKernel :
    LerayPressureReconstructionStep
  recordGradientPressureAsDivergenceError :
    LerayPressureReconstructionStep
  applyCalderonZygmundLocalEstimate :
    LerayPressureReconstructionStep
  subtractAveragesOnLocalizedCylinder :
    LerayPressureReconstructionStep
  sendExteriorKernelToPressureTailBudget :
    LerayPressureReconstructionStep

canonicalLerayPressureReconstructionSteps :
  List LerayPressureReconstructionStep
canonicalLerayPressureReconstructionSteps =
  reconstructPressureByRieszRieszOfUiUj
  ∷ splitLocalPressureIntoCoreAndHarmonicTail
  ∷ commuteLerayProjectionPastCutoff
  ∷ commuteDyadicProjectionPastPressureKernel
  ∷ recordGradientPressureAsDivergenceError
  ∷ applyCalderonZygmundLocalEstimate
  ∷ subtractAveragesOnLocalizedCylinder
  ∷ sendExteriorKernelToPressureTailBudget
  ∷ []

lerayPressureReconstructionStepCount : Nat
lerayPressureReconstructionStepCount =
  listLength canonicalLerayPressureReconstructionSteps

lerayPressureReconstructionStepCountIs8 :
  lerayPressureReconstructionStepCount ≡ 8
lerayPressureReconstructionStepCountIs8 =
  refl

pressureReconstructionTargetText : String
pressureReconstructionTargetText =
  "Pressure is reconstructed by the Leray/Riesz pressure formula, localized into core plus harmonic/exterior tails, and only then entered into the Abel replacement error budget"

data PressureCommutatorTerm : Set where
  commutator-LerayPhiMinusPhiLeray :
    PressureCommutatorTerm
  commutator-PjPhiMinusPhiPj :
    PressureCommutatorTerm
  commutator-RieszPhiMinusPhiRiesz :
    PressureCommutatorTerm
  pressureGradientTimesCutoffGradient :
    PressureCommutatorTerm
  harmonicPressureTail :
    PressureCommutatorTerm
  exteriorAnnularPressureTail :
    PressureCommutatorTerm
  shellOffWindowPressureTail :
    PressureCommutatorTerm
  timeCutoffPressureRemainder :
    PressureCommutatorTerm
  lowFrequencyPressureNormalization :
    PressureCommutatorTerm

canonicalPressureCommutatorTerms : List PressureCommutatorTerm
canonicalPressureCommutatorTerms =
  commutator-LerayPhiMinusPhiLeray
  ∷ commutator-PjPhiMinusPhiPj
  ∷ commutator-RieszPhiMinusPhiRiesz
  ∷ pressureGradientTimesCutoffGradient
  ∷ harmonicPressureTail
  ∷ exteriorAnnularPressureTail
  ∷ shellOffWindowPressureTail
  ∷ timeCutoffPressureRemainder
  ∷ lowFrequencyPressureNormalization
  ∷ []

pressureCommutatorTermCount : Nat
pressureCommutatorTermCount =
  listLength canonicalPressureCommutatorTerms

pressureCommutatorTermCountIs9 :
  pressureCommutatorTermCount ≡ 9
pressureCommutatorTermCountIs9 =
  refl

pressureCommutatorTheoremTargetText : String
pressureCommutatorTheoremTargetText =
  "Pressure commutator theorem: all Leray/Riesz/cutoff/shell pressure commutators are bounded by epsilon localized dissipation plus lower-order residual, Abel-window tail, and pressure-tail controls"

------------------------------------------------------------------------
-- Boundary, cutoff, and pressure-tail controls.

data BoundaryCutoffControl : Set where
  parabolicBoundaryTermsStayOnAnnulus :
    BoundaryCutoffControl
  annularFluxControlledByLocalEnergy :
    BoundaryCutoffControl
  cutoffDerivativeTermsDoNotEnterCoreMean :
    BoundaryCutoffControl
  shellRecenterDriftIsLowerOrder :
    BoundaryCutoffControl
  lowEnstrophyCoreCaseIsSeparate :
    BoundaryCutoffControl
  pressureAverageSubtractionIsRecorded :
    BoundaryCutoffControl
  harmonicTailHasInteriorDecay :
    BoundaryCutoffControl
  noBoundaryTermPromotesA6 :
    BoundaryCutoffControl

canonicalBoundaryCutoffControls : List BoundaryCutoffControl
canonicalBoundaryCutoffControls =
  parabolicBoundaryTermsStayOnAnnulus
  ∷ annularFluxControlledByLocalEnergy
  ∷ cutoffDerivativeTermsDoNotEnterCoreMean
  ∷ shellRecenterDriftIsLowerOrder
  ∷ lowEnstrophyCoreCaseIsSeparate
  ∷ pressureAverageSubtractionIsRecorded
  ∷ harmonicTailHasInteriorDecay
  ∷ noBoundaryTermPromotesA6
  ∷ []

boundaryCutoffControlCount : Nat
boundaryCutoffControlCount =
  listLength canonicalBoundaryCutoffControls

boundaryCutoffControlCountIs8 :
  boundaryCutoffControlCount ≡ 8
boundaryCutoffControlCountIs8 =
  refl

data PressureTailControl : Set where
  localCZPressureCoreBound :
    PressureTailControl
  pressureTailKernelDecayAcrossDyadicAnnuli :
    PressureTailControl
  harmonicPressureInteriorGradientBound :
    PressureTailControl
  shellSummableOffWindowPressureTail :
    PressureTailControl
  abelWindowPressureTailSummability :
    PressureTailControl
  pressureTailLowerOrderAgainstCriticalResidual :
    PressureTailControl
  epsilonDissipationAbsorptionForPressureGradient :
    PressureTailControl
  tailConstantIndependentOfShellCenter :
    PressureTailControl

canonicalPressureTailControls : List PressureTailControl
canonicalPressureTailControls =
  localCZPressureCoreBound
  ∷ pressureTailKernelDecayAcrossDyadicAnnuli
  ∷ harmonicPressureInteriorGradientBound
  ∷ shellSummableOffWindowPressureTail
  ∷ abelWindowPressureTailSummability
  ∷ pressureTailLowerOrderAgainstCriticalResidual
  ∷ epsilonDissipationAbsorptionForPressureGradient
  ∷ tailConstantIndependentOfShellCenter
  ∷ []

pressureTailControlCount : Nat
pressureTailControlCount =
  listLength canonicalPressureTailControls

pressureTailControlCountIs8 :
  pressureTailControlCount ≡ 8
pressureTailControlCountIs8 =
  refl

pressureTailControlText : String
pressureTailControlText =
  "Pressure tails are not discarded: core CZ, harmonic interior decay, exterior annuli, shell off-window terms, and Abel-window tails each have a named lower-order or epsilon-absorption target"

data AbelReplacementInterface : Set where
  startFromLocalizedEnstrophyStretchingSource :
    AbelReplacementInterface
  isolateCoreOmegaSOmegaBeforePressureTerms :
    AbelReplacementInterface
  removePressureAndCutoffDefectsFromCoreMean :
    AbelReplacementInterface
  passOnlyCoreShellWeightsToPointwiseToAbel :
    AbelReplacementInterface
  preserveDiagonalAndOffDiagonalLedgers :
    AbelReplacementInterface
  returnPressureCommutatorsAsErrorBudget :
    AbelReplacementInterface
  returnBoundaryCutoffTermsAsErrorBudget :
    AbelReplacementInterface
  replaceCoreOmegaSOmegaByAbelShellMeanOnlyAfterA6 :
    AbelReplacementInterface

canonicalAbelReplacementInterfaces : List AbelReplacementInterface
canonicalAbelReplacementInterfaces =
  startFromLocalizedEnstrophyStretchingSource
  ∷ isolateCoreOmegaSOmegaBeforePressureTerms
  ∷ removePressureAndCutoffDefectsFromCoreMean
  ∷ passOnlyCoreShellWeightsToPointwiseToAbel
  ∷ preserveDiagonalAndOffDiagonalLedgers
  ∷ returnPressureCommutatorsAsErrorBudget
  ∷ returnBoundaryCutoffTermsAsErrorBudget
  ∷ replaceCoreOmegaSOmegaByAbelShellMeanOnlyAfterA6
  ∷ []

abelReplacementInterfaceCount : Nat
abelReplacementInterfaceCount =
  listLength canonicalAbelReplacementInterfaces

abelReplacementInterfaceCountIs8 :
  abelReplacementInterfaceCount ≡ 8
abelReplacementInterfaceCountIs8 =
  refl

abelReplacementInterfaceText : String
abelReplacementInterfaceText =
  "This child boundary supplies the localization/pressure/cutoff error interface needed before the parent pointwise-to-Abel receipt may replace core omega.Somega by an Abel/shell mean"

------------------------------------------------------------------------
-- Blockers and fail-closed status flags.

data LocalizationPressureCommutatorBlocker : Set where
  missingLocalizedCutoffTheorem :
    LocalizationPressureCommutatorBlocker
  missingLerayPressureReconstructionProof :
    LocalizationPressureCommutatorBlocker
  missingPressureCommutatorTheorem :
    LocalizationPressureCommutatorBlocker
  missingBoundaryCutoffAbsorptionProof :
    LocalizationPressureCommutatorBlocker
  missingPressureTailSummabilityProof :
    LocalizationPressureCommutatorBlocker
  missingDyadicCutoffCommutatorEstimate :
    LocalizationPressureCommutatorBlocker
  missingCompatibilityWithAbelShellWeights :
    LocalizationPressureCommutatorBlocker
  missingIntegrationIntoPointwiseToAbelA6 :
    LocalizationPressureCommutatorBlocker
  missingResidualDepletionTransfer :
    LocalizationPressureCommutatorBlocker
  clayNavierStokesPromotionClosed :
    LocalizationPressureCommutatorBlocker

canonicalLocalizationPressureCommutatorBlockers :
  List LocalizationPressureCommutatorBlocker
canonicalLocalizationPressureCommutatorBlockers =
  missingLocalizedCutoffTheorem
  ∷ missingLerayPressureReconstructionProof
  ∷ missingPressureCommutatorTheorem
  ∷ missingBoundaryCutoffAbsorptionProof
  ∷ missingPressureTailSummabilityProof
  ∷ missingDyadicCutoffCommutatorEstimate
  ∷ missingCompatibilityWithAbelShellWeights
  ∷ missingIntegrationIntoPointwiseToAbelA6
  ∷ missingResidualDepletionTransfer
  ∷ clayNavierStokesPromotionClosed
  ∷ []

localizationPressureCommutatorBlockerCount : Nat
localizationPressureCommutatorBlockerCount =
  listLength canonicalLocalizationPressureCommutatorBlockers

localizationPressureCommutatorBlockerCountIs10 :
  localizationPressureCommutatorBlockerCount ≡ 10
localizationPressureCommutatorBlockerCountIs10 =
  refl

data NonClaimGuard : Set where
  noLocalizedCutoffTheoremClaim :
    NonClaimGuard
  noPressureCommutatorTheoremClaim :
    NonClaimGuard
  noPointwiseToAbelA6Claim :
    NonClaimGuard
  noResidualDepletionClaim :
    NonClaimGuard
  noLocalDefectMonotonicityClaim :
    NonClaimGuard
  noClayNavierStokesClaim :
    NonClaimGuard
  noTerminalPromotionClaim :
    NonClaimGuard

canonicalNonClaimGuards : List NonClaimGuard
canonicalNonClaimGuards =
  noLocalizedCutoffTheoremClaim
  ∷ noPressureCommutatorTheoremClaim
  ∷ noPointwiseToAbelA6Claim
  ∷ noResidualDepletionClaim
  ∷ noLocalDefectMonotonicityClaim
  ∷ noClayNavierStokesClaim
  ∷ noTerminalPromotionClaim
  ∷ []

nonClaimGuardCount : Nat
nonClaimGuardCount =
  listLength canonicalNonClaimGuards

nonClaimGuardCountIs7 :
  nonClaimGuardCount ≡ 7
nonClaimGuardCountIs7 =
  refl

boundaryRecorded : Bool
boundaryRecorded =
  true

importsRecorded : Bool
importsRecorded =
  true

localizedCutoffObjectsRecorded : Bool
localizedCutoffObjectsRecorded =
  true

lerayPressureReconstructionRecorded : Bool
lerayPressureReconstructionRecorded =
  true

pressureCommutatorTermsRecorded : Bool
pressureCommutatorTermsRecorded =
  true

boundaryCutoffControlsRecorded : Bool
boundaryCutoffControlsRecorded =
  true

pressureTailControlsRecorded : Bool
pressureTailControlsRecorded =
  true

abelReplacementInterfaceRecorded : Bool
abelReplacementInterfaceRecorded =
  true

localizedCutoffTheoremProved : Bool
localizedCutoffTheoremProved =
  false

lerayPressureReconstructionProved : Bool
lerayPressureReconstructionProved =
  false

pressureCommutatorTheoremProved : Bool
pressureCommutatorTheoremProved =
  false

pointwiseToAbelAveragingProved : Bool
pointwiseToAbelAveragingProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

residualDepletionProved : Bool
residualDepletionProved =
  false

fullLocalDefectMonotonicityProved : Bool
fullLocalDefectMonotonicityProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalUnificationPromoted : Bool
terminalUnificationPromoted =
  false

data NSLocalizationPressureCommutatorStatus : Set where
  localizationPressureCommutatorBoundaryRecorded_noPromotion :
    NSLocalizationPressureCommutatorStatus

------------------------------------------------------------------------
-- Compact O/R/C/S/L/P/G/F ledger.

data ORCSLPGFRow : Set where
  O-laneTwoNoetherLocalizationPressureChildBoundary :
    ORCSLPGFRow
  R-recordCutoffLerayCommutatorPressureTailControls :
    ORCSLPGFRow
  C-importsPointwiseToAbelAndOffDiagonalAbsorption :
    ORCSLPGFRow
  S-localizationPressureA6ResidualClayTerminalAllFalse :
    ORCSLPGFRow
  L-localizationPressureBoundaryFeedsPointwiseToAbelA6 :
    ORCSLPGFRow
  P-proveCutoffCommutatorLerayPressureTailAbsorption :
    ORCSLPGFRow
  G-noPromotionPastRecordedBoundary :
    ORCSLPGFRow
  F-gapLocalizedPressureCommutatorTheoremsRemainOpen :
    ORCSLPGFRow

canonicalORCSLPGFRows : List ORCSLPGFRow
canonicalORCSLPGFRows =
  O-laneTwoNoetherLocalizationPressureChildBoundary
  ∷ R-recordCutoffLerayCommutatorPressureTailControls
  ∷ C-importsPointwiseToAbelAndOffDiagonalAbsorption
  ∷ S-localizationPressureA6ResidualClayTerminalAllFalse
  ∷ L-localizationPressureBoundaryFeedsPointwiseToAbelA6
  ∷ P-proveCutoffCommutatorLerayPressureTailAbsorption
  ∷ G-noPromotionPastRecordedBoundary
  ∷ F-gapLocalizedPressureCommutatorTheoremsRemainOpen
  ∷ []

orcsLpgfRowCount : Nat
orcsLpgfRowCount =
  listLength canonicalORCSLPGFRows

orcsLpgfRowCountIs8 :
  orcsLpgfRowCount ≡ 8
orcsLpgfRowCountIs8 =
  refl

canonicalORCSLPGFSummary : String
canonicalORCSLPGFSummary =
  "O Lane 2 Noether child boundary for localization and pressure; R record cutoff, Leray reconstruction, pressure commutator, boundary/cutoff, and pressure-tail controls; C imports pointwise-to-Abel parent and off-diagonal sibling; S localization theorem=false, pressure commutator theorem=false, A6=false, residual depletion=false, NS Clay=false, terminal=false; L this boundary feeds parent A6 before omega.Somega becomes Abel/shell mean; P prove cutoff, Leray, pressure-tail, and commutator absorption estimates; G no promotion; F localized pressure analytic theorems remain open."

nsLocalizationPressureCommutatorSummary : String
nsLocalizationPressureCommutatorSummary =
  "Records the A6 localization/pressure child target: cutoff and Leray pressure reconstruction must turn all boundary, commutator, and pressure-tail defects into lower-order or epsilon-absorbed errors before the parent pointwise-to-Abel receipt replaces core omega.Somega by Abel/shell mean."

------------------------------------------------------------------------
-- Canonical boundary receipt.

record NSLocalizationPressureCommutatorBoundary : Set where
  field
    status :
      NSLocalizationPressureCommutatorStatus
    statusIsCanonical :
      status ≡ localizationPressureCommutatorBoundaryRecorded_noPromotion
    importedSupport :
      ImportedLocalizationPressureCommutatorSupport
    localizedCutoffObjects :
      List LocalizedCutoffObject
    localizedCutoffObjectCountProof :
      localizedCutoffObjectCount ≡ 9
    localizedCutoffRequirements :
      List LocalizedCutoffRequirement
    localizedCutoffRequirementCountProof :
      localizedCutoffRequirementCount ≡ 8
    lerayPressureReconstructionSteps :
      List LerayPressureReconstructionStep
    lerayPressureReconstructionStepCountProof :
      lerayPressureReconstructionStepCount ≡ 8
    pressureCommutatorTerms :
      List PressureCommutatorTerm
    pressureCommutatorTermCountProof :
      pressureCommutatorTermCount ≡ 9
    boundaryCutoffControls :
      List BoundaryCutoffControl
    boundaryCutoffControlCountProof :
      boundaryCutoffControlCount ≡ 8
    pressureTailControls :
      List PressureTailControl
    pressureTailControlCountProof :
      pressureTailControlCount ≡ 8
    abelReplacementInterfaces :
      List AbelReplacementInterface
    abelReplacementInterfaceCountProof :
      abelReplacementInterfaceCount ≡ 8
    blockers :
      List LocalizationPressureCommutatorBlocker
    blockerCountProof :
      localizationPressureCommutatorBlockerCount ≡ 10
    nonClaimGuards :
      List NonClaimGuard
    nonClaimGuardCountProof :
      nonClaimGuardCount ≡ 7
    orcsLpgfRows :
      List ORCSLPGFRow
    orcsLpgfRowCountProof :
      orcsLpgfRowCount ≡ 8
    localizedCutoffTheoremTarget :
      String
    pressureReconstructionTarget :
      String
    pressureCommutatorTheoremTarget :
      String
    pressureTailControl :
      String
    abelReplacementInterface :
      String
    orcsLpgfSummary :
      String
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsLocalizationPressureCommutatorSummary
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    importsRecordedIsTrue :
      importsRecorded ≡ true
    localizedCutoffObjectsRecordedIsTrue :
      localizedCutoffObjectsRecorded ≡ true
    lerayPressureReconstructionRecordedIsTrue :
      lerayPressureReconstructionRecorded ≡ true
    pressureCommutatorTermsRecordedIsTrue :
      pressureCommutatorTermsRecorded ≡ true
    boundaryCutoffControlsRecordedIsTrue :
      boundaryCutoffControlsRecorded ≡ true
    pressureTailControlsRecordedIsTrue :
      pressureTailControlsRecorded ≡ true
    abelReplacementInterfaceRecordedIsTrue :
      abelReplacementInterfaceRecorded ≡ true
    localizedCutoffTheoremProvedIsFalse :
      localizedCutoffTheoremProved ≡ false
    lerayPressureReconstructionProvedIsFalse :
      lerayPressureReconstructionProved ≡ false
    pressureCommutatorTheoremProvedIsFalse :
      pressureCommutatorTheoremProved ≡ false
    pointwiseToAbelAveragingProvedIsFalse :
      pointwiseToAbelAveragingProved ≡ false
    triadicCompensatedLeakageIdentityProvedIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    fullLocalDefectMonotonicityProvedIsFalse :
      fullLocalDefectMonotonicityProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSLocalizationPressureCommutatorBoundary :
  NSLocalizationPressureCommutatorBoundary
canonicalNSLocalizationPressureCommutatorBoundary =
  record
    { status =
        localizationPressureCommutatorBoundaryRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedLocalizationPressureCommutatorSupport
    ; localizedCutoffObjects =
        canonicalLocalizedCutoffObjects
    ; localizedCutoffObjectCountProof =
        refl
    ; localizedCutoffRequirements =
        canonicalLocalizedCutoffRequirements
    ; localizedCutoffRequirementCountProof =
        refl
    ; lerayPressureReconstructionSteps =
        canonicalLerayPressureReconstructionSteps
    ; lerayPressureReconstructionStepCountProof =
        refl
    ; pressureCommutatorTerms =
        canonicalPressureCommutatorTerms
    ; pressureCommutatorTermCountProof =
        refl
    ; boundaryCutoffControls =
        canonicalBoundaryCutoffControls
    ; boundaryCutoffControlCountProof =
        refl
    ; pressureTailControls =
        canonicalPressureTailControls
    ; pressureTailControlCountProof =
        refl
    ; abelReplacementInterfaces =
        canonicalAbelReplacementInterfaces
    ; abelReplacementInterfaceCountProof =
        refl
    ; blockers =
        canonicalLocalizationPressureCommutatorBlockers
    ; blockerCountProof =
        refl
    ; nonClaimGuards =
        canonicalNonClaimGuards
    ; nonClaimGuardCountProof =
        refl
    ; orcsLpgfRows =
        canonicalORCSLPGFRows
    ; orcsLpgfRowCountProof =
        refl
    ; localizedCutoffTheoremTarget =
        localizedCutoffTheoremTargetText
    ; pressureReconstructionTarget =
        pressureReconstructionTargetText
    ; pressureCommutatorTheoremTarget =
        pressureCommutatorTheoremTargetText
    ; pressureTailControl =
        pressureTailControlText
    ; abelReplacementInterface =
        abelReplacementInterfaceText
    ; orcsLpgfSummary =
        canonicalORCSLPGFSummary
    ; summary =
        nsLocalizationPressureCommutatorSummary
    ; summaryIsCanonical =
        refl
    ; boundaryRecordedIsTrue =
        refl
    ; importsRecordedIsTrue =
        refl
    ; localizedCutoffObjectsRecordedIsTrue =
        refl
    ; lerayPressureReconstructionRecordedIsTrue =
        refl
    ; pressureCommutatorTermsRecordedIsTrue =
        refl
    ; boundaryCutoffControlsRecordedIsTrue =
        refl
    ; pressureTailControlsRecordedIsTrue =
        refl
    ; abelReplacementInterfaceRecordedIsTrue =
        refl
    ; localizedCutoffTheoremProvedIsFalse =
        refl
    ; lerayPressureReconstructionProvedIsFalse =
        refl
    ; pressureCommutatorTheoremProvedIsFalse =
        refl
    ; pointwiseToAbelAveragingProvedIsFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedIsFalse =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; fullLocalDefectMonotonicityProvedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalUnificationPromotedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this child receipt cannot promote downstream claims.

postulate
  localizationPressureBoundaryDoesNotProveLocalizedCutoff :
    localizedCutoffTheoremProved ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProvePressureCommutator :
    pressureCommutatorTheoremProved ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveA6 :
    triadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  localizationPressureBoundaryDoesNotProveTerminalUnification :
    terminalUnificationPromoted ≡ true →
    ⊥

nsLocalizationPressureKeepsLocalizedCutoffFalse :
  localizedCutoffTheoremProved ≡ false
nsLocalizationPressureKeepsLocalizedCutoffFalse =
  refl

nsLocalizationPressureKeepsPressureCommutatorFalse :
  pressureCommutatorTheoremProved ≡ false
nsLocalizationPressureKeepsPressureCommutatorFalse =
  refl

nsLocalizationPressureKeepsA6False :
  triadicCompensatedLeakageIdentityProved ≡ false
nsLocalizationPressureKeepsA6False =
  refl

nsLocalizationPressureKeepsResidualDepletionFalse :
  residualDepletionProved ≡ false
nsLocalizationPressureKeepsResidualDepletionFalse =
  refl

nsLocalizationPressureKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsLocalizationPressureKeepsClayFalse =
  refl

nsLocalizationPressureKeepsTerminalFalse :
  terminalUnificationPromoted ≡ false
nsLocalizationPressureKeepsTerminalFalse =
  refl
