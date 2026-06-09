module DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary
  as MeanSquare
import DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary
  as Arcsine
import DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary
  as Stretching
import DASHI.Physics.Closure.NSFiniteCascadeStretchingNeutralityBoundary
  as Neutrality
import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as PointwiseToAbel

------------------------------------------------------------------------
-- NS A6 diagonal shell stretching to Abel mean boundary.
--
-- This module is a narrow fail-closed receipt for the diagonal part of the
-- pointwise-to-Abel theorem:
--
--   sum_j xi_j <P_j omega, S(P_j u) P_j omega>_phi
--
-- should be identified, after localized shell/triad recording, with the
-- diagonal Abel mean
--
--   (int lambda(c) (2 kappa^2 - 1) d mu_r^diag) * Omega_r
--
-- up to diagonal-only errors.  This is one subtheorem inside the larger A6
-- TriadicCompensatedLeakageIdentity.  It uses the finite stretching formula
-- and kappa receipts as inputs but deliberately does not prove the localized
-- PDE identification, off-diagonal absorption, Abel LLN, residual depletion,
-- NS Clay, or terminal unification.

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
-- Imported canonical support.

pointwiseToAbelBoundaryReference : String
pointwiseToAbelBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

stretchingFormulaBoundaryReference : String
stretchingFormulaBoundaryReference =
  "DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary"

arcsineBoundaryReference : String
arcsineBoundaryReference =
  "DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary"

neutralityBoundaryReference : String
neutralityBoundaryReference =
  "DASHI.Physics.Closure.NSFiniteCascadeStretchingNeutralityBoundary"

meanSquareBoundaryReference : String
meanSquareBoundaryReference =
  "DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary"

pointwiseToAbelBoundaryImported : Bool
pointwiseToAbelBoundaryImported =
  true

stretchingFormulaBoundaryImported : Bool
stretchingFormulaBoundaryImported =
  true

arcsineBoundaryImported : Bool
arcsineBoundaryImported =
  true

neutralityBoundaryImported : Bool
neutralityBoundaryImported =
  true

meanSquareBoundaryImported : Bool
meanSquareBoundaryImported =
  true

record ImportedDiagonalStretchingSupport : Set where
  field
    pointwiseToAbelBoundary :
      PointwiseToAbel.NSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    stretchingFormulaBoundary :
      Stretching.NSCoherentStretchingExactFormulaBoundary
    stretchingFormulaBoundaryIsCanonical :
      stretchingFormulaBoundary
        ≡ Stretching.canonicalNSCoherentStretchingExactFormulaBoundary
    arcsineBoundary :
      Arcsine.NSCascadeKappaArcsineLawBoundary
    arcsineBoundaryIsCanonical :
      arcsineBoundary
        ≡ Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    neutralityBoundary :
      Neutrality.NSFiniteCascadeStretchingNeutralityBoundary
    neutralityBoundaryIsCanonical :
      neutralityBoundary
        ≡ Neutrality.canonicalNSFiniteCascadeStretchingNeutralityBoundary
    meanSquareBoundary :
      MeanSquare.NSBiotSavartStrainMeanSquareExactFormulaBoundary
    meanSquareBoundaryIsCanonical :
      meanSquareBoundary
        ≡ MeanSquare.canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary
    pointwiseToAbelImportedIsTrue :
      pointwiseToAbelBoundaryImported ≡ true
    stretchingFormulaImportedIsTrue :
      stretchingFormulaBoundaryImported ≡ true
    arcsineImportedIsTrue :
      arcsineBoundaryImported ≡ true
    neutralityImportedIsTrue :
      neutralityBoundaryImported ≡ true
    meanSquareImportedIsTrue :
      meanSquareBoundaryImported ≡ true

canonicalImportedDiagonalStretchingSupport :
  ImportedDiagonalStretchingSupport
canonicalImportedDiagonalStretchingSupport =
  record
    { pointwiseToAbelBoundary =
        PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; stretchingFormulaBoundary =
        Stretching.canonicalNSCoherentStretchingExactFormulaBoundary
    ; stretchingFormulaBoundaryIsCanonical =
        refl
    ; arcsineBoundary =
        Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    ; arcsineBoundaryIsCanonical =
        refl
    ; neutralityBoundary =
        Neutrality.canonicalNSFiniteCascadeStretchingNeutralityBoundary
    ; neutralityBoundaryIsCanonical =
        refl
    ; meanSquareBoundary =
        MeanSquare.canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary
    ; meanSquareBoundaryIsCanonical =
        refl
    ; pointwiseToAbelImportedIsTrue =
        refl
    ; stretchingFormulaImportedIsTrue =
        refl
    ; arcsineImportedIsTrue =
        refl
    ; neutralityImportedIsTrue =
        refl
    ; meanSquareImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Diagonal shell weights.

data DiagonalShellWeight : Set where
  localizedShellVorticity-PjOmega :
    DiagonalShellWeight
  localizedShellVelocity-PjU :
    DiagonalShellWeight
  localizedShellEnstrophy-Omega-j-r :
    DiagonalShellWeight
  normalizedDiagonalWeight-xi-j-r :
    DiagonalShellWeight
  abelLogWindowWeight-a-j-r :
    DiagonalShellWeight
  diagonalTriadicAtomWeight-w-j-c-kappa :
    DiagonalShellWeight
  totalLocalizedEnstrophy-Omega-r :
    DiagonalShellWeight
  diagonalAbelMeasure-mu-r-diag :
    DiagonalShellWeight

canonicalDiagonalShellWeights : List DiagonalShellWeight
canonicalDiagonalShellWeights =
  localizedShellVorticity-PjOmega
  ∷ localizedShellVelocity-PjU
  ∷ localizedShellEnstrophy-Omega-j-r
  ∷ normalizedDiagonalWeight-xi-j-r
  ∷ abelLogWindowWeight-a-j-r
  ∷ diagonalTriadicAtomWeight-w-j-c-kappa
  ∷ totalLocalizedEnstrophy-Omega-r
  ∷ diagonalAbelMeasure-mu-r-diag
  ∷ []

diagonalShellWeightCount : Nat
diagonalShellWeightCount =
  listLength canonicalDiagonalShellWeights

diagonalShellWeightCountIs8 :
  diagonalShellWeightCount ≡ 8
diagonalShellWeightCountIs8 =
  refl

diagonalShellWeightDefinitionText : String
diagonalShellWeightDefinitionText =
  "xi_j,r = ||P_j omega||_{L2(phi)}^2 / Omega_r, then Abel-log-windowed to form the diagonal measure mu_r^diag on (c,kappa,lambda)"

data WeightNormalizationRequirement : Set where
  shellWeightsAreNonnegative :
    WeightNormalizationRequirement
  shellWeightsSumToOneAfterOmegaRNormalization :
    WeightNormalizationRequirement
  abelWindowWeightsAreNonnegative :
    WeightNormalizationRequirement
  abelWindowWeightsHaveFiniteMass :
    WeightNormalizationRequirement
  diagonalAtomsUseOnlyNearShellSelfInteractions :
    WeightNormalizationRequirement
  lowEnstrophyCutoffCaseHandledSeparately :
    WeightNormalizationRequirement
  localizationPhiIsFixedAtQrScale :
    WeightNormalizationRequirement

canonicalWeightNormalizationRequirements :
  List WeightNormalizationRequirement
canonicalWeightNormalizationRequirements =
  shellWeightsAreNonnegative
  ∷ shellWeightsSumToOneAfterOmegaRNormalization
  ∷ abelWindowWeightsAreNonnegative
  ∷ abelWindowWeightsHaveFiniteMass
  ∷ diagonalAtomsUseOnlyNearShellSelfInteractions
  ∷ lowEnstrophyCutoffCaseHandledSeparately
  ∷ localizationPhiIsFixedAtQrScale
  ∷ []

weightNormalizationRequirementCount : Nat
weightNormalizationRequirementCount =
  listLength canonicalWeightNormalizationRequirements

weightNormalizationRequirementCountIs7 :
  weightNormalizationRequirementCount ≡ 7
weightNormalizationRequirementCountIs7 =
  refl

------------------------------------------------------------------------
-- Diagonal pointwise stretching term.

data DiagonalStretchingTerm : Set where
  localizedPointwiseOmegaDotSOmega :
    DiagonalStretchingTerm
  diagonalShellTerm-sum-j-PjOmega-Sj-PjOmega :
    DiagonalStretchingTerm
  diagonalShellStrain-Sj-from-PjU :
    DiagonalStretchingTerm
  projectedVorticityDirection-OmegaHat-j-c :
    DiagonalStretchingTerm
  shellTriadOutputDirection-c-j :
    DiagonalStretchingTerm
  shellCoherenceKappa-j :
    DiagonalStretchingTerm
  shellStretchingEigenvalueLambda-j :
    DiagonalStretchingTerm
  diagonalAbelMean-lambda-twoKappaSquaredMinusOne :
    DiagonalStretchingTerm

canonicalDiagonalStretchingTerms : List DiagonalStretchingTerm
canonicalDiagonalStretchingTerms =
  localizedPointwiseOmegaDotSOmega
  ∷ diagonalShellTerm-sum-j-PjOmega-Sj-PjOmega
  ∷ diagonalShellStrain-Sj-from-PjU
  ∷ projectedVorticityDirection-OmegaHat-j-c
  ∷ shellTriadOutputDirection-c-j
  ∷ shellCoherenceKappa-j
  ∷ shellStretchingEigenvalueLambda-j
  ∷ diagonalAbelMean-lambda-twoKappaSquaredMinusOne
  ∷ []

diagonalStretchingTermCount : Nat
diagonalStretchingTermCount =
  listLength canonicalDiagonalStretchingTerms

diagonalStretchingTermCountIs8 :
  diagonalStretchingTermCount ≡ 8
diagonalStretchingTermCountIs8 =
  refl

localizedDiagonalStretchingText : String
localizedDiagonalStretchingText =
  "Diag_r = sum_j <P_j omega, S(P_j u) P_j omega>_{phi_r}"

diagonalAbelMeanTargetText : String
diagonalAbelMeanTargetText =
  "Diag_r / Omega_r = int lambda(c)(2 kappa^2 - 1) d mu_r^diag + diagonal_error_r"

------------------------------------------------------------------------
-- Finite formula transfer into each diagonal shell atom.

data FiniteFormulaInput : Set where
  tangentStrainEigenbasisAtOutputDirection :
    FiniteFormulaInput
  shellVorticityDirectionProjectedToTangentPlane :
    FiniteFormulaInput
  kappaRecordsPropagatedPolarizationCoordinate :
    FiniteFormulaInput
  exactFormulaOmegaSOmegaEqualsLambdaTwoKappaSquaredMinusOne :
    FiniteFormulaInput
  arcsineLawSuppliesNeutralBaselineNotDiagonalProof :
    FiniteFormulaInput
  meanSquareElevenSixtiethsSuppliesScaleForErrorBudget :
    FiniteFormulaInput
  finiteNeutralityDoesNotReplaceLocalizedIdentification :
    FiniteFormulaInput

canonicalFiniteFormulaInputs : List FiniteFormulaInput
canonicalFiniteFormulaInputs =
  tangentStrainEigenbasisAtOutputDirection
  ∷ shellVorticityDirectionProjectedToTangentPlane
  ∷ kappaRecordsPropagatedPolarizationCoordinate
  ∷ exactFormulaOmegaSOmegaEqualsLambdaTwoKappaSquaredMinusOne
  ∷ arcsineLawSuppliesNeutralBaselineNotDiagonalProof
  ∷ meanSquareElevenSixtiethsSuppliesScaleForErrorBudget
  ∷ finiteNeutralityDoesNotReplaceLocalizedIdentification
  ∷ []

finiteFormulaInputCount : Nat
finiteFormulaInputCount =
  listLength canonicalFiniteFormulaInputs

finiteFormulaInputCountIs7 :
  finiteFormulaInputCount ≡ 7
finiteFormulaInputCountIs7 =
  refl

data ShellAtomIdentificationStep : Set where
  freezeDyadicShellAndLocalization :
    ShellAtomIdentificationStep
  chooseTrueLerayOutputDirectionForShellAtom :
    ShellAtomIdentificationStep
  normalizeOutputVorticityDirection :
    ShellAtomIdentificationStep
  readKappaAgainstPropagatedPolarizationFrame :
    ShellAtomIdentificationStep
  applyFiniteStretchingFormulaPerAtom :
    ShellAtomIdentificationStep
  multiplyByLocalizedShellEnstrophyWeight :
    ShellAtomIdentificationStep
  sumOverDiagonalShellWindow :
    ShellAtomIdentificationStep
  compareDiscreteSumWithAbelIntegral :
    ShellAtomIdentificationStep

canonicalShellAtomIdentificationSteps :
  List ShellAtomIdentificationStep
canonicalShellAtomIdentificationSteps =
  freezeDyadicShellAndLocalization
  ∷ chooseTrueLerayOutputDirectionForShellAtom
  ∷ normalizeOutputVorticityDirection
  ∷ readKappaAgainstPropagatedPolarizationFrame
  ∷ applyFiniteStretchingFormulaPerAtom
  ∷ multiplyByLocalizedShellEnstrophyWeight
  ∷ sumOverDiagonalShellWindow
  ∷ compareDiscreteSumWithAbelIntegral
  ∷ []

shellAtomIdentificationStepCount : Nat
shellAtomIdentificationStepCount =
  listLength canonicalShellAtomIdentificationSteps

shellAtomIdentificationStepCountIs8 :
  shellAtomIdentificationStepCount ≡ 8
shellAtomIdentificationStepCountIs8 =
  refl

------------------------------------------------------------------------
-- Error terms restricted to the diagonal theorem.

data DiagonalErrorTerm : Set where
  shellLocalizationCommutatorError :
    DiagonalErrorTerm
  dyadicProjectionDoesNotCommuteWithCutoffError :
    DiagonalErrorTerm
  shellSelfInteractionFrameVariationError :
    DiagonalErrorTerm
  abelWindowDriftError :
    DiagonalErrorTerm
  lowEnstrophyNormalizationError :
    DiagonalErrorTerm
  finiteShellDiscretizationError :
    DiagonalErrorTerm
  outputDirectionDegeneracyExclusionError :
    DiagonalErrorTerm

canonicalDiagonalErrorTerms : List DiagonalErrorTerm
canonicalDiagonalErrorTerms =
  shellLocalizationCommutatorError
  ∷ dyadicProjectionDoesNotCommuteWithCutoffError
  ∷ shellSelfInteractionFrameVariationError
  ∷ abelWindowDriftError
  ∷ lowEnstrophyNormalizationError
  ∷ finiteShellDiscretizationError
  ∷ outputDirectionDegeneracyExclusionError
  ∷ []

diagonalErrorTermCount : Nat
diagonalErrorTermCount =
  listLength canonicalDiagonalErrorTerms

diagonalErrorTermCountIs7 :
  diagonalErrorTermCount ≡ 7
diagonalErrorTermCountIs7 =
  refl

diagonalErrorBudgetText : String
diagonalErrorBudgetText =
  "diagonal_error_r must be absorbed by localization commutators, Abel drift, shell discretization, and low-enstrophy exceptional cases; off-diagonal errors are outside this receipt"

data DiagonalNonClaimGuard : Set where
  noOffDiagonalAbsorptionClaim :
    DiagonalNonClaimGuard
  noAbelLLNMixingClaim :
    DiagonalNonClaimGuard
  noPressureCommutatorClosureClaim :
    DiagonalNonClaimGuard
  noPointwiseTriadSignClaim :
    DiagonalNonClaimGuard
  noResidualDepletionClaim :
    DiagonalNonClaimGuard
  noLocalDefectMonotonicityClaim :
    DiagonalNonClaimGuard
  noClayNavierStokesClaim :
    DiagonalNonClaimGuard
  noTerminalUnificationClaim :
    DiagonalNonClaimGuard

canonicalDiagonalNonClaimGuards : List DiagonalNonClaimGuard
canonicalDiagonalNonClaimGuards =
  noOffDiagonalAbsorptionClaim
  ∷ noAbelLLNMixingClaim
  ∷ noPressureCommutatorClosureClaim
  ∷ noPointwiseTriadSignClaim
  ∷ noResidualDepletionClaim
  ∷ noLocalDefectMonotonicityClaim
  ∷ noClayNavierStokesClaim
  ∷ noTerminalUnificationClaim
  ∷ []

diagonalNonClaimGuardCount : Nat
diagonalNonClaimGuardCount =
  listLength canonicalDiagonalNonClaimGuards

diagonalNonClaimGuardCountIs8 :
  diagonalNonClaimGuardCount ≡ 8
diagonalNonClaimGuardCountIs8 =
  refl

data DiagonalStretchingBlocker : Set where
  missingLocalizedDiagonalShellIdentity :
    DiagonalStretchingBlocker
  missingKappaFrameCompatibilityForPjOmega :
    DiagonalStretchingBlocker
  missingDiagonalMeasureRecordingProof :
    DiagonalStretchingBlocker
  missingCommutatorErrorBound :
    DiagonalStretchingBlocker
  missingAbelWindowDriftBound :
    DiagonalStretchingBlocker
  missingLowEnstrophyExceptionalCaseHandling :
    DiagonalStretchingBlocker
  missingIntegrationIntoFullPointwiseToAbelAveraging :
    DiagonalStretchingBlocker

canonicalDiagonalStretchingBlockers : List DiagonalStretchingBlocker
canonicalDiagonalStretchingBlockers =
  missingLocalizedDiagonalShellIdentity
  ∷ missingKappaFrameCompatibilityForPjOmega
  ∷ missingDiagonalMeasureRecordingProof
  ∷ missingCommutatorErrorBound
  ∷ missingAbelWindowDriftBound
  ∷ missingLowEnstrophyExceptionalCaseHandling
  ∷ missingIntegrationIntoFullPointwiseToAbelAveraging
  ∷ []

diagonalStretchingBlockerCount : Nat
diagonalStretchingBlockerCount =
  listLength canonicalDiagonalStretchingBlockers

diagonalStretchingBlockerCountIs7 :
  diagonalStretchingBlockerCount ≡ 7
diagonalStretchingBlockerCountIs7 =
  refl

------------------------------------------------------------------------
-- Boundary status and fail-closed booleans.

boundaryRecorded : Bool
boundaryRecorded =
  true

importsRecorded : Bool
importsRecorded =
  true

diagonalShellWeightsRecorded : Bool
diagonalShellWeightsRecorded =
  true

diagonalStretchingTermsRecorded : Bool
diagonalStretchingTermsRecorded =
  true

finiteFormulaInputsRecorded : Bool
finiteFormulaInputsRecorded =
  true

diagonalErrorBudgetRecorded : Bool
diagonalErrorBudgetRecorded =
  true

diagonalStretchingToAbelMeanProved : Bool
diagonalStretchingToAbelMeanProved =
  false

localizedDiagonalShellIdentityProved : Bool
localizedDiagonalShellIdentityProved =
  false

diagonalMeasureRecordingProved : Bool
diagonalMeasureRecordingProved =
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

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalUnificationPromoted : Bool
terminalUnificationPromoted =
  false

data NSDiagonalStretchingToAbelMeanStatus : Set where
  diagonalStretchingToAbelMeanBoundaryRecorded_noPromotion :
    NSDiagonalStretchingToAbelMeanStatus

nsDiagonalStretchingToAbelMeanSummary : String
nsDiagonalStretchingToAbelMeanSummary =
  "Records the A6 diagonal-shell target Diag_r/Omega_r = int lambda(c)(2 kappa^2 - 1) d mu_r^diag + diagonal_error_r, using finite kappa/stretching receipts while leaving the localized PDE proof and all Clay promotion false."

record NSDiagonalStretchingToAbelMeanBoundary : Set where
  field
    status :
      NSDiagonalStretchingToAbelMeanStatus
    statusIsCanonical :
      status ≡ diagonalStretchingToAbelMeanBoundaryRecorded_noPromotion
    importedSupport :
      ImportedDiagonalStretchingSupport
    diagonalShellWeights :
      List DiagonalShellWeight
    diagonalShellWeightCountProof :
      diagonalShellWeightCount ≡ 8
    normalizationRequirements :
      List WeightNormalizationRequirement
    normalizationRequirementCountProof :
      weightNormalizationRequirementCount ≡ 7
    diagonalStretchingTerms :
      List DiagonalStretchingTerm
    diagonalStretchingTermCountProof :
      diagonalStretchingTermCount ≡ 8
    finiteFormulaInputs :
      List FiniteFormulaInput
    finiteFormulaInputCountProof :
      finiteFormulaInputCount ≡ 7
    shellAtomIdentificationSteps :
      List ShellAtomIdentificationStep
    shellAtomIdentificationStepCountProof :
      shellAtomIdentificationStepCount ≡ 8
    diagonalErrors :
      List DiagonalErrorTerm
    diagonalErrorCountProof :
      diagonalErrorTermCount ≡ 7
    nonClaimGuards :
      List DiagonalNonClaimGuard
    nonClaimGuardCountProof :
      diagonalNonClaimGuardCount ≡ 8
    blockers :
      List DiagonalStretchingBlocker
    blockerCountProof :
      diagonalStretchingBlockerCount ≡ 7
    shellWeightDefinition :
      String
    localizedDiagonalStretching :
      String
    diagonalAbelMeanTarget :
      String
    diagonalErrorBudget :
      String
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsDiagonalStretchingToAbelMeanSummary
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    importsRecordedIsTrue :
      importsRecorded ≡ true
    diagonalShellWeightsRecordedIsTrue :
      diagonalShellWeightsRecorded ≡ true
    diagonalStretchingTermsRecordedIsTrue :
      diagonalStretchingTermsRecorded ≡ true
    finiteFormulaInputsRecordedIsTrue :
      finiteFormulaInputsRecorded ≡ true
    diagonalErrorBudgetRecordedIsTrue :
      diagonalErrorBudgetRecorded ≡ true
    diagonalStretchingToAbelMeanProvedIsFalse :
      diagonalStretchingToAbelMeanProved ≡ false
    localizedDiagonalShellIdentityProvedIsFalse :
      localizedDiagonalShellIdentityProved ≡ false
    diagonalMeasureRecordingProvedIsFalse :
      diagonalMeasureRecordingProved ≡ false
    pointwiseToAbelAveragingProvedIsFalse :
      pointwiseToAbelAveragingProved ≡ false
    triadicCompensatedLeakageIdentityProvedIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSDiagonalStretchingToAbelMeanBoundary :
  NSDiagonalStretchingToAbelMeanBoundary
canonicalNSDiagonalStretchingToAbelMeanBoundary =
  record
    { status =
        diagonalStretchingToAbelMeanBoundaryRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedDiagonalStretchingSupport
    ; diagonalShellWeights =
        canonicalDiagonalShellWeights
    ; diagonalShellWeightCountProof =
        refl
    ; normalizationRequirements =
        canonicalWeightNormalizationRequirements
    ; normalizationRequirementCountProof =
        refl
    ; diagonalStretchingTerms =
        canonicalDiagonalStretchingTerms
    ; diagonalStretchingTermCountProof =
        refl
    ; finiteFormulaInputs =
        canonicalFiniteFormulaInputs
    ; finiteFormulaInputCountProof =
        refl
    ; shellAtomIdentificationSteps =
        canonicalShellAtomIdentificationSteps
    ; shellAtomIdentificationStepCountProof =
        refl
    ; diagonalErrors =
        canonicalDiagonalErrorTerms
    ; diagonalErrorCountProof =
        refl
    ; nonClaimGuards =
        canonicalDiagonalNonClaimGuards
    ; nonClaimGuardCountProof =
        refl
    ; blockers =
        canonicalDiagonalStretchingBlockers
    ; blockerCountProof =
        refl
    ; shellWeightDefinition =
        diagonalShellWeightDefinitionText
    ; localizedDiagonalStretching =
        localizedDiagonalStretchingText
    ; diagonalAbelMeanTarget =
        diagonalAbelMeanTargetText
    ; diagonalErrorBudget =
        diagonalErrorBudgetText
    ; summary =
        nsDiagonalStretchingToAbelMeanSummary
    ; summaryIsCanonical =
        refl
    ; boundaryRecordedIsTrue =
        refl
    ; importsRecordedIsTrue =
        refl
    ; diagonalShellWeightsRecordedIsTrue =
        refl
    ; diagonalStretchingTermsRecordedIsTrue =
        refl
    ; finiteFormulaInputsRecordedIsTrue =
        refl
    ; diagonalErrorBudgetRecordedIsTrue =
        refl
    ; diagonalStretchingToAbelMeanProvedIsFalse =
        refl
    ; localizedDiagonalShellIdentityProvedIsFalse =
        refl
    ; diagonalMeasureRecordingProvedIsFalse =
        refl
    ; pointwiseToAbelAveragingProvedIsFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedIsFalse =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalUnificationPromotedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this diagonal receipt cannot promote downstream claims.

postulate
  diagonalStretchingBoundaryDoesNotProvePointwiseToAbel :
    pointwiseToAbelAveragingProved ≡ true →
    ⊥

  diagonalStretchingBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  diagonalStretchingBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  diagonalStretchingBoundaryDoesNotProveTerminalUnification :
    terminalUnificationPromoted ≡ true →
    ⊥

nsDiagonalStretchingKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsDiagonalStretchingKeepsClayFalse =
  refl

nsDiagonalStretchingKeepsTerminalFalse :
  terminalUnificationPromoted ≡ false
nsDiagonalStretchingKeepsTerminalFalse =
  refl
