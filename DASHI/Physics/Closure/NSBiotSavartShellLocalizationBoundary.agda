module DASHI.Physics.Closure.NSBiotSavartShellLocalizationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary
  as Diagonal
import DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary
  as OffDiagonal
import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as PointwiseToAbel
import DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary
  as Shell

------------------------------------------------------------------------
-- NS A6.2 Biot-Savart shell localization boundary.
--
-- This module records the new hard sub-lemma inside the A6
-- pointwise-to-Abel proof attempt:
--
--   the localized same-shell strain tensor seen in
--
--     <P_j omega, S(u) P_j omega>_{phi_r}
--
--   must be replaceable by the true same-shell Biot-Savart/Leray strain
--   multiplier L_j[P_j u], with all off-shell strain tails decaying through
--   Calderon-Zygmund kernel estimates and Type-I Lorentz L^{3,inf}
--   control.
--
-- Target shape:
--
--   || P_j S(u) - L_j[P_j u] ||_{L2 -> L2}
--     <= C(M,phi) 2^{-delta |j-k|} ||u||_{L^{3,inf}}
--
--   for off-shell k, plus exact same-shell multiplier identification on
--   the diagonal shell.
--
-- This is deliberately fail-closed.  It records the exact obligations:
-- same-shell strain multiplier identification, off-shell leakage decay,
-- Calderon-Zygmund kernel estimate, Lorentz L3inf dependence,
-- diagonal-to-Abel compatibility, and no Clay promotion.  It does not
-- prove the CZ estimate, does not prove A6, and does not promote NS Clay.

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

pointwiseToAbelBoundaryReference : String
pointwiseToAbelBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

diagonalStretchingBoundaryReference : String
diagonalStretchingBoundaryReference =
  "DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary"

offDiagonalAbsorptionBoundaryReference : String
offDiagonalAbsorptionBoundaryReference =
  "DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary"

triadicShellBernsteinHolderBoundaryReference : String
triadicShellBernsteinHolderBoundaryReference =
  "DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary"

pointwiseToAbelBoundaryImported : Bool
pointwiseToAbelBoundaryImported =
  true

diagonalStretchingBoundaryImported : Bool
diagonalStretchingBoundaryImported =
  true

offDiagonalAbsorptionBoundaryImported : Bool
offDiagonalAbsorptionBoundaryImported =
  true

triadicShellBernsteinHolderBoundaryImported : Bool
triadicShellBernsteinHolderBoundaryImported =
  true

record ImportedBiotSavartShellLocalizationSupport : Set where
  field
    pointwiseToAbelBoundary :
      PointwiseToAbel.NSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    diagonalStretchingBoundary :
      Diagonal.NSDiagonalStretchingToAbelMeanBoundary
    diagonalStretchingBoundaryIsCanonical :
      diagonalStretchingBoundary
        ≡ Diagonal.canonicalNSDiagonalStretchingToAbelMeanBoundary
    offDiagonalAbsorptionBoundary :
      OffDiagonal.NSOffDiagonalShellAbsorptionBoundary
    offDiagonalAbsorptionBoundaryIsCanonical :
      offDiagonalAbsorptionBoundary
        ≡ OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    shellEstimateTarget :
      Shell.TightTriadicShellEstimateTarget
    shellEstimateTargetIsCanonical :
      shellEstimateTarget
        ≡ Shell.canonicalTightTriadicShellEstimateTarget
    pointwiseToAbelBoundaryImportedIsTrue :
      pointwiseToAbelBoundaryImported ≡ true
    diagonalStretchingBoundaryImportedIsTrue :
      diagonalStretchingBoundaryImported ≡ true
    offDiagonalAbsorptionBoundaryImportedIsTrue :
      offDiagonalAbsorptionBoundaryImported ≡ true
    triadicShellBernsteinHolderBoundaryImportedIsTrue :
      triadicShellBernsteinHolderBoundaryImported ≡ true

canonicalImportedBiotSavartShellLocalizationSupport :
  ImportedBiotSavartShellLocalizationSupport
canonicalImportedBiotSavartShellLocalizationSupport =
  record
    { pointwiseToAbelBoundary =
        PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; diagonalStretchingBoundary =
        Diagonal.canonicalNSDiagonalStretchingToAbelMeanBoundary
    ; diagonalStretchingBoundaryIsCanonical =
        refl
    ; offDiagonalAbsorptionBoundary =
        OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    ; offDiagonalAbsorptionBoundaryIsCanonical =
        refl
    ; shellEstimateTarget =
        Shell.canonicalTightTriadicShellEstimateTarget
    ; shellEstimateTargetIsCanonical =
        refl
    ; pointwiseToAbelBoundaryImportedIsTrue =
        refl
    ; diagonalStretchingBoundaryImportedIsTrue =
        refl
    ; offDiagonalAbsorptionBoundaryImportedIsTrue =
        refl
    ; triadicShellBernsteinHolderBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Operators and localized shell carriers.

data BiotSavartShellObject : Set where
  dyadicVelocityShell-PjU :
    BiotSavartShellObject
  dyadicVorticityShell-PjOmega :
    BiotSavartShellObject
  strainTensor-S-u-symmetricGrad :
    BiotSavartShellObject
  sameShellStrainMultiplier-Lj-PjU :
    BiotSavartShellObject
  localizedCutoff-phi-r :
    BiotSavartShellObject
  localizedDiagonalPairing-PjOmega-S-PjOmega :
    BiotSavartShellObject
  offShellVelocityTail-PkU-kNotJ :
    BiotSavartShellObject
  CalderonZygmundKernel-K-strain :
    BiotSavartShellObject
  LorentzTypeIBound-L3inf :
    BiotSavartShellObject
  AbelDiagonalAtom-mu-r-diag :
    BiotSavartShellObject

canonicalBiotSavartShellObjects : List BiotSavartShellObject
canonicalBiotSavartShellObjects =
  dyadicVelocityShell-PjU
  ∷ dyadicVorticityShell-PjOmega
  ∷ strainTensor-S-u-symmetricGrad
  ∷ sameShellStrainMultiplier-Lj-PjU
  ∷ localizedCutoff-phi-r
  ∷ localizedDiagonalPairing-PjOmega-S-PjOmega
  ∷ offShellVelocityTail-PkU-kNotJ
  ∷ CalderonZygmundKernel-K-strain
  ∷ LorentzTypeIBound-L3inf
  ∷ AbelDiagonalAtom-mu-r-diag
  ∷ []

biotSavartShellObjectCount : Nat
biotSavartShellObjectCount =
  listLength canonicalBiotSavartShellObjects

biotSavartShellObjectCountIs10 :
  biotSavartShellObjectCount ≡ 10
biotSavartShellObjectCountIs10 =
  refl

sameShellMultiplierTargetText : String
sameShellMultiplierTargetText =
  "On the diagonal shell, P_j S(u) restricted to P_j omega is identified with the true Biot-Savart/Leray strain multiplier L_j[P_j u]"

offShellDecayTargetText : String
offShellDecayTargetText =
  "For k not near j, the strain tail from P_k u contributes at most C 2^{-delta |j-k|} ||u||_{L3inf} to the localized L2 pairing"

calderonZygmundKernelTargetText : String
calderonZygmundKernelTargetText =
  "Use the even CZ strain kernel, dyadic cancellation, annular decay, and cutoff commutator bounds to localize S(u) to the same shell"

lorentzDependenceTargetText : String
lorentzDependenceTargetText =
  "All constants are allowed to depend on the Type-I Lorentz ||u||_{L^{3,inf}} bound and cutoff profile, but not on j or r after scaling"

diagonalToAbelCompatibilityText : String
diagonalToAbelCompatibilityText =
  "The localized same-shell multiplier must preserve the diagonal atom used by mu_r^diag before applying lambda(c)(2 kappa^2 - 1)"

------------------------------------------------------------------------
-- Exact obligations for the A6.2 theorem.

data ShellLocalizationObligation : Set where
  sameShellStrainMultiplierIdentification :
    ShellLocalizationObligation
  offShellLeakageDecay :
    ShellLocalizationObligation
  CalderonZygmundKernelEstimate :
    ShellLocalizationObligation
  LorentzL3infDependence :
    ShellLocalizationObligation
  diagonalToAbelCompatibility :
    ShellLocalizationObligation
  localizedCutoffCommutatorControl :
    ShellLocalizationObligation
  uniformDyadicConstantControl :
    ShellLocalizationObligation
  degeneracyAndLowEnstrophyCasesSeparated :
    ShellLocalizationObligation

canonicalShellLocalizationObligations :
  List ShellLocalizationObligation
canonicalShellLocalizationObligations =
  sameShellStrainMultiplierIdentification
  ∷ offShellLeakageDecay
  ∷ CalderonZygmundKernelEstimate
  ∷ LorentzL3infDependence
  ∷ diagonalToAbelCompatibility
  ∷ localizedCutoffCommutatorControl
  ∷ uniformDyadicConstantControl
  ∷ degeneracyAndLowEnstrophyCasesSeparated
  ∷ []

shellLocalizationObligationCount : Nat
shellLocalizationObligationCount =
  listLength canonicalShellLocalizationObligations

shellLocalizationObligationCountIs8 :
  shellLocalizationObligationCount ≡ 8
shellLocalizationObligationCountIs8 =
  refl

data SameShellMultiplierStep : Set where
  FourierSymbolForBiotSavartVelocity :
    SameShellMultiplierStep
  FourierSymbolForSymmetricGradientStrain :
    SameShellMultiplierStep
  LerayProjectionKeepsDivergenceFreeShell :
    SameShellMultiplierStep
  freezeShellFrequencyWithinAnnulus :
    SameShellMultiplierStep
  identifyTangentStrainEigenbasis :
    SameShellMultiplierStep
  compareWithFiniteStretchingFormula :
    SameShellMultiplierStep
  recordMultiplierEqualityBeforeAbelAveraging :
    SameShellMultiplierStep

canonicalSameShellMultiplierSteps : List SameShellMultiplierStep
canonicalSameShellMultiplierSteps =
  FourierSymbolForBiotSavartVelocity
  ∷ FourierSymbolForSymmetricGradientStrain
  ∷ LerayProjectionKeepsDivergenceFreeShell
  ∷ freezeShellFrequencyWithinAnnulus
  ∷ identifyTangentStrainEigenbasis
  ∷ compareWithFiniteStretchingFormula
  ∷ recordMultiplierEqualityBeforeAbelAveraging
  ∷ []

sameShellMultiplierStepCount : Nat
sameShellMultiplierStepCount =
  listLength canonicalSameShellMultiplierSteps

sameShellMultiplierStepCountIs7 :
  sameShellMultiplierStepCount ≡ 7
sameShellMultiplierStepCountIs7 =
  refl

data OffShellLeakageDecayStep : Set where
  splitVelocityIntoSameShellAndTail :
    OffShellLeakageDecayStep
  exploitDyadicFrequencySeparation :
    OffShellLeakageDecayStep
  useKernelCancellationOnAnnuli :
    OffShellLeakageDecayStep
  proveTwoMinusDeltaSeparationFactor :
    OffShellLeakageDecayStep
  sumGeometricTailOverShellGap :
    OffShellLeakageDecayStep
  sendRemainderToOffDiagonalAbsorption :
    OffShellLeakageDecayStep

canonicalOffShellLeakageDecaySteps :
  List OffShellLeakageDecayStep
canonicalOffShellLeakageDecaySteps =
  splitVelocityIntoSameShellAndTail
  ∷ exploitDyadicFrequencySeparation
  ∷ useKernelCancellationOnAnnuli
  ∷ proveTwoMinusDeltaSeparationFactor
  ∷ sumGeometricTailOverShellGap
  ∷ sendRemainderToOffDiagonalAbsorption
  ∷ []

offShellLeakageDecayStepCount : Nat
offShellLeakageDecayStepCount =
  listLength canonicalOffShellLeakageDecaySteps

offShellLeakageDecayStepCountIs6 :
  offShellLeakageDecayStepCount ≡ 6
offShellLeakageDecayStepCountIs6 =
  refl

data CZKernelEstimateRequirement : Set where
  strainKernelIsEvenCalderonZygmund :
    CZKernelEstimateRequirement
  kernelHasMeanZeroOnSpheres :
    CZKernelEstimateRequirement
  dyadicProjectorHasCancellation :
    CZKernelEstimateRequirement
  localizedCutoffProducesCommutatorKernel :
    CZKernelEstimateRequirement
  annularIntegralGainsShellSeparation :
    CZKernelEstimateRequirement
  nearFieldIsHandledBySameShellMultiplier :
    CZKernelEstimateRequirement
  farFieldIsRecordedAsTailBudget :
    CZKernelEstimateRequirement
  constantsUniformUnderParabolicScaling :
    CZKernelEstimateRequirement

canonicalCZKernelEstimateRequirements :
  List CZKernelEstimateRequirement
canonicalCZKernelEstimateRequirements =
  strainKernelIsEvenCalderonZygmund
  ∷ kernelHasMeanZeroOnSpheres
  ∷ dyadicProjectorHasCancellation
  ∷ localizedCutoffProducesCommutatorKernel
  ∷ annularIntegralGainsShellSeparation
  ∷ nearFieldIsHandledBySameShellMultiplier
  ∷ farFieldIsRecordedAsTailBudget
  ∷ constantsUniformUnderParabolicScaling
  ∷ []

czKernelEstimateRequirementCount : Nat
czKernelEstimateRequirementCount =
  listLength canonicalCZKernelEstimateRequirements

czKernelEstimateRequirementCountIs8 :
  czKernelEstimateRequirementCount ≡ 8
czKernelEstimateRequirementCountIs8 =
  refl

data LorentzDependenceClause : Set where
  TypeIBoundSupScaleL3inf :
    LorentzDependenceClause
  weakL3ControlsLocalizedVelocityShellMass :
    LorentzDependenceClause
  LorentzHolderPairsWithL3Over2LocalStrain :
    LorentzDependenceClause
  constantsDependOnMNotShellIndex :
    LorentzDependenceClause
  lowFrequencyTailUsesLocalEnergyFallback :
    LorentzDependenceClause
  highFrequencyTailUsesDyadicDecay :
    LorentzDependenceClause

canonicalLorentzDependenceClauses :
  List LorentzDependenceClause
canonicalLorentzDependenceClauses =
  TypeIBoundSupScaleL3inf
  ∷ weakL3ControlsLocalizedVelocityShellMass
  ∷ LorentzHolderPairsWithL3Over2LocalStrain
  ∷ constantsDependOnMNotShellIndex
  ∷ lowFrequencyTailUsesLocalEnergyFallback
  ∷ highFrequencyTailUsesDyadicDecay
  ∷ []

lorentzDependenceClauseCount : Nat
lorentzDependenceClauseCount =
  listLength canonicalLorentzDependenceClauses

lorentzDependenceClauseCountIs6 :
  lorentzDependenceClauseCount ≡ 6
lorentzDependenceClauseCountIs6 =
  refl

data DiagonalToAbelCompatibilityStep : Set where
  sameShellAtomUsesPjUAndPjOmega :
    DiagonalToAbelCompatibilityStep
  outputDirectionRecordedBeforeShellSummation :
    DiagonalToAbelCompatibilityStep
  kappaFrameUnchangedByLocalizationReplacement :
    DiagonalToAbelCompatibilityStep
  lambdaEigenvalueMatchesBiotSavartStrainSymbol :
    DiagonalToAbelCompatibilityStep
  AbelMeasureReceivesOnlyLocalizedDiagonalAtoms :
    DiagonalToAbelCompatibilityStep
  residualTailIsNotFoldedIntoDiagonalBias :
    DiagonalToAbelCompatibilityStep
  compatibleWithDiagonalStretchingBoundary :
    DiagonalToAbelCompatibilityStep

canonicalDiagonalToAbelCompatibilitySteps :
  List DiagonalToAbelCompatibilityStep
canonicalDiagonalToAbelCompatibilitySteps =
  sameShellAtomUsesPjUAndPjOmega
  ∷ outputDirectionRecordedBeforeShellSummation
  ∷ kappaFrameUnchangedByLocalizationReplacement
  ∷ lambdaEigenvalueMatchesBiotSavartStrainSymbol
  ∷ AbelMeasureReceivesOnlyLocalizedDiagonalAtoms
  ∷ residualTailIsNotFoldedIntoDiagonalBias
  ∷ compatibleWithDiagonalStretchingBoundary
  ∷ []

diagonalToAbelCompatibilityStepCount : Nat
diagonalToAbelCompatibilityStepCount =
  listLength canonicalDiagonalToAbelCompatibilitySteps

diagonalToAbelCompatibilityStepCountIs7 :
  diagonalToAbelCompatibilityStepCount ≡ 7
diagonalToAbelCompatibilityStepCountIs7 =
  refl

------------------------------------------------------------------------
-- Error budget and blockers.

data ShellLocalizationErrorTerm : Set where
  offShellStrainLeakageError :
    ShellLocalizationErrorTerm
  cutoffCommutatorKernelError :
    ShellLocalizationErrorTerm
  lowFrequencyLorentzTailError :
    ShellLocalizationErrorTerm
  highFrequencyGeometricTailError :
    ShellLocalizationErrorTerm
  finiteAnnulusSymbolVariationError :
    ShellLocalizationErrorTerm
  degeneracyOutputDirectionError :
    ShellLocalizationErrorTerm
  lowEnstrophyNormalizationError :
    ShellLocalizationErrorTerm
  diagonalAtomRecordingMismatchError :
    ShellLocalizationErrorTerm

canonicalShellLocalizationErrorTerms :
  List ShellLocalizationErrorTerm
canonicalShellLocalizationErrorTerms =
  offShellStrainLeakageError
  ∷ cutoffCommutatorKernelError
  ∷ lowFrequencyLorentzTailError
  ∷ highFrequencyGeometricTailError
  ∷ finiteAnnulusSymbolVariationError
  ∷ degeneracyOutputDirectionError
  ∷ lowEnstrophyNormalizationError
  ∷ diagonalAtomRecordingMismatchError
  ∷ []

shellLocalizationErrorTermCount : Nat
shellLocalizationErrorTermCount =
  listLength canonicalShellLocalizationErrorTerms

shellLocalizationErrorTermCountIs8 :
  shellLocalizationErrorTermCount ≡ 8
shellLocalizationErrorTermCountIs8 =
  refl

data ShellLocalizationBlocker : Set where
  missingSameShellMultiplierEqualityProof :
    ShellLocalizationBlocker
  missingOffShellCZDecayProof :
    ShellLocalizationBlocker
  missingLorentzL3infConstantTracking :
    ShellLocalizationBlocker
  missingCutoffCommutatorKernelEstimate :
    ShellLocalizationBlocker
  missingDiagonalMeasureCompatibilityProof :
    ShellLocalizationBlocker
  missingIntegrationIntoA6ErrorBudget :
    ShellLocalizationBlocker

canonicalShellLocalizationBlockers :
  List ShellLocalizationBlocker
canonicalShellLocalizationBlockers =
  missingSameShellMultiplierEqualityProof
  ∷ missingOffShellCZDecayProof
  ∷ missingLorentzL3infConstantTracking
  ∷ missingCutoffCommutatorKernelEstimate
  ∷ missingDiagonalMeasureCompatibilityProof
  ∷ missingIntegrationIntoA6ErrorBudget
  ∷ []

shellLocalizationBlockerCount : Nat
shellLocalizationBlockerCount =
  listLength canonicalShellLocalizationBlockers

shellLocalizationBlockerCountIs6 :
  shellLocalizationBlockerCount ≡ 6
shellLocalizationBlockerCountIs6 =
  refl

data NonPromotionGuard : Set where
  noA6ProofFromThisBoundary :
    NonPromotionGuard
  noPointwiseToAbelClosureClaim :
    NonPromotionGuard
  noResidualDepletionClaim :
    NonPromotionGuard
  noLocalDefectMonotonicityClaim :
    NonPromotionGuard
  noCKNBKMClosureClaim :
    NonPromotionGuard
  noClayNavierStokesClaim :
    NonPromotionGuard
  noTerminalUnificationClaim :
    NonPromotionGuard

canonicalNonPromotionGuards : List NonPromotionGuard
canonicalNonPromotionGuards =
  noA6ProofFromThisBoundary
  ∷ noPointwiseToAbelClosureClaim
  ∷ noResidualDepletionClaim
  ∷ noLocalDefectMonotonicityClaim
  ∷ noCKNBKMClosureClaim
  ∷ noClayNavierStokesClaim
  ∷ noTerminalUnificationClaim
  ∷ []

nonPromotionGuardCount : Nat
nonPromotionGuardCount =
  listLength canonicalNonPromotionGuards

nonPromotionGuardCountIs7 :
  nonPromotionGuardCount ≡ 7
nonPromotionGuardCountIs7 =
  refl

------------------------------------------------------------------------
-- Fail-closed status booleans.

boundaryRecorded : Bool
boundaryRecorded =
  true

importsRecorded : Bool
importsRecorded =
  true

sameShellStrainMultiplierIdentificationRecorded : Bool
sameShellStrainMultiplierIdentificationRecorded =
  true

offShellLeakageDecayRecorded : Bool
offShellLeakageDecayRecorded =
  true

calderonZygmundKernelEstimateRecorded : Bool
calderonZygmundKernelEstimateRecorded =
  true

lorentzL3infDependenceRecorded : Bool
lorentzL3infDependenceRecorded =
  true

diagonalToAbelCompatibilityRecorded : Bool
diagonalToAbelCompatibilityRecorded =
  true

biotSavartShellLocalizationProved : Bool
biotSavartShellLocalizationProved =
  false

sameShellMultiplierIdentificationProved : Bool
sameShellMultiplierIdentificationProved =
  false

offShellLeakageDecayProved : Bool
offShellLeakageDecayProved =
  false

calderonZygmundKernelEstimateProved : Bool
calderonZygmundKernelEstimateProved =
  false

lorentzL3infDependenceProved : Bool
lorentzL3infDependenceProved =
  false

diagonalToAbelCompatibilityProved : Bool
diagonalToAbelCompatibilityProved =
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

------------------------------------------------------------------------
-- Canonical boundary receipt.

record NSBiotSavartShellLocalizationBoundary : Set where
  field
    importedSupport :
      ImportedBiotSavartShellLocalizationSupport
    shellObjects :
      List BiotSavartShellObject
    shellObjectCountProof :
      biotSavartShellObjectCount ≡ 10
    obligations :
      List ShellLocalizationObligation
    obligationCountProof :
      shellLocalizationObligationCount ≡ 8
    sameShellMultiplierSteps :
      List SameShellMultiplierStep
    sameShellMultiplierStepCountProof :
      sameShellMultiplierStepCount ≡ 7
    offShellLeakageDecaySteps :
      List OffShellLeakageDecayStep
    offShellLeakageDecayStepCountProof :
      offShellLeakageDecayStepCount ≡ 6
    czKernelEstimateRequirements :
      List CZKernelEstimateRequirement
    czKernelEstimateRequirementCountProof :
      czKernelEstimateRequirementCount ≡ 8
    lorentzDependenceClauses :
      List LorentzDependenceClause
    lorentzDependenceClauseCountProof :
      lorentzDependenceClauseCount ≡ 6
    diagonalToAbelCompatibilitySteps :
      List DiagonalToAbelCompatibilityStep
    diagonalToAbelCompatibilityStepCountProof :
      diagonalToAbelCompatibilityStepCount ≡ 7
    errorTerms :
      List ShellLocalizationErrorTerm
    errorTermCountProof :
      shellLocalizationErrorTermCount ≡ 8
    blockers :
      List ShellLocalizationBlocker
    blockerCountProof :
      shellLocalizationBlockerCount ≡ 6
    nonPromotionGuards :
      List NonPromotionGuard
    nonPromotionGuardCountProof :
      nonPromotionGuardCount ≡ 7
    sameShellMultiplierTarget :
      String
    offShellDecayTarget :
      String
    calderonZygmundKernelTarget :
      String
    lorentzDependenceTarget :
      String
    diagonalToAbelCompatibilityTarget :
      String
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    importsRecordedIsTrue :
      importsRecorded ≡ true
    sameShellStrainMultiplierIdentificationRecordedIsTrue :
      sameShellStrainMultiplierIdentificationRecorded ≡ true
    offShellLeakageDecayRecordedIsTrue :
      offShellLeakageDecayRecorded ≡ true
    calderonZygmundKernelEstimateRecordedIsTrue :
      calderonZygmundKernelEstimateRecorded ≡ true
    lorentzL3infDependenceRecordedIsTrue :
      lorentzL3infDependenceRecorded ≡ true
    diagonalToAbelCompatibilityRecordedIsTrue :
      diagonalToAbelCompatibilityRecorded ≡ true
    biotSavartShellLocalizationProvedIsFalse :
      biotSavartShellLocalizationProved ≡ false
    sameShellMultiplierIdentificationProvedIsFalse :
      sameShellMultiplierIdentificationProved ≡ false
    offShellLeakageDecayProvedIsFalse :
      offShellLeakageDecayProved ≡ false
    calderonZygmundKernelEstimateProvedIsFalse :
      calderonZygmundKernelEstimateProved ≡ false
    lorentzL3infDependenceProvedIsFalse :
      lorentzL3infDependenceProved ≡ false
    diagonalToAbelCompatibilityProvedIsFalse :
      diagonalToAbelCompatibilityProved ≡ false
    triadicCompensatedLeakageIdentityProvedIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSBiotSavartShellLocalizationBoundary :
  NSBiotSavartShellLocalizationBoundary
canonicalNSBiotSavartShellLocalizationBoundary =
  record
    { importedSupport =
        canonicalImportedBiotSavartShellLocalizationSupport
    ; shellObjects =
        canonicalBiotSavartShellObjects
    ; shellObjectCountProof =
        refl
    ; obligations =
        canonicalShellLocalizationObligations
    ; obligationCountProof =
        refl
    ; sameShellMultiplierSteps =
        canonicalSameShellMultiplierSteps
    ; sameShellMultiplierStepCountProof =
        refl
    ; offShellLeakageDecaySteps =
        canonicalOffShellLeakageDecaySteps
    ; offShellLeakageDecayStepCountProof =
        refl
    ; czKernelEstimateRequirements =
        canonicalCZKernelEstimateRequirements
    ; czKernelEstimateRequirementCountProof =
        refl
    ; lorentzDependenceClauses =
        canonicalLorentzDependenceClauses
    ; lorentzDependenceClauseCountProof =
        refl
    ; diagonalToAbelCompatibilitySteps =
        canonicalDiagonalToAbelCompatibilitySteps
    ; diagonalToAbelCompatibilityStepCountProof =
        refl
    ; errorTerms =
        canonicalShellLocalizationErrorTerms
    ; errorTermCountProof =
        refl
    ; blockers =
        canonicalShellLocalizationBlockers
    ; blockerCountProof =
        refl
    ; nonPromotionGuards =
        canonicalNonPromotionGuards
    ; nonPromotionGuardCountProof =
        refl
    ; sameShellMultiplierTarget =
        sameShellMultiplierTargetText
    ; offShellDecayTarget =
        offShellDecayTargetText
    ; calderonZygmundKernelTarget =
        calderonZygmundKernelTargetText
    ; lorentzDependenceTarget =
        lorentzDependenceTargetText
    ; diagonalToAbelCompatibilityTarget =
        diagonalToAbelCompatibilityText
    ; boundaryRecordedIsTrue =
        refl
    ; importsRecordedIsTrue =
        refl
    ; sameShellStrainMultiplierIdentificationRecordedIsTrue =
        refl
    ; offShellLeakageDecayRecordedIsTrue =
        refl
    ; calderonZygmundKernelEstimateRecordedIsTrue =
        refl
    ; lorentzL3infDependenceRecordedIsTrue =
        refl
    ; diagonalToAbelCompatibilityRecordedIsTrue =
        refl
    ; biotSavartShellLocalizationProvedIsFalse =
        refl
    ; sameShellMultiplierIdentificationProvedIsFalse =
        refl
    ; offShellLeakageDecayProvedIsFalse =
        refl
    ; calderonZygmundKernelEstimateProvedIsFalse =
        refl
    ; lorentzL3infDependenceProvedIsFalse =
        refl
    ; diagonalToAbelCompatibilityProvedIsFalse =
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
-- Contradictions: this boundary alone cannot promote theorem closure.

postulate
  biotSavartShellLocalizationBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  biotSavartShellLocalizationBoundaryDoesNotProveA6 :
    triadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  biotSavartShellLocalizationBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  biotSavartShellLocalizationBoundaryDoesNotProveTerminalUnification :
    terminalUnificationPromoted ≡ true →
    ⊥
