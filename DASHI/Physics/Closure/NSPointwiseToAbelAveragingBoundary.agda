module DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary
  as Arcsine
import DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary
  as Stretching
import DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary
  as Shell
import DASHI.Physics.Closure.NSTypeIBlowupKappaBiasBoundBoundary
  as KappaBias

------------------------------------------------------------------------
-- NS A6 pointwise-to-Abel averaging boundary.
--
-- This module records the hard analytic subtheorem inside
-- TriadicCompensatedLeakageIdentity:
--
--   replace the localized pointwise enstrophy-stretching term
--
--     ∫_{Q_r} (ω · Sω) φ
--
--   by the Abel/shell triadic mean
--
--     ∫ λ(c) (2κ² - 1) dμ_r
--
--   with controlled diagonal, off-diagonal, localization, pressure, and
--   shell-mixing errors.
--
-- The receipt is deliberately fail-closed.  It records the shell weights,
-- diagonal/off-diagonal decomposition, Abel LLN/mixing obligation,
-- local replacement target, and blockers.  It does not prove the Abel LLN,
-- does not prove residual depletion, does not prove local defect
-- monotonicity, and does not promote Navier-Stokes Clay.

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
-- Imported finite and analytic anchors.

arcsineBoundaryReference : String
arcsineBoundaryReference =
  "DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary"

stretchingFormulaBoundaryReference : String
stretchingFormulaBoundaryReference =
  "DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary"

shellBernsteinBoundaryReference : String
shellBernsteinBoundaryReference =
  "DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary"

kappaBiasBoundaryReference : String
kappaBiasBoundaryReference =
  "DASHI.Physics.Closure.NSTypeIBlowupKappaBiasBoundBoundary"

arcsineBoundaryImported : Bool
arcsineBoundaryImported =
  true

stretchingFormulaBoundaryImported : Bool
stretchingFormulaBoundaryImported =
  true

shellBernsteinBoundaryImported : Bool
shellBernsteinBoundaryImported =
  true

kappaBiasBoundaryImported : Bool
kappaBiasBoundaryImported =
  true

record ImportedPointwiseToAbelSupport : Set where
  field
    arcsineBoundary :
      Arcsine.NSCascadeKappaArcsineLawBoundary
    arcsineBoundaryIsCanonical :
      arcsineBoundary ≡ Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    stretchingFormulaBoundary :
      Stretching.NSCoherentStretchingExactFormulaBoundary
    stretchingFormulaBoundaryIsCanonical :
      stretchingFormulaBoundary
        ≡ Stretching.canonicalNSCoherentStretchingExactFormulaBoundary
    shellBernsteinBoundary :
      Shell.TightTriadicShellEstimateTarget
    shellBernsteinBoundaryIsCanonical :
      shellBernsteinBoundary
        ≡ Shell.canonicalTightTriadicShellEstimateTarget
    kappaBiasBoundary :
      KappaBias.NSTypeIBlowupKappaBiasBoundBoundary
    kappaBiasBoundaryIsCanonical :
      kappaBiasBoundary
        ≡ KappaBias.canonicalNSTypeIBlowupKappaBiasBoundBoundary
    arcsineBoundaryImportedIsTrue :
      arcsineBoundaryImported ≡ true
    stretchingFormulaBoundaryImportedIsTrue :
      stretchingFormulaBoundaryImported ≡ true
    shellBernsteinBoundaryImportedIsTrue :
      shellBernsteinBoundaryImported ≡ true
    kappaBiasBoundaryImportedIsTrue :
      kappaBiasBoundaryImported ≡ true

canonicalImportedPointwiseToAbelSupport :
  ImportedPointwiseToAbelSupport
canonicalImportedPointwiseToAbelSupport =
  record
    { arcsineBoundary =
        Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    ; arcsineBoundaryIsCanonical =
        refl
    ; stretchingFormulaBoundary =
        Stretching.canonicalNSCoherentStretchingExactFormulaBoundary
    ; stretchingFormulaBoundaryIsCanonical =
        refl
    ; shellBernsteinBoundary =
        Shell.canonicalTightTriadicShellEstimateTarget
    ; shellBernsteinBoundaryIsCanonical =
        refl
    ; kappaBiasBoundary =
        KappaBias.canonicalNSTypeIBlowupKappaBiasBoundBoundary
    ; kappaBiasBoundaryIsCanonical =
        refl
    ; arcsineBoundaryImportedIsTrue =
        refl
    ; stretchingFormulaBoundaryImportedIsTrue =
        refl
    ; shellBernsteinBoundaryImportedIsTrue =
        refl
    ; kappaBiasBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Shell weights and Abel averaging carrier.

data ShellWeightObject : Set where
  localizedVorticityShell-Pj-omega :
    ShellWeightObject
  shellEnergyWeight-xi-j :
    ShellWeightObject
  normalizedShellWeight-xi-j-over-totalEnstrophy :
    ShellWeightObject
  abelWindowWeight-expMinusAbsJMinusJrOverN :
    ShellWeightObject
  residualScaleDyadicCenter-jr :
    ShellWeightObject
  shellWindowLength-N-about-logOneOverR :
    ShellWeightObject
  localCutoffPhiOnQr :
    ShellWeightObject
  abelTriadicMeasure-mu-r :
    ShellWeightObject

canonicalShellWeightObjects : List ShellWeightObject
canonicalShellWeightObjects =
  localizedVorticityShell-Pj-omega
  ∷ shellEnergyWeight-xi-j
  ∷ normalizedShellWeight-xi-j-over-totalEnstrophy
  ∷ abelWindowWeight-expMinusAbsJMinusJrOverN
  ∷ residualScaleDyadicCenter-jr
  ∷ shellWindowLength-N-about-logOneOverR
  ∷ localCutoffPhiOnQr
  ∷ abelTriadicMeasure-mu-r
  ∷ []

shellWeightObjectCount : Nat
shellWeightObjectCount =
  listLength canonicalShellWeightObjects

shellWeightObjectCountIs8 :
  shellWeightObjectCount ≡ 8
shellWeightObjectCountIs8 =
  refl

shellWeightDefinitionText : String
shellWeightDefinitionText =
  "xi_j(t) = ||P_j omega||_L2(phi)^2 / sum_l ||P_l omega||_L2(phi)^2, Abel-weighted near j_r ~ log(1/r)"

data AbelWindowRequirement : Set where
  finiteMassWindow :
    AbelWindowRequirement
  normalizedNonnegativeWeights :
    AbelWindowRequirement
  logarithmicWindowLengthTendsToInfinity :
    AbelWindowRequirement
  dyadicCenterTracksResidualScale :
    AbelWindowRequirement
  tailsAreSummableUnderTypeIBound :
    AbelWindowRequirement
  shellWeightStabilityUnderOneCascadeStep :
    AbelWindowRequirement

canonicalAbelWindowRequirements : List AbelWindowRequirement
canonicalAbelWindowRequirements =
  finiteMassWindow
  ∷ normalizedNonnegativeWeights
  ∷ logarithmicWindowLengthTendsToInfinity
  ∷ dyadicCenterTracksResidualScale
  ∷ tailsAreSummableUnderTypeIBound
  ∷ shellWeightStabilityUnderOneCascadeStep
  ∷ []

abelWindowRequirementCount : Nat
abelWindowRequirementCount =
  listLength canonicalAbelWindowRequirements

abelWindowRequirementCountIs6 :
  abelWindowRequirementCount ≡ 6
abelWindowRequirementCountIs6 =
  refl

------------------------------------------------------------------------
-- Diagonal/off-diagonal decomposition.

data StretchingDecompositionTerm : Set where
  localizedPointwiseStretching-integral-omega-dot-S-omega-phi :
    StretchingDecompositionTerm
  diagonalShellStretching-sum-j-Pjomega-S-Pjomega :
    StretchingDecompositionTerm
  nearDiagonalTriadicShellInteractions-j-approx-k :
    StretchingDecompositionTerm
  offDiagonalHighLowInteractions-j-far-k :
    StretchingDecompositionTerm
  commutatorWithCutoffPhi :
    StretchingDecompositionTerm
  pressureLerayProjectionRemainder :
    StretchingDecompositionTerm
  transportAndTimeCutoffRemainder :
    StretchingDecompositionTerm
  abelMeanStretchingIntegral-lambda-twoKappaSquaredMinusOne :
    StretchingDecompositionTerm

canonicalStretchingDecompositionTerms :
  List StretchingDecompositionTerm
canonicalStretchingDecompositionTerms =
  localizedPointwiseStretching-integral-omega-dot-S-omega-phi
  ∷ diagonalShellStretching-sum-j-Pjomega-S-Pjomega
  ∷ nearDiagonalTriadicShellInteractions-j-approx-k
  ∷ offDiagonalHighLowInteractions-j-far-k
  ∷ commutatorWithCutoffPhi
  ∷ pressureLerayProjectionRemainder
  ∷ transportAndTimeCutoffRemainder
  ∷ abelMeanStretchingIntegral-lambda-twoKappaSquaredMinusOne
  ∷ []

stretchingDecompositionTermCount : Nat
stretchingDecompositionTermCount =
  listLength canonicalStretchingDecompositionTerms

stretchingDecompositionTermCountIs8 :
  stretchingDecompositionTermCount ≡ 8
stretchingDecompositionTermCountIs8 =
  refl

data DiagonalControlClause : Set where
  diagonalUsesExactStretchingFormula :
    DiagonalControlClause
  diagonalIdentifiesKappaForEachShellTriad :
    DiagonalControlClause
  diagonalWeightsMatchLocalizedEnstrophyWeights :
    DiagonalControlClause
  diagonalErrorControlledByAbelWindowDrift :
    DiagonalControlClause
  diagonalReplacementNotProvedHere :
    DiagonalControlClause

canonicalDiagonalControlClauses : List DiagonalControlClause
canonicalDiagonalControlClauses =
  diagonalUsesExactStretchingFormula
  ∷ diagonalIdentifiesKappaForEachShellTriad
  ∷ diagonalWeightsMatchLocalizedEnstrophyWeights
  ∷ diagonalErrorControlledByAbelWindowDrift
  ∷ diagonalReplacementNotProvedHere
  ∷ []

diagonalControlClauseCount : Nat
diagonalControlClauseCount =
  listLength canonicalDiagonalControlClauses

diagonalControlClauseCountIs5 :
  diagonalControlClauseCount ≡ 5
diagonalControlClauseCountIs5 =
  refl

data OffDiagonalControlClause : Set where
  offDiagonalSeparatedShellsRequireAlmostOrthogonality :
    OffDiagonalControlClause
  offDiagonalNearShellsRequireCoifmanMeyer :
    OffDiagonalControlClause
  offDiagonalHighLowTermsRequireParaproductAbsorption :
    OffDiagonalControlClause
  offDiagonalPressureTermsRequireLerayCommutatorControl :
    OffDiagonalControlClause
  offDiagonalTotalMustBeLowerOrderInCriticalResidual :
    OffDiagonalControlClause
  offDiagonalBoundNotProvedHere :
    OffDiagonalControlClause

canonicalOffDiagonalControlClauses : List OffDiagonalControlClause
canonicalOffDiagonalControlClauses =
  offDiagonalSeparatedShellsRequireAlmostOrthogonality
  ∷ offDiagonalNearShellsRequireCoifmanMeyer
  ∷ offDiagonalHighLowTermsRequireParaproductAbsorption
  ∷ offDiagonalPressureTermsRequireLerayCommutatorControl
  ∷ offDiagonalTotalMustBeLowerOrderInCriticalResidual
  ∷ offDiagonalBoundNotProvedHere
  ∷ []

offDiagonalControlClauseCount : Nat
offDiagonalControlClauseCount =
  listLength canonicalOffDiagonalControlClauses

offDiagonalControlClauseCountIs6 :
  offDiagonalControlClauseCount ≡ 6
offDiagonalControlClauseCountIs6 = refl

------------------------------------------------------------------------
-- Abel LLN / mixing obligation.

data AbelLLNMixingObligation : Set where
  shellKappaVariablesUseCorrectedArcsineLaw :
    AbelLLNMixingObligation
  lambdaKappaIndependenceMustHoldAtAbelScale :
    AbelLLNMixingObligation
  shellInteractionsNeedEffectiveDecorrelation :
    AbelLLNMixingObligation
  varianceShouldDecayAsOneOverWindowLength :
    AbelLLNMixingObligation
  llmErrorTargetIsOrderNMinusOneHalf :
    AbelLLNMixingObligation
  mixingMustSurviveLocalizationCutoff :
    AbelLLNMixingObligation
  noPointwiseSignClaimFromIndividualTriads :
    AbelLLNMixingObligation
  abelLLNNotProvedHere :
    AbelLLNMixingObligation

canonicalAbelLLNMixingObligations : List AbelLLNMixingObligation
canonicalAbelLLNMixingObligations =
  shellKappaVariablesUseCorrectedArcsineLaw
  ∷ lambdaKappaIndependenceMustHoldAtAbelScale
  ∷ shellInteractionsNeedEffectiveDecorrelation
  ∷ varianceShouldDecayAsOneOverWindowLength
  ∷ llmErrorTargetIsOrderNMinusOneHalf
  ∷ mixingMustSurviveLocalizationCutoff
  ∷ noPointwiseSignClaimFromIndividualTriads
  ∷ abelLLNNotProvedHere
  ∷ []

abelLLNMixingObligationCount : Nat
abelLLNMixingObligationCount =
  listLength canonicalAbelLLNMixingObligations

abelLLNMixingObligationCountIs8 :
  abelLLNMixingObligationCount ≡ 8
abelLLNMixingObligationCountIs8 =
  refl

abelLLNTargetText : String
abelLLNTargetText =
  "Pointwise localized stretching equals Abel shell mean plus O(N^{-1/2}) mixing error and lower-order commutators"

noTriadPointwiseSignText : String
noTriadPointwiseSignText =
  "Individual triads need not have a definite sign; the target is an Abel/shell averaging theorem"

------------------------------------------------------------------------
-- Local enstrophy-stretching replacement target.

data LocalReplacementTarget : Set where
  startFromLocalizedVorticityEnstrophyInequality :
    LocalReplacementTarget
  replaceOmegaDotSOmegaByAbelMean :
    LocalReplacementTarget
  useFiniteFormulaLambdaTwoKappaSquaredMinusOne :
    LocalReplacementTarget
  insertKappaBiasBoundAfterStationarity :
    LocalReplacementTarget
  retainEpsilonDissipationAbsorptionTerm :
    LocalReplacementTarget
  retainLowerOrderCutoffAndPressureTerms :
    LocalReplacementTarget
  deriveNegativeResidualCoefficientOnlyAfterA6 :
    LocalReplacementTarget

canonicalLocalReplacementTargets : List LocalReplacementTarget
canonicalLocalReplacementTargets =
  startFromLocalizedVorticityEnstrophyInequality
  ∷ replaceOmegaDotSOmegaByAbelMean
  ∷ useFiniteFormulaLambdaTwoKappaSquaredMinusOne
  ∷ insertKappaBiasBoundAfterStationarity
  ∷ retainEpsilonDissipationAbsorptionTerm
  ∷ retainLowerOrderCutoffAndPressureTerms
  ∷ deriveNegativeResidualCoefficientOnlyAfterA6
  ∷ []

localReplacementTargetCount : Nat
localReplacementTargetCount =
  listLength canonicalLocalReplacementTargets

localReplacementTargetCountIs7 :
  localReplacementTargetCount ≡ 7
localReplacementTargetCountIs7 =
  refl

pointwiseToAbelReplacementTargetText : String
pointwiseToAbelReplacementTargetText =
  "∫_{Q_r} (ω·Sω) φ = (∫ λ(c)(2κ²-1) dμ_r) * Ω_r + error_r"

triadicCompensatedLeakageTargetText : String
triadicCompensatedLeakageTargetText =
  "A6 feeds ∂tΩ_r + 2D_r <= (2 Bias(mu_r) - epsilon0) * LambdaOmega_r + lower-order terms"

data RequiredErrorBudget : Set where
  abelLLNError-O-NMinusOneHalf :
    RequiredErrorBudget
  offDiagonalParaproductLowerOrder :
    RequiredErrorBudget
  lerayPressureCommutatorLowerOrder :
    RequiredErrorBudget
  localizationCutoffLowerOrder :
    RequiredErrorBudget
  stationarityBiasError-deltaR :
    RequiredErrorBudget
  dissipationAbsorptionEpsilon :
    RequiredErrorBudget

canonicalRequiredErrorBudgets : List RequiredErrorBudget
canonicalRequiredErrorBudgets =
  abelLLNError-O-NMinusOneHalf
  ∷ offDiagonalParaproductLowerOrder
  ∷ lerayPressureCommutatorLowerOrder
  ∷ localizationCutoffLowerOrder
  ∷ stationarityBiasError-deltaR
  ∷ dissipationAbsorptionEpsilon
  ∷ []

requiredErrorBudgetCount : Nat
requiredErrorBudgetCount =
  listLength canonicalRequiredErrorBudgets

requiredErrorBudgetCountIs6 :
  requiredErrorBudgetCount ≡ 6
requiredErrorBudgetCountIs6 =
  refl

------------------------------------------------------------------------
-- Blockers and fail-closed status flags.

data PointwiseToAbelBlocker : Set where
  missingAbelLLNMixingTheorem :
    PointwiseToAbelBlocker
  missingDiagonalIdentificationProof :
    PointwiseToAbelBlocker
  missingOffDiagonalAbsorptionProof :
    PointwiseToAbelBlocker
  missingLocalizedLerayCommutatorProof :
    PointwiseToAbelBlocker
  missingA2TightTriadicShellEstimate :
    PointwiseToAbelBlocker
  missingA3StationarityRateAsExecutablePDETheorem :
    PointwiseToAbelBlocker
  missingResidualDepletionAndCKNClosure :
    PointwiseToAbelBlocker

canonicalPointwiseToAbelBlockers : List PointwiseToAbelBlocker
canonicalPointwiseToAbelBlockers =
  missingAbelLLNMixingTheorem
  ∷ missingDiagonalIdentificationProof
  ∷ missingOffDiagonalAbsorptionProof
  ∷ missingLocalizedLerayCommutatorProof
  ∷ missingA2TightTriadicShellEstimate
  ∷ missingA3StationarityRateAsExecutablePDETheorem
  ∷ missingResidualDepletionAndCKNClosure
  ∷ []

pointwiseToAbelBlockerCount : Nat
pointwiseToAbelBlockerCount =
  listLength canonicalPointwiseToAbelBlockers

pointwiseToAbelBlockerCountIs7 :
  pointwiseToAbelBlockerCount ≡ 7
pointwiseToAbelBlockerCountIs7 =
  refl

boundaryRecorded : Bool
boundaryRecorded =
  true

shellWeightsRecorded : Bool
shellWeightsRecorded =
  true

diagonalOffDiagonalDecompositionRecorded : Bool
diagonalOffDiagonalDecompositionRecorded =
  true

abelLLNMixingObligationRecorded : Bool
abelLLNMixingObligationRecorded =
  true

localReplacementTargetRecorded : Bool
localReplacementTargetRecorded =
  true

pointwiseToAbelAveragingProved : Bool
pointwiseToAbelAveragingProved =
  false

abelLLNMixingProved : Bool
abelLLNMixingProved =
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

record NSPointwiseToAbelAveragingBoundary : Set where
  field
    importedSupport :
      ImportedPointwiseToAbelSupport
    shellWeights :
      List ShellWeightObject
    shellWeightCountProof :
      shellWeightObjectCount ≡ 8
    abelWindowRequirements :
      List AbelWindowRequirement
    abelWindowRequirementCountProof :
      abelWindowRequirementCount ≡ 6
    decompositionTerms :
      List StretchingDecompositionTerm
    decompositionTermCountProof :
      stretchingDecompositionTermCount ≡ 8
    diagonalClauses :
      List DiagonalControlClause
    diagonalClauseCountProof :
      diagonalControlClauseCount ≡ 5
    offDiagonalClauses :
      List OffDiagonalControlClause
    offDiagonalClauseCountProof :
      offDiagonalControlClauseCount ≡ 6
    abelLLNObligations :
      List AbelLLNMixingObligation
    abelLLNObligationCountProof :
      abelLLNMixingObligationCount ≡ 8
    localReplacementTargets :
      List LocalReplacementTarget
    localReplacementTargetCountProof :
      localReplacementTargetCount ≡ 7
    errorBudget :
      List RequiredErrorBudget
    errorBudgetCountProof :
      requiredErrorBudgetCount ≡ 6
    blockers :
      List PointwiseToAbelBlocker
    blockerCountProof :
      pointwiseToAbelBlockerCount ≡ 7
    shellWeightDefinition :
      String
    abelLLNTarget :
      String
    noPointwiseSignClaim :
      String
    replacementTarget :
      String
    compensatedLeakageTarget :
      String
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    shellWeightsRecordedIsTrue :
      shellWeightsRecorded ≡ true
    decompositionRecordedIsTrue :
      diagonalOffDiagonalDecompositionRecorded ≡ true
    abelLLNMixingObligationRecordedIsTrue :
      abelLLNMixingObligationRecorded ≡ true
    localReplacementTargetRecordedIsTrue :
      localReplacementTargetRecorded ≡ true
    pointwiseToAbelAveragingProvedIsFalse :
      pointwiseToAbelAveragingProved ≡ false
    abelLLNMixingProvedIsFalse :
      abelLLNMixingProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    fullLocalDefectMonotonicityProvedIsFalse :
      fullLocalDefectMonotonicityProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSPointwiseToAbelAveragingBoundary :
  NSPointwiseToAbelAveragingBoundary
canonicalNSPointwiseToAbelAveragingBoundary =
  record
    { importedSupport =
        canonicalImportedPointwiseToAbelSupport
    ; shellWeights =
        canonicalShellWeightObjects
    ; shellWeightCountProof =
        refl
    ; abelWindowRequirements =
        canonicalAbelWindowRequirements
    ; abelWindowRequirementCountProof =
        refl
    ; decompositionTerms =
        canonicalStretchingDecompositionTerms
    ; decompositionTermCountProof =
        refl
    ; diagonalClauses =
        canonicalDiagonalControlClauses
    ; diagonalClauseCountProof =
        refl
    ; offDiagonalClauses =
        canonicalOffDiagonalControlClauses
    ; offDiagonalClauseCountProof =
        refl
    ; abelLLNObligations =
        canonicalAbelLLNMixingObligations
    ; abelLLNObligationCountProof =
        refl
    ; localReplacementTargets =
        canonicalLocalReplacementTargets
    ; localReplacementTargetCountProof =
        refl
    ; errorBudget =
        canonicalRequiredErrorBudgets
    ; errorBudgetCountProof =
        refl
    ; blockers =
        canonicalPointwiseToAbelBlockers
    ; blockerCountProof =
        refl
    ; shellWeightDefinition =
        shellWeightDefinitionText
    ; abelLLNTarget =
        abelLLNTargetText
    ; noPointwiseSignClaim =
        noTriadPointwiseSignText
    ; replacementTarget =
        pointwiseToAbelReplacementTargetText
    ; compensatedLeakageTarget =
        triadicCompensatedLeakageTargetText
    ; boundaryRecordedIsTrue =
        refl
    ; shellWeightsRecordedIsTrue =
        refl
    ; decompositionRecordedIsTrue =
        refl
    ; abelLLNMixingObligationRecordedIsTrue =
        refl
    ; localReplacementTargetRecordedIsTrue =
        refl
    ; pointwiseToAbelAveragingProvedIsFalse =
        refl
    ; abelLLNMixingProvedIsFalse =
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
-- Contradictions: promotions remain impossible from this boundary alone.

postulate
  pointwiseToAbelBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  pointwiseToAbelBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  pointwiseToAbelBoundaryDoesNotProveTerminalUnification :
    terminalUnificationPromoted ≡ true →
    ⊥
