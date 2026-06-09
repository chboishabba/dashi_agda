module DASHI.Physics.Closure.NSAbelShellMixingLLNBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as Pointwise
import DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary
  as Arcsine

------------------------------------------------------------------------
-- NS A6 Abel shell mixing / LLN boundary.
--
-- This module isolates the mixing subtheorem inside the hard
-- pointwise-to-Abel averaging step:
--
--   localized pointwise stretching
--     ∫ (ω · Sω) φ
--
--   is decomposed into dyadic shell/triadic contributions, and the Abel
--   log-window mean should approximate the shell expectation with an
--   O(N^-1/2) effective-sample error once the true Leray cascade supplies
--   adequate decorrelation/mixing.
--
-- This receipt records the Abel window length, effective sample count,
-- mixing and independence assumptions, O(N^-1/2) target, blockers, and
-- false proof/residual/Clay/terminal flags.  It does not prove the LLN,
-- does not prove the pointwise-to-Abel replacement theorem, and does not
-- promote Navier-Stokes Clay.

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
-- Imported support surfaces.

pointwiseBoundaryReference : String
pointwiseBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

arcsineBoundaryReference : String
arcsineBoundaryReference =
  "DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary"

pointwiseBoundaryImported : Bool
pointwiseBoundaryImported =
  true

arcsineBoundaryImported : Bool
arcsineBoundaryImported =
  true

record ImportedAbelShellMixingSupport : Set where
  field
    pointwiseBoundary :
      Pointwise.NSPointwiseToAbelAveragingBoundary
    pointwiseBoundaryIsCanonical :
      pointwiseBoundary
        ≡ Pointwise.canonicalNSPointwiseToAbelAveragingBoundary
    arcsineBoundary :
      Arcsine.NSCascadeKappaArcsineLawBoundary
    arcsineBoundaryIsCanonical :
      arcsineBoundary
        ≡ Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    pointwiseBoundaryImportedIsTrue :
      pointwiseBoundaryImported ≡ true
    arcsineBoundaryImportedIsTrue :
      arcsineBoundaryImported ≡ true

canonicalImportedAbelShellMixingSupport :
  ImportedAbelShellMixingSupport
canonicalImportedAbelShellMixingSupport =
  record
    { pointwiseBoundary =
        Pointwise.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseBoundaryIsCanonical =
        refl
    ; arcsineBoundary =
        Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    ; arcsineBoundaryIsCanonical =
        refl
    ; pointwiseBoundaryImportedIsTrue =
        refl
    ; arcsineBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Abel log-window and effective-sample structure.

data AbelWindowScaleClause : Set where
  residualCenter-jrTracksLogOneOverR :
    AbelWindowScaleClause
  windowLength-N-tendsToInfinity :
    AbelWindowScaleClause
  windowLength-N-isSmallRelativeToCenter :
    AbelWindowScaleClause
  abelWeightsAreNonnegative :
    AbelWindowScaleClause
  abelWeightsAreNormalized :
    AbelWindowScaleClause
  windowTailsAreExponentiallySuppressed :
    AbelWindowScaleClause
  endpointsDoNotCarryMacroscopicMass :
    AbelWindowScaleClause
  sameWindowUsedForPointwiseAndTriadicMeans :
    AbelWindowScaleClause

canonicalAbelWindowScaleClauses : List AbelWindowScaleClause
canonicalAbelWindowScaleClauses =
  residualCenter-jrTracksLogOneOverR
  ∷ windowLength-N-tendsToInfinity
  ∷ windowLength-N-isSmallRelativeToCenter
  ∷ abelWeightsAreNonnegative
  ∷ abelWeightsAreNormalized
  ∷ windowTailsAreExponentiallySuppressed
  ∷ endpointsDoNotCarryMacroscopicMass
  ∷ sameWindowUsedForPointwiseAndTriadicMeans
  ∷ []

abelWindowScaleClauseCount : Nat
abelWindowScaleClauseCount =
  listLength canonicalAbelWindowScaleClauses

abelWindowScaleClauseCountIs8 :
  abelWindowScaleClauseCount ≡ 8
abelWindowScaleClauseCountIs8 =
  refl

abelWindowLengthText : String
abelWindowLengthText =
  "Use N = N(r) dyadic shell samples in an Abel/log window centered at j_r ~= log_2(1/r), with N -> infinity and N / j_r -> 0."

data EffectiveSampleClause : Set where
  rawWindowHasNObservations :
    EffectiveSampleClause
  correlationLengthIsFiniteOrSummable :
    EffectiveSampleClause
  effectiveSampleCountComparableToN :
    EffectiveSampleClause
  badCorrelationsReduceEffectiveSampleCount :
    EffectiveSampleClause
  varianceScalesLikeOneOverEffectiveN :
    EffectiveSampleClause
  biasErrorSeparatedFromVarianceError :
    EffectiveSampleClause
  stationarityDefectAddedLinearly :
    EffectiveSampleClause

canonicalEffectiveSampleClauses : List EffectiveSampleClause
canonicalEffectiveSampleClauses =
  rawWindowHasNObservations
  ∷ correlationLengthIsFiniteOrSummable
  ∷ effectiveSampleCountComparableToN
  ∷ badCorrelationsReduceEffectiveSampleCount
  ∷ varianceScalesLikeOneOverEffectiveN
  ∷ biasErrorSeparatedFromVarianceError
  ∷ stationarityDefectAddedLinearly
  ∷ []

effectiveSampleClauseCount : Nat
effectiveSampleClauseCount =
  listLength canonicalEffectiveSampleClauses

effectiveSampleClauseCountIs7 :
  effectiveSampleClauseCount ≡ 7
effectiveSampleClauseCountIs7 =
  refl

effectiveSampleCountText : String
effectiveSampleCountText =
  "N_eff is the number of effectively independent shell-triad samples after summable shell-correlation loss; target N_eff >= c N."

------------------------------------------------------------------------
-- Mixing and independence assumptions needed before LLN promotion.

data MixingAssumption : Set where
  shellCorrelationFunctionSummable :
    MixingAssumption
  adjacentShellDependenceLocalized :
    MixingAssumption
  distantShellBlocksDecorrelate :
    MixingAssumption
  lerayCascadeDoesNotCreateLongRangeShellLocking :
    MixingAssumption
  localizedCutoffCommutatorsDoNotDestroyMixing :
    MixingAssumption
  pressureProjectionCommutatorsAreErrorTerms :
    MixingAssumption
  typeIOrAncientRescalingSuppliesUniformMixingWindow :
    MixingAssumption
  approximateTransferStationarityProvidesNoDrift :
    MixingAssumption

canonicalMixingAssumptions : List MixingAssumption
canonicalMixingAssumptions =
  shellCorrelationFunctionSummable
  ∷ adjacentShellDependenceLocalized
  ∷ distantShellBlocksDecorrelate
  ∷ lerayCascadeDoesNotCreateLongRangeShellLocking
  ∷ localizedCutoffCommutatorsDoNotDestroyMixing
  ∷ pressureProjectionCommutatorsAreErrorTerms
  ∷ typeIOrAncientRescalingSuppliesUniformMixingWindow
  ∷ approximateTransferStationarityProvidesNoDrift
  ∷ []

mixingAssumptionCount : Nat
mixingAssumptionCount =
  listLength canonicalMixingAssumptions

mixingAssumptionCountIs8 :
  mixingAssumptionCount ≡ 8
mixingAssumptionCountIs8 =
  refl

data IndependenceAssumption : Set where
  kappaArcsineBaselineAvailable :
    IndependenceAssumption
  lambdaKappaIndependenceAtTransferOutput :
    IndependenceAssumption
  shellBlockKappaSamplesAsymptoticallyIndependent :
    IndependenceAssumption
  diagonalTriadsIndependentAfterBlockSplitting :
    IndependenceAssumption
  offDiagonalTriadsHaveZeroMeanOrAbsorbableMean :
    IndependenceAssumption
  independenceIsOnlyAsymptoticNotPointwise :
    IndependenceAssumption
  correlatedCounterexamplesRemainAdmissibilityBlockers :
    IndependenceAssumption

canonicalIndependenceAssumptions : List IndependenceAssumption
canonicalIndependenceAssumptions =
  kappaArcsineBaselineAvailable
  ∷ lambdaKappaIndependenceAtTransferOutput
  ∷ shellBlockKappaSamplesAsymptoticallyIndependent
  ∷ diagonalTriadsIndependentAfterBlockSplitting
  ∷ offDiagonalTriadsHaveZeroMeanOrAbsorbableMean
  ∷ independenceIsOnlyAsymptoticNotPointwise
  ∷ correlatedCounterexamplesRemainAdmissibilityBlockers
  ∷ []

independenceAssumptionCount : Nat
independenceAssumptionCount =
  listLength canonicalIndependenceAssumptions

independenceAssumptionCountIs7 :
  independenceAssumptionCount ≡ 7
independenceAssumptionCountIs7 =
  refl

mixingAssumptionText : String
mixingAssumptionText =
  "The Abel LLN needs summable shell correlations and asymptotic lambda/kappa block independence; finite arcsine law alone is not enough."

------------------------------------------------------------------------
-- LLN target, variance proxy, and error budget.

data LLNErrorTerm : Set where
  inverseSquareRootEffectiveSampleError :
    LLNErrorTerm
  stationarityDefect-delta-r :
    LLNErrorTerm
  finiteWindowEndpointError :
    LLNErrorTerm
  shellTailTruncationError :
    LLNErrorTerm
  localizationCommutatorError :
    LLNErrorTerm
  pressureLerayCommutatorError :
    LLNErrorTerm
  offDiagonalAbsorptionError :
    LLNErrorTerm
  boundedMassNormalizationError :
    LLNErrorTerm

canonicalLLNErrorTerms : List LLNErrorTerm
canonicalLLNErrorTerms =
  inverseSquareRootEffectiveSampleError
  ∷ stationarityDefect-delta-r
  ∷ finiteWindowEndpointError
  ∷ shellTailTruncationError
  ∷ localizationCommutatorError
  ∷ pressureLerayCommutatorError
  ∷ offDiagonalAbsorptionError
  ∷ boundedMassNormalizationError
  ∷ []

llnErrorTermCount : Nat
llnErrorTermCount =
  listLength canonicalLLNErrorTerms

llnErrorTermCountIs8 :
  llnErrorTermCount ≡ 8
llnErrorTermCountIs8 =
  refl

oNMinusOneHalfProxyTargetText : String
oNMinusOneHalfProxyTargetText =
  "Target: || AbelWindowMean(pointwise shell stretching) - TriadicExpectation || <= C N_eff^(-1/2) + delta_r + commutator/tail errors."

varianceProxyText : String
varianceProxyText =
  "Variance proxy: Var_N <= C / N_eff, using arcsine E(kappa^2)=1/2 and finite lambda^2 scale 11/60 inherited from the finite cascade package."

data LLNPromotionGate : Set where
  proveSummableShellCorrelation :
    LLNPromotionGate
  proveEffectiveSampleLowerBound :
    LLNPromotionGate
  proveDiagonalTriadicIdentification :
    LLNPromotionGate
  proveOffDiagonalAbsorption :
    LLNPromotionGate
  proveLocalizedCommutatorSmallness :
    LLNPromotionGate
  provePressureCommutatorSmallness :
    LLNPromotionGate
  proveStationarityDefectGoesToZero :
    LLNPromotionGate
  proveUniformIntegrabilityForAbelMeans :
    LLNPromotionGate

canonicalLLNPromotionGates : List LLNPromotionGate
canonicalLLNPromotionGates =
  proveSummableShellCorrelation
  ∷ proveEffectiveSampleLowerBound
  ∷ proveDiagonalTriadicIdentification
  ∷ proveOffDiagonalAbsorption
  ∷ proveLocalizedCommutatorSmallness
  ∷ provePressureCommutatorSmallness
  ∷ proveStationarityDefectGoesToZero
  ∷ proveUniformIntegrabilityForAbelMeans
  ∷ []

llnPromotionGateCount : Nat
llnPromotionGateCount =
  listLength canonicalLLNPromotionGates

llnPromotionGateCountIs8 :
  llnPromotionGateCount ≡ 8
llnPromotionGateCountIs8 =
  refl

------------------------------------------------------------------------
-- Blockers and explicit non-claims.

data AbelShellMixingBlocker : Set where
  finiteArcsineLawDoesNotProvePDEMixing :
    AbelShellMixingBlocker
  transferStationarityStillNeeded :
    AbelShellMixingBlocker
  diagonalIdentificationStillNeeded :
    AbelShellMixingBlocker
  offDiagonalCrossTermsStillNeedAbsorption :
    AbelShellMixingBlocker
  localizedCutoffCanCreateCommutatorErrors :
    AbelShellMixingBlocker
  lerayProjectionPressureCanCreateNonlocalErrors :
    AbelShellMixingBlocker
  correlatedTriadCounterexamplesMustBeExcluded :
    AbelShellMixingBlocker
  pointwiseStretchingHasNoTriadwiseSign :
    AbelShellMixingBlocker
  cknResidualDepletionStillDownstream :
    AbelShellMixingBlocker

canonicalAbelShellMixingBlockers : List AbelShellMixingBlocker
canonicalAbelShellMixingBlockers =
  finiteArcsineLawDoesNotProvePDEMixing
  ∷ transferStationarityStillNeeded
  ∷ diagonalIdentificationStillNeeded
  ∷ offDiagonalCrossTermsStillNeedAbsorption
  ∷ localizedCutoffCanCreateCommutatorErrors
  ∷ lerayProjectionPressureCanCreateNonlocalErrors
  ∷ correlatedTriadCounterexamplesMustBeExcluded
  ∷ pointwiseStretchingHasNoTriadwiseSign
  ∷ cknResidualDepletionStillDownstream
  ∷ []

abelShellMixingBlockerCount : Nat
abelShellMixingBlockerCount =
  listLength canonicalAbelShellMixingBlockers

abelShellMixingBlockerCountIs9 :
  abelShellMixingBlockerCount ≡ 9
abelShellMixingBlockerCountIs9 =
  refl

noPointwiseSignText : String
noPointwiseSignText =
  "This LLN target is global/statistical across Abel shell blocks; it does not assert pointwise triad sign or pointwise negative stretching."

blockerSummaryText : String
blockerSummaryText =
  "The remaining theorem is a PDE mixing/LLN estimate, not another finite S2 cascade calculation."

------------------------------------------------------------------------
-- Boundary and promotion booleans.

boundaryRecorded : Bool
boundaryRecorded =
  true

abelWindowRecorded : Bool
abelWindowRecorded =
  true

effectiveSampleRecorded : Bool
effectiveSampleRecorded =
  true

mixingAssumptionsRecorded : Bool
mixingAssumptionsRecorded =
  true

llnErrorTargetRecorded : Bool
llnErrorTargetRecorded =
  true

abelShellMixingLLNProved : Bool
abelShellMixingLLNProved =
  false

pointwiseToAbelAveragingProved : Bool
pointwiseToAbelAveragingProved =
  false

triadicCompensatedLeakageProved : Bool
triadicCompensatedLeakageProved =
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
-- Canonical receipt.

record NSAbelShellMixingLLNBoundary : Set where
  field
    importedSupport :
      ImportedAbelShellMixingSupport
    abelWindowClauses :
      List AbelWindowScaleClause
    abelWindowClauseCountProof :
      abelWindowScaleClauseCount ≡ 8
    effectiveSampleClauses :
      List EffectiveSampleClause
    effectiveSampleClauseCountProof :
      effectiveSampleClauseCount ≡ 7
    mixingAssumptions :
      List MixingAssumption
    mixingAssumptionCountProof :
      mixingAssumptionCount ≡ 8
    independenceAssumptions :
      List IndependenceAssumption
    independenceAssumptionCountProof :
      independenceAssumptionCount ≡ 7
    llnErrorTerms :
      List LLNErrorTerm
    llnErrorTermCountProof :
      llnErrorTermCount ≡ 8
    promotionGates :
      List LLNPromotionGate
    promotionGateCountProof :
      llnPromotionGateCount ≡ 8
    blockers :
      List AbelShellMixingBlocker
    blockerCountProof :
      abelShellMixingBlockerCount ≡ 9
    abelWindowLength :
      String
    effectiveSampleCount :
      String
    mixingAssumption :
      String
    oNMinusOneHalfProxyTarget :
      String
    varianceProxy :
      String
    noPointwiseSign :
      String
    blockerSummary :
      String
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    abelWindowRecordedIsTrue :
      abelWindowRecorded ≡ true
    effectiveSampleRecordedIsTrue :
      effectiveSampleRecorded ≡ true
    mixingAssumptionsRecordedIsTrue :
      mixingAssumptionsRecorded ≡ true
    llnErrorTargetRecordedIsTrue :
      llnErrorTargetRecorded ≡ true
    abelShellMixingLLNProvedIsFalse :
      abelShellMixingLLNProved ≡ false
    pointwiseToAbelAveragingProvedIsFalse :
      pointwiseToAbelAveragingProved ≡ false
    triadicCompensatedLeakageProvedIsFalse :
      triadicCompensatedLeakageProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSAbelShellMixingLLNBoundary :
  NSAbelShellMixingLLNBoundary
canonicalNSAbelShellMixingLLNBoundary =
  record
    { importedSupport =
        canonicalImportedAbelShellMixingSupport
    ; abelWindowClauses =
        canonicalAbelWindowScaleClauses
    ; abelWindowClauseCountProof =
        refl
    ; effectiveSampleClauses =
        canonicalEffectiveSampleClauses
    ; effectiveSampleClauseCountProof =
        refl
    ; mixingAssumptions =
        canonicalMixingAssumptions
    ; mixingAssumptionCountProof =
        refl
    ; independenceAssumptions =
        canonicalIndependenceAssumptions
    ; independenceAssumptionCountProof =
        refl
    ; llnErrorTerms =
        canonicalLLNErrorTerms
    ; llnErrorTermCountProof =
        refl
    ; promotionGates =
        canonicalLLNPromotionGates
    ; promotionGateCountProof =
        refl
    ; blockers =
        canonicalAbelShellMixingBlockers
    ; blockerCountProof =
        refl
    ; abelWindowLength =
        abelWindowLengthText
    ; effectiveSampleCount =
        effectiveSampleCountText
    ; mixingAssumption =
        mixingAssumptionText
    ; oNMinusOneHalfProxyTarget =
        oNMinusOneHalfProxyTargetText
    ; varianceProxy =
        varianceProxyText
    ; noPointwiseSign =
        noPointwiseSignText
    ; blockerSummary =
        blockerSummaryText
    ; boundaryRecordedIsTrue =
        refl
    ; abelWindowRecordedIsTrue =
        refl
    ; effectiveSampleRecordedIsTrue =
        refl
    ; mixingAssumptionsRecordedIsTrue =
        refl
    ; llnErrorTargetRecordedIsTrue =
        refl
    ; abelShellMixingLLNProvedIsFalse =
        refl
    ; pointwiseToAbelAveragingProvedIsFalse =
        refl
    ; triadicCompensatedLeakageProvedIsFalse =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalUnificationPromotedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this boundary cannot be used as a promotion witness.

postulate
  abelShellMixingBoundaryDoesNotProveLLN :
    abelShellMixingLLNProved ≡ true →
    ⊥

  abelShellMixingBoundaryDoesNotProvePointwiseToAbel :
    pointwiseToAbelAveragingProved ≡ true →
    ⊥

  abelShellMixingBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  abelShellMixingBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  abelShellMixingBoundaryDoesNotProveTerminal :
    terminalUnificationPromoted ≡ true →
    ⊥
