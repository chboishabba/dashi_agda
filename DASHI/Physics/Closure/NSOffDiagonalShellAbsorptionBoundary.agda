module DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as PointwiseToAbel
import DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary
  as Shell

------------------------------------------------------------------------
-- NS A6 off-diagonal shell absorption boundary.
--
-- This module records the fail-closed analytic target for the
-- off-diagonal part of TriadicCompensatedLeakageIdentity.  It is narrower
-- than NSPointwiseToAbelAveragingBoundary:
--
--   after the localized stretching term is decomposed into diagonal,
--   near-diagonal, high-low, high-high, pressure/Leray, and cutoff
--   commutator pieces, every off-diagonal piece must be absorbed into
--
--     epsilon * localized dissipation
--       + lower-order critical residual
--       + Abel-window tail / shell-orthogonality error.
--
-- The receipt imports the broad A6 pointwise-to-Abel boundary and the A2
-- shell Bernstein/Hölder target.  It deliberately does not prove
-- Coifman-Meyer bounds, does not prove paraproduct summability, does not
-- prove localized Leray commutator control, and does not promote NS Clay.

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

triadicShellBernsteinHolderBoundaryReference : String
triadicShellBernsteinHolderBoundaryReference =
  "DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary"

pointwiseToAbelBoundaryImported : Bool
pointwiseToAbelBoundaryImported =
  true

triadicShellBernsteinHolderBoundaryImported : Bool
triadicShellBernsteinHolderBoundaryImported =
  true

record ImportedOffDiagonalAbsorptionSupport : Set where
  field
    pointwiseToAbelBoundary :
      PointwiseToAbel.NSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    shellEstimateTarget :
      Shell.TightTriadicShellEstimateTarget
    shellEstimateTargetIsCanonical :
      shellEstimateTarget
        ≡ Shell.canonicalTightTriadicShellEstimateTarget
    pointwiseToAbelBoundaryImportedIsTrue :
      pointwiseToAbelBoundaryImported ≡ true
    triadicShellBernsteinHolderBoundaryImportedIsTrue :
      triadicShellBernsteinHolderBoundaryImported ≡ true

canonicalImportedOffDiagonalAbsorptionSupport :
  ImportedOffDiagonalAbsorptionSupport
canonicalImportedOffDiagonalAbsorptionSupport =
  record
    { pointwiseToAbelBoundary =
        PointwiseToAbel.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; shellEstimateTarget =
        Shell.canonicalTightTriadicShellEstimateTarget
    ; shellEstimateTargetIsCanonical =
        refl
    ; pointwiseToAbelBoundaryImportedIsTrue =
        refl
    ; triadicShellBernsteinHolderBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Off-diagonal term taxonomy.

data OffDiagonalShellRegime : Set where
  highLowVelocityLowVorticity :
    OffDiagonalShellRegime
  lowHighVelocityHighVorticity :
    OffDiagonalShellRegime
  highHighSeparatedInputShells :
    OffDiagonalShellRegime
  highHighSeparatedOutputShell :
    OffDiagonalShellRegime
  nearDiagonalButOutputOffWindow :
    OffDiagonalShellRegime
  farSeparatedCommutatorTail :
    OffDiagonalShellRegime
  pressureLerayOffDiagonalTail :
    OffDiagonalShellRegime
  timeCutoffOffDiagonalTail :
    OffDiagonalShellRegime

canonicalOffDiagonalShellRegimes : List OffDiagonalShellRegime
canonicalOffDiagonalShellRegimes =
  highLowVelocityLowVorticity
  ∷ lowHighVelocityHighVorticity
  ∷ highHighSeparatedInputShells
  ∷ highHighSeparatedOutputShell
  ∷ nearDiagonalButOutputOffWindow
  ∷ farSeparatedCommutatorTail
  ∷ pressureLerayOffDiagonalTail
  ∷ timeCutoffOffDiagonalTail
  ∷ []

offDiagonalShellRegimeCount : Nat
offDiagonalShellRegimeCount =
  listLength canonicalOffDiagonalShellRegimes

offDiagonalShellRegimeCountIs8 :
  offDiagonalShellRegimeCount ≡ 8
offDiagonalShellRegimeCountIs8 =
  refl

data OffDiagonalContribution : Set where
  paraproduct-P-low-u-dot-grad-P-high-omega :
    OffDiagonalContribution
  paraproduct-P-high-u-dot-grad-P-low-omega :
    OffDiagonalContribution
  highHighToLowRemainder :
    OffDiagonalContribution
  highHighToHighOffWindowRemainder :
    OffDiagonalContribution
  lerayProjectionPressureCommutator :
    OffDiagonalContribution
  localizedCutoffCommutator :
    OffDiagonalContribution
  abelWindowTailInteraction :
    OffDiagonalContribution
  shellRecenterDriftInteraction :
    OffDiagonalContribution
  nonresonantTriadicOutputInteraction :
    OffDiagonalContribution

canonicalOffDiagonalContributions : List OffDiagonalContribution
canonicalOffDiagonalContributions =
  paraproduct-P-low-u-dot-grad-P-high-omega
  ∷ paraproduct-P-high-u-dot-grad-P-low-omega
  ∷ highHighToLowRemainder
  ∷ highHighToHighOffWindowRemainder
  ∷ lerayProjectionPressureCommutator
  ∷ localizedCutoffCommutator
  ∷ abelWindowTailInteraction
  ∷ shellRecenterDriftInteraction
  ∷ nonresonantTriadicOutputInteraction
  ∷ []

offDiagonalContributionCount : Nat
offDiagonalContributionCount =
  listLength canonicalOffDiagonalContributions

offDiagonalContributionCountIs9 :
  offDiagonalContributionCount ≡ 9
offDiagonalContributionCountIs9 =
  refl

offDiagonalDecompositionText : String
offDiagonalDecompositionText =
  "omega dot S omega localized by phi is split into diagonal Abel mean plus high-low, low-high, high-high, off-window, Leray-pressure, cutoff, and Abel-tail off-diagonal pieces"

------------------------------------------------------------------------
-- Analytic routes required for absorption.

data AbsorptionRoute : Set where
  dyadicAlmostOrthogonalityForSeparatedShells :
    AbsorptionRoute
  bonyParaproductHighLowAbsorption :
    AbsorptionRoute
  coifmanMeyerNearDiagonalBilinearBound :
    AbsorptionRoute
  trueLeraySymbolCancellationLedger :
    AbsorptionRoute
  localizedLerayProjectionCommutatorBound :
    AbsorptionRoute
  cutoffCommutatorIntegratedByParts :
    AbsorptionRoute
  abelWindowTailSummability :
    AbsorptionRoute
  shellRecenterDriftLowerOrderBound :
    AbsorptionRoute
  pressureTermAbsorbedByCZAndLocalEnergy :
    AbsorptionRoute
  epsilonGradientAbsorption :
    AbsorptionRoute

canonicalAbsorptionRoutes : List AbsorptionRoute
canonicalAbsorptionRoutes =
  dyadicAlmostOrthogonalityForSeparatedShells
  ∷ bonyParaproductHighLowAbsorption
  ∷ coifmanMeyerNearDiagonalBilinearBound
  ∷ trueLeraySymbolCancellationLedger
  ∷ localizedLerayProjectionCommutatorBound
  ∷ cutoffCommutatorIntegratedByParts
  ∷ abelWindowTailSummability
  ∷ shellRecenterDriftLowerOrderBound
  ∷ pressureTermAbsorbedByCZAndLocalEnergy
  ∷ epsilonGradientAbsorption
  ∷ []

absorptionRouteCount : Nat
absorptionRouteCount =
  listLength canonicalAbsorptionRoutes

absorptionRouteCountIs10 :
  absorptionRouteCount ≡ 10
absorptionRouteCountIs10 =
  refl

data CoifmanMeyerAbsorptionTarget : Set where
  uniformDerivativeBoundsForOffDiagonalSymbol :
    CoifmanMeyerAbsorptionTarget
  L2xL2ToL1ShellSummableEstimate :
    CoifmanMeyerAbsorptionTarget
  L3xL3ToLThreeHalvesCriticalEstimate :
    CoifmanMeyerAbsorptionTarget
  nearDiagonalTrueLerayMultiplierBound :
    CoifmanMeyerAbsorptionTarget
  outputShellProjectionBoundIndependentOfCenter :
    CoifmanMeyerAbsorptionTarget
  noImprovedOperatorNormClaim :
    CoifmanMeyerAbsorptionTarget

canonicalCoifmanMeyerAbsorptionTargets :
  List CoifmanMeyerAbsorptionTarget
canonicalCoifmanMeyerAbsorptionTargets =
  uniformDerivativeBoundsForOffDiagonalSymbol
  ∷ L2xL2ToL1ShellSummableEstimate
  ∷ L3xL3ToLThreeHalvesCriticalEstimate
  ∷ nearDiagonalTrueLerayMultiplierBound
  ∷ outputShellProjectionBoundIndependentOfCenter
  ∷ noImprovedOperatorNormClaim
  ∷ []

coifmanMeyerAbsorptionTargetCount : Nat
coifmanMeyerAbsorptionTargetCount =
  listLength canonicalCoifmanMeyerAbsorptionTargets

coifmanMeyerAbsorptionTargetCountIs6 :
  coifmanMeyerAbsorptionTargetCount ≡ 6
coifmanMeyerAbsorptionTargetCountIs6 =
  refl

coifmanMeyerAbsorptionTargetText : String
coifmanMeyerAbsorptionTargetText =
  "Off-diagonal bilinear multipliers are bounded and summable by Coifman-Meyer/LP theory; no strict C-c gain is claimed from the multiplier norm"

------------------------------------------------------------------------
-- Epsilon-gradient and residual absorption budget.

data AbsorptionBudgetTerm : Set where
  epsilonLocalizedGradientVorticity :
    AbsorptionBudgetTerm
  epsilonLocalizedVelocityGradient :
    AbsorptionBudgetTerm
  lowerOrderCriticalResidual :
    AbsorptionBudgetTerm
  abelTailErrorOrderNMinusOne :
    AbsorptionBudgetTerm
  shellMixingErrorOrderNMinusOneHalf :
    AbsorptionBudgetTerm
  cutoffScaleError-rMinusOneTimesEnergy :
    AbsorptionBudgetTerm
  pressureCZLowerOrderError :
    AbsorptionBudgetTerm
  stationarityDefectError-deltaR :
    AbsorptionBudgetTerm

canonicalAbsorptionBudgetTerms : List AbsorptionBudgetTerm
canonicalAbsorptionBudgetTerms =
  epsilonLocalizedGradientVorticity
  ∷ epsilonLocalizedVelocityGradient
  ∷ lowerOrderCriticalResidual
  ∷ abelTailErrorOrderNMinusOne
  ∷ shellMixingErrorOrderNMinusOneHalf
  ∷ cutoffScaleError-rMinusOneTimesEnergy
  ∷ pressureCZLowerOrderError
  ∷ stationarityDefectError-deltaR
  ∷ []

absorptionBudgetTermCount : Nat
absorptionBudgetTermCount =
  listLength canonicalAbsorptionBudgetTerms

absorptionBudgetTermCountIs8 :
  absorptionBudgetTermCount ≡ 8
absorptionBudgetTermCountIs8 =
  refl

epsilonAbsorptionTargetText : String
epsilonAbsorptionTargetText =
  "OffDiagonal <= epsilon * integral |nabla omega|^2 phi + C_epsilon * lower-order residual + Abel tail and stationarity errors"

localizedGradientAbsorptionText : String
localizedGradientAbsorptionText =
  "Every high-frequency off-diagonal derivative must land on a dissipative shell or be converted into a lower-order cutoff/pressure commutator"

------------------------------------------------------------------------
-- Ledger from off-diagonal regimes to intended absorption routes.

data OffDiagonalAbsorptionLedgerRow : Set where
  highLowRowsUseBonyParaproduct :
    OffDiagonalShellRegime →
    AbsorptionRoute →
    OffDiagonalAbsorptionLedgerRow
  highHighRowsUseAlmostOrthogonality :
    OffDiagonalShellRegime →
    AbsorptionRoute →
    OffDiagonalAbsorptionLedgerRow
  nearDiagonalRowsUseCoifmanMeyer :
    OffDiagonalShellRegime →
    AbsorptionRoute →
    OffDiagonalAbsorptionLedgerRow
  pressureRowsUseLerayCommutator :
    OffDiagonalShellRegime →
    AbsorptionRoute →
    OffDiagonalAbsorptionLedgerRow
  cutoffRowsUseIntegratedByParts :
    OffDiagonalShellRegime →
    AbsorptionRoute →
    OffDiagonalAbsorptionLedgerRow
  abelTailRowsUseWindowSummability :
    OffDiagonalShellRegime →
    AbsorptionRoute →
    OffDiagonalAbsorptionLedgerRow

canonicalOffDiagonalAbsorptionLedger :
  List OffDiagonalAbsorptionLedgerRow
canonicalOffDiagonalAbsorptionLedger =
  highLowRowsUseBonyParaproduct
    highLowVelocityLowVorticity
    bonyParaproductHighLowAbsorption
  ∷ highLowRowsUseBonyParaproduct
      lowHighVelocityHighVorticity
      bonyParaproductHighLowAbsorption
  ∷ highHighRowsUseAlmostOrthogonality
      highHighSeparatedInputShells
      dyadicAlmostOrthogonalityForSeparatedShells
  ∷ highHighRowsUseAlmostOrthogonality
      highHighSeparatedOutputShell
      dyadicAlmostOrthogonalityForSeparatedShells
  ∷ nearDiagonalRowsUseCoifmanMeyer
      nearDiagonalButOutputOffWindow
      coifmanMeyerNearDiagonalBilinearBound
  ∷ pressureRowsUseLerayCommutator
      pressureLerayOffDiagonalTail
      localizedLerayProjectionCommutatorBound
  ∷ cutoffRowsUseIntegratedByParts
      farSeparatedCommutatorTail
      cutoffCommutatorIntegratedByParts
  ∷ cutoffRowsUseIntegratedByParts
      timeCutoffOffDiagonalTail
      cutoffCommutatorIntegratedByParts
  ∷ abelTailRowsUseWindowSummability
      nearDiagonalButOutputOffWindow
      abelWindowTailSummability
  ∷ []

offDiagonalAbsorptionLedgerRowCount : Nat
offDiagonalAbsorptionLedgerRowCount =
  listLength canonicalOffDiagonalAbsorptionLedger

offDiagonalAbsorptionLedgerRowCountIs9 :
  offDiagonalAbsorptionLedgerRowCount ≡ 9
offDiagonalAbsorptionLedgerRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Blockers and fail-closed governance.

data NSOffDiagonalShellAbsorptionBlocker : Set where
  missingA2TightTriadicShellEstimate :
    NSOffDiagonalShellAbsorptionBlocker
  missingCoifmanMeyerOffDiagonalSymbolBounds :
    NSOffDiagonalShellAbsorptionBlocker
  missingHighLowParaproductSummability :
    NSOffDiagonalShellAbsorptionBlocker
  missingHighHighAlmostOrthogonalityProof :
    NSOffDiagonalShellAbsorptionBlocker
  missingLocalizedLerayPressureCommutatorProof :
    NSOffDiagonalShellAbsorptionBlocker
  missingCutoffCommutatorIntegrationByParts :
    NSOffDiagonalShellAbsorptionBlocker
  missingEpsilonGradientAbsorptionInequality :
    NSOffDiagonalShellAbsorptionBlocker
  missingPointwiseToAbelDiagonalIdentification :
    NSOffDiagonalShellAbsorptionBlocker
  missingResidualDepletionTransfer :
    NSOffDiagonalShellAbsorptionBlocker
  clayNavierStokesPromotionClosed :
    NSOffDiagonalShellAbsorptionBlocker

canonicalNSOffDiagonalShellAbsorptionBlockers :
  List NSOffDiagonalShellAbsorptionBlocker
canonicalNSOffDiagonalShellAbsorptionBlockers =
  missingA2TightTriadicShellEstimate
  ∷ missingCoifmanMeyerOffDiagonalSymbolBounds
  ∷ missingHighLowParaproductSummability
  ∷ missingHighHighAlmostOrthogonalityProof
  ∷ missingLocalizedLerayPressureCommutatorProof
  ∷ missingCutoffCommutatorIntegrationByParts
  ∷ missingEpsilonGradientAbsorptionInequality
  ∷ missingPointwiseToAbelDiagonalIdentification
  ∷ missingResidualDepletionTransfer
  ∷ clayNavierStokesPromotionClosed
  ∷ []

offDiagonalShellAbsorptionBlockerCount : Nat
offDiagonalShellAbsorptionBlockerCount =
  listLength canonicalNSOffDiagonalShellAbsorptionBlockers

offDiagonalShellAbsorptionBlockerCountIs10 :
  offDiagonalShellAbsorptionBlockerCount ≡ 10
offDiagonalShellAbsorptionBlockerCountIs10 =
  refl

boundaryRecorded : Bool
boundaryRecorded =
  true

importsRecorded : Bool
importsRecorded =
  true

termTaxonomyRecorded : Bool
termTaxonomyRecorded =
  true

absorptionRoutesRecorded : Bool
absorptionRoutesRecorded =
  true

epsilonAbsorptionBudgetRecorded : Bool
epsilonAbsorptionBudgetRecorded =
  true

offDiagonalShellAbsorptionProved : Bool
offDiagonalShellAbsorptionProved =
  false

coifmanMeyerAbsorptionProved : Bool
coifmanMeyerAbsorptionProved =
  false

epsilonGradientAbsorptionProved : Bool
epsilonGradientAbsorptionProved =
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

------------------------------------------------------------------------
-- Compact O/R/C/S/L/P/G/F ledger.

data ORCSLPGFRow : Set where
  O-laneTwoOffDiagonalA6Boundary :
    ORCSLPGFRow
  R-absorbOffDiagonalShellTerms :
    ORCSLPGFRow
  C-importsPointwiseToAbelAndShellEstimate :
    ORCSLPGFRow
  S-failClosedNoAbsorptionProof :
    ORCSLPGFRow
  L-diagonalMeanThenOffDiagonalAbsorptionThenResidual :
    ORCSLPGFRow
  P-proveCoifmanMeyerParaproductCommutatorAbsorption :
    ORCSLPGFRow
  G-noNSClayOrTerminalPromotion :
    ORCSLPGFRow
  F-gapOffDiagonalAnalyticEstimatesRemainOpen :
    ORCSLPGFRow

canonicalORCSLPGFRows : List ORCSLPGFRow
canonicalORCSLPGFRows =
  O-laneTwoOffDiagonalA6Boundary
  ∷ R-absorbOffDiagonalShellTerms
  ∷ C-importsPointwiseToAbelAndShellEstimate
  ∷ S-failClosedNoAbsorptionProof
  ∷ L-diagonalMeanThenOffDiagonalAbsorptionThenResidual
  ∷ P-proveCoifmanMeyerParaproductCommutatorAbsorption
  ∷ G-noNSClayOrTerminalPromotion
  ∷ F-gapOffDiagonalAnalyticEstimatesRemainOpen
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
  "O Lane 2 A6 off-diagonal receipt; R absorb high-low/high-high/off-window/Leray/cutoff shell terms; C imports pointwise-to-Abel and A2 shell targets; S fail-closed; L off-diagonal absorption feeds A6 only after diagonal Abel identification; P prove Coifman-Meyer, paraproduct, commutator, epsilon absorption estimates; G no NS Clay or terminal promotion; F analytic estimates open."

------------------------------------------------------------------------
-- Canonical boundary receipt.

record NSOffDiagonalShellAbsorptionBoundary : Set where
  field
    importedSupport :
      ImportedOffDiagonalAbsorptionSupport
    regimes :
      List OffDiagonalShellRegime
    regimeCountProof :
      offDiagonalShellRegimeCount ≡ 8
    contributions :
      List OffDiagonalContribution
    contributionCountProof :
      offDiagonalContributionCount ≡ 9
    absorptionRoutes :
      List AbsorptionRoute
    absorptionRouteCountProof :
      absorptionRouteCount ≡ 10
    coifmanMeyerTargets :
      List CoifmanMeyerAbsorptionTarget
    coifmanMeyerTargetCountProof :
      coifmanMeyerAbsorptionTargetCount ≡ 6
    budgetTerms :
      List AbsorptionBudgetTerm
    budgetTermCountProof :
      absorptionBudgetTermCount ≡ 8
    absorptionLedger :
      List OffDiagonalAbsorptionLedgerRow
    absorptionLedgerRowCountProof :
      offDiagonalAbsorptionLedgerRowCount ≡ 9
    blockers :
      List NSOffDiagonalShellAbsorptionBlocker
    blockerCountProof :
      offDiagonalShellAbsorptionBlockerCount ≡ 10
    orcsLpgfRows :
      List ORCSLPGFRow
    orcsLpgfRowCountProof :
      orcsLpgfRowCount ≡ 8
    decompositionText :
      String
    coifmanMeyerText :
      String
    epsilonAbsorptionText :
      String
    localizedGradientAbsorption :
      String
    orcsLpgfSummary :
      String
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    importsRecordedIsTrue :
      importsRecorded ≡ true
    termTaxonomyRecordedIsTrue :
      termTaxonomyRecorded ≡ true
    absorptionRoutesRecordedIsTrue :
      absorptionRoutesRecorded ≡ true
    epsilonAbsorptionBudgetRecordedIsTrue :
      epsilonAbsorptionBudgetRecorded ≡ true
    offDiagonalShellAbsorptionProvedIsFalse :
      offDiagonalShellAbsorptionProved ≡ false
    coifmanMeyerAbsorptionProvedIsFalse :
      coifmanMeyerAbsorptionProved ≡ false
    epsilonGradientAbsorptionProvedIsFalse :
      epsilonGradientAbsorptionProved ≡ false
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

canonicalNSOffDiagonalShellAbsorptionBoundary :
  NSOffDiagonalShellAbsorptionBoundary
canonicalNSOffDiagonalShellAbsorptionBoundary =
  record
    { importedSupport =
        canonicalImportedOffDiagonalAbsorptionSupport
    ; regimes =
        canonicalOffDiagonalShellRegimes
    ; regimeCountProof =
        refl
    ; contributions =
        canonicalOffDiagonalContributions
    ; contributionCountProof =
        refl
    ; absorptionRoutes =
        canonicalAbsorptionRoutes
    ; absorptionRouteCountProof =
        refl
    ; coifmanMeyerTargets =
        canonicalCoifmanMeyerAbsorptionTargets
    ; coifmanMeyerTargetCountProof =
        refl
    ; budgetTerms =
        canonicalAbsorptionBudgetTerms
    ; budgetTermCountProof =
        refl
    ; absorptionLedger =
        canonicalOffDiagonalAbsorptionLedger
    ; absorptionLedgerRowCountProof =
        refl
    ; blockers =
        canonicalNSOffDiagonalShellAbsorptionBlockers
    ; blockerCountProof =
        refl
    ; orcsLpgfRows =
        canonicalORCSLPGFRows
    ; orcsLpgfRowCountProof =
        refl
    ; decompositionText =
        offDiagonalDecompositionText
    ; coifmanMeyerText =
        coifmanMeyerAbsorptionTargetText
    ; epsilonAbsorptionText =
        epsilonAbsorptionTargetText
    ; localizedGradientAbsorption =
        localizedGradientAbsorptionText
    ; orcsLpgfSummary =
        canonicalORCSLPGFSummary
    ; boundaryRecordedIsTrue =
        refl
    ; importsRecordedIsTrue =
        refl
    ; termTaxonomyRecordedIsTrue =
        refl
    ; absorptionRoutesRecordedIsTrue =
        refl
    ; epsilonAbsorptionBudgetRecordedIsTrue =
        refl
    ; offDiagonalShellAbsorptionProvedIsFalse =
        refl
    ; coifmanMeyerAbsorptionProvedIsFalse =
        refl
    ; epsilonGradientAbsorptionProvedIsFalse =
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
-- Contradictions: this receipt cannot be used as a proof or promotion.

postulate
  offDiagonalBoundaryDoesNotProveA6 :
    triadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  offDiagonalBoundaryDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  offDiagonalBoundaryDoesNotProveClay :
    clayNavierStokesPromoted ≡ true →
    ⊥

  offDiagonalBoundaryDoesNotProveTerminalUnification :
    terminalUnificationPromoted ≡ true →
    ⊥
