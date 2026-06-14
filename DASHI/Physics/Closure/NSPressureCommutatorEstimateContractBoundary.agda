module DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary
  as ErrorBudget
import DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary
  as Localization
import DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary
  as OffDiagonal
import DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary
  as Shell

------------------------------------------------------------------------
-- NS A6 pressure/localization theorem-contract boundary.
--
-- This module records the narrow fail-closed theorem contract for the
-- localized Leray pressure commutator estimate needed by A6.  The target
-- is the analytic package that must bound the localized pressure lane
--
--   [P_j , phi] R_i R_l
--
-- together with local Calderon-Zygmund pressure, harmonic pressure tail,
-- annular cutoff errors, epsilon-gradient absorption, and lower-order
-- residual routing into NSA6ErrorBudgetCompositeBoundary.
--
-- This is a contract boundary only.  It records precise theorem targets
-- and budget ownership.  It does not prove the pressure commutator
-- estimate, does not absorb the pressure tail, does not prove the
-- localization theorem, does not prove the triadic compensated leakage
-- identity, does not promote NS Clay, and does not promote a terminal
-- theorem.

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

localizationPressureCommutatorBoundaryReference : String
localizationPressureCommutatorBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary"

offDiagonalShellAbsorptionBoundaryReference : String
offDiagonalShellAbsorptionBoundaryReference =
  "DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary"

triadicShellBernsteinHolderBoundaryReference : String
triadicShellBernsteinHolderBoundaryReference =
  "DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary"

nsa6ErrorBudgetCompositeBoundaryReference : String
nsa6ErrorBudgetCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary"

localizationPressureCommutatorBoundaryImported : Bool
localizationPressureCommutatorBoundaryImported =
  true

offDiagonalShellAbsorptionBoundaryImported : Bool
offDiagonalShellAbsorptionBoundaryImported =
  true

triadicShellBernsteinHolderBoundaryImported : Bool
triadicShellBernsteinHolderBoundaryImported =
  true

nsa6ErrorBudgetCompositeBoundaryImported : Bool
nsa6ErrorBudgetCompositeBoundaryImported =
  true

record ImportedNSPressureCommutatorEstimateSupport : Set where
  field
    localizationBoundary :
      Localization.NSLocalizationPressureCommutatorBoundary
    localizationBoundaryIsCanonical :
      localizationBoundary
        ≡ Localization.canonicalNSLocalizationPressureCommutatorBoundary
    offDiagonalBoundary :
      OffDiagonal.NSOffDiagonalShellAbsorptionBoundary
    offDiagonalBoundaryIsCanonical :
      offDiagonalBoundary
        ≡ OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    triadicShellTarget :
      Shell.TightTriadicShellEstimateTarget
    triadicShellTargetIsCanonical :
      triadicShellTarget
        ≡ Shell.canonicalTightTriadicShellEstimateTarget
    errorBudgetCompositeBoundary :
      ErrorBudget.NSA6ErrorBudgetCompositeBoundary
    errorBudgetCompositeBoundaryIsCanonical :
      errorBudgetCompositeBoundary
        ≡ ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    localizationPressureCommutatorBoundaryImportedIsTrue :
      localizationPressureCommutatorBoundaryImported ≡ true
    offDiagonalShellAbsorptionBoundaryImportedIsTrue :
      offDiagonalShellAbsorptionBoundaryImported ≡ true
    triadicShellBernsteinHolderBoundaryImportedIsTrue :
      triadicShellBernsteinHolderBoundaryImported ≡ true
    nsa6ErrorBudgetCompositeBoundaryImportedIsTrue :
      nsa6ErrorBudgetCompositeBoundaryImported ≡ true

canonicalImportedNSPressureCommutatorEstimateSupport :
  ImportedNSPressureCommutatorEstimateSupport
canonicalImportedNSPressureCommutatorEstimateSupport =
  record
    { localizationBoundary =
        Localization.canonicalNSLocalizationPressureCommutatorBoundary
    ; localizationBoundaryIsCanonical =
        refl
    ; offDiagonalBoundary =
        OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    ; offDiagonalBoundaryIsCanonical =
        refl
    ; triadicShellTarget =
        Shell.canonicalTightTriadicShellEstimateTarget
    ; triadicShellTargetIsCanonical =
        refl
    ; errorBudgetCompositeBoundary =
        ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    ; errorBudgetCompositeBoundaryIsCanonical =
        refl
    ; localizationPressureCommutatorBoundaryImportedIsTrue =
        refl
    ; offDiagonalShellAbsorptionBoundaryImportedIsTrue =
        refl
    ; triadicShellBernsteinHolderBoundaryImportedIsTrue =
        refl
    ; nsa6ErrorBudgetCompositeBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Localized Leray pressure commutator objects.

data PressureCommutatorOperator : Set where
  dyadicProjection-Pj :
    PressureCommutatorOperator
  spatialCutoff-phi :
    PressureCommutatorOperator
  rieszTransform-Ri :
    PressureCommutatorOperator
  rieszTransform-Rl :
    PressureCommutatorOperator
  lerayPressureOperator-RiRl :
    PressureCommutatorOperator
  cutoffCommutator-PjPhiMinusPhiPj :
    PressureCommutatorOperator
  localizedCommutator-PjPhiRiRlMinusPhiPjRiRl :
    PressureCommutatorOperator
  pressureGradientLocalizedByPhi :
    PressureCommutatorOperator
  shellWindowedPressureProjection :
    PressureCommutatorOperator

canonicalPressureCommutatorOperators :
  List PressureCommutatorOperator
canonicalPressureCommutatorOperators =
  dyadicProjection-Pj
  ∷ spatialCutoff-phi
  ∷ rieszTransform-Ri
  ∷ rieszTransform-Rl
  ∷ lerayPressureOperator-RiRl
  ∷ cutoffCommutator-PjPhiMinusPhiPj
  ∷ localizedCommutator-PjPhiRiRlMinusPhiPjRiRl
  ∷ pressureGradientLocalizedByPhi
  ∷ shellWindowedPressureProjection
  ∷ []

pressureCommutatorOperatorCount : Nat
pressureCommutatorOperatorCount =
  listLength canonicalPressureCommutatorOperators

pressureCommutatorOperatorCountIs9 :
  pressureCommutatorOperatorCount ≡ 9
pressureCommutatorOperatorCountIs9 =
  refl

cutoffRieszCommutatorTargetText : String
cutoffRieszCommutatorTargetText =
  "Target: ||[P_j, phi] R_i R_l f|| localized by Q_r is bounded by epsilon times localized gradient dissipation plus C_epsilon times cutoff-scale lower-order energy and shell-tail residuals"

data CutoffRieszCommutatorRequirement : Set where
  kernelCancellationAgainstCutoffDifference :
    CutoffRieszCommutatorRequirement
  rieszRieszOrderZeroUniformOnShells :
    CutoffRieszCommutatorRequirement
  dyadicProjectionKernelMomentBound :
    CutoffRieszCommutatorRequirement
  cutoffGradientCosts-rMinusOne :
    CutoffRieszCommutatorRequirement
  cutoffLaplacianCosts-rMinusTwo :
    CutoffRieszCommutatorRequirement
  commutatorGainsDistanceFromCoreToAnnulus :
    CutoffRieszCommutatorRequirement
  noPointwisePositivePressureClaim :
    CutoffRieszCommutatorRequirement
  estimateStableUnderShellRecentering :
    CutoffRieszCommutatorRequirement

canonicalCutoffRieszCommutatorRequirements :
  List CutoffRieszCommutatorRequirement
canonicalCutoffRieszCommutatorRequirements =
  kernelCancellationAgainstCutoffDifference
  ∷ rieszRieszOrderZeroUniformOnShells
  ∷ dyadicProjectionKernelMomentBound
  ∷ cutoffGradientCosts-rMinusOne
  ∷ cutoffLaplacianCosts-rMinusTwo
  ∷ commutatorGainsDistanceFromCoreToAnnulus
  ∷ noPointwisePositivePressureClaim
  ∷ estimateStableUnderShellRecentering
  ∷ []

cutoffRieszCommutatorRequirementCount : Nat
cutoffRieszCommutatorRequirementCount =
  listLength canonicalCutoffRieszCommutatorRequirements

cutoffRieszCommutatorRequirementCountIs8 :
  cutoffRieszCommutatorRequirementCount ≡ 8
cutoffRieszCommutatorRequirementCountIs8 =
  refl

------------------------------------------------------------------------
-- Local pressure and tail theorem targets.

data LocalPressureEstimateTarget : Set where
  localCalderonZygmundPressureCore :
    LocalPressureEstimateTarget
  pressureAverageSubtractionOnCylinder :
    LocalPressureEstimateTarget
  localizedPressureGradientAsDivergenceError :
    LocalPressureEstimateTarget
  pressureCoreControlledByLocalEnergy :
    LocalPressureEstimateTarget
  shellLocalizedCZBoundUniformInJ :
    LocalPressureEstimateTarget
  lowFrequencyPressureNormalization :
    LocalPressureEstimateTarget
  criticalScalingNoSupercriticalLoss :
    LocalPressureEstimateTarget
  noGlobalPressureCompactnessClaim :
    LocalPressureEstimateTarget

canonicalLocalPressureEstimateTargets :
  List LocalPressureEstimateTarget
canonicalLocalPressureEstimateTargets =
  localCalderonZygmundPressureCore
  ∷ pressureAverageSubtractionOnCylinder
  ∷ localizedPressureGradientAsDivergenceError
  ∷ pressureCoreControlledByLocalEnergy
  ∷ shellLocalizedCZBoundUniformInJ
  ∷ lowFrequencyPressureNormalization
  ∷ criticalScalingNoSupercriticalLoss
  ∷ noGlobalPressureCompactnessClaim
  ∷ []

localPressureEstimateTargetCount : Nat
localPressureEstimateTargetCount =
  listLength canonicalLocalPressureEstimateTargets

localPressureEstimateTargetCountIs8 :
  localPressureEstimateTargetCount ≡ 8
localPressureEstimateTargetCountIs8 =
  refl

localCalderonZygmundPressureTargetText : String
localCalderonZygmundPressureTargetText =
  "Local CZ pressure target: phi R_i R_l(u_i u_l) is controlled on the core cylinder after subtracting averages, with only localized energy, epsilon-gradient, and NSA6 lower-order budget terms remaining"

data HarmonicPressureTailTarget : Set where
  splitExteriorPressureAsHarmonicTail :
    HarmonicPressureTailTarget
  interiorGradientDecayFromTwoRToR :
    HarmonicPressureTailTarget
  annularKernelTailSummableAcrossDyadicRings :
    HarmonicPressureTailTarget
  harmonicAverageRemovedBeforeCoreEstimate :
    HarmonicPressureTailTarget
  tailConstantIndependentOfOutputShell :
    HarmonicPressureTailTarget
  tailSentToPressureTailBudget :
    HarmonicPressureTailTarget
  noTailAbsorptionWithoutDecayProof :
    HarmonicPressureTailTarget

canonicalHarmonicPressureTailTargets :
  List HarmonicPressureTailTarget
canonicalHarmonicPressureTailTargets =
  splitExteriorPressureAsHarmonicTail
  ∷ interiorGradientDecayFromTwoRToR
  ∷ annularKernelTailSummableAcrossDyadicRings
  ∷ harmonicAverageRemovedBeforeCoreEstimate
  ∷ tailConstantIndependentOfOutputShell
  ∷ tailSentToPressureTailBudget
  ∷ noTailAbsorptionWithoutDecayProof
  ∷ []

harmonicPressureTailTargetCount : Nat
harmonicPressureTailTargetCount =
  listLength canonicalHarmonicPressureTailTargets

harmonicPressureTailTargetCountIs7 :
  harmonicPressureTailTargetCount ≡ 7
harmonicPressureTailTargetCountIs7 =
  refl

harmonicPressureTailTargetText : String
harmonicPressureTailTargetText =
  "Harmonic pressure tail target: exterior pressure is split from the local CZ core, gains interior decay on Q_r, and routes only summable dyadic-annular remnants to the pressure-tail budget"

------------------------------------------------------------------------
-- Annular cutoff error and epsilon-gradient absorption.

data AnnularCutoffErrorTarget : Set where
  spatialCutoffDerivativeSupportedOnAnnulus :
    AnnularCutoffErrorTarget
  temporalCutoffDerivativeSupportedNearParabolicBoundary :
    AnnularCutoffErrorTarget
  pressureTimesGradPhiIsAnnular :
    AnnularCutoffErrorTarget
  dyadicCommutatorKernelSeesCoreAnnulusSeparation :
    AnnularCutoffErrorTarget
  annularFluxControlledByLocalEnergy :
    AnnularCutoffErrorTarget
  annularPressureErrorRoutesToTailBudget :
    AnnularCutoffErrorTarget
  annularCutoffErrorDoesNotEnterCoreAbelMean :
    AnnularCutoffErrorTarget
  noBoundaryTermPromotion :
    AnnularCutoffErrorTarget

canonicalAnnularCutoffErrorTargets :
  List AnnularCutoffErrorTarget
canonicalAnnularCutoffErrorTargets =
  spatialCutoffDerivativeSupportedOnAnnulus
  ∷ temporalCutoffDerivativeSupportedNearParabolicBoundary
  ∷ pressureTimesGradPhiIsAnnular
  ∷ dyadicCommutatorKernelSeesCoreAnnulusSeparation
  ∷ annularFluxControlledByLocalEnergy
  ∷ annularPressureErrorRoutesToTailBudget
  ∷ annularCutoffErrorDoesNotEnterCoreAbelMean
  ∷ noBoundaryTermPromotion
  ∷ []

annularCutoffErrorTargetCount : Nat
annularCutoffErrorTargetCount =
  listLength canonicalAnnularCutoffErrorTargets

annularCutoffErrorTargetCountIs8 :
  annularCutoffErrorTargetCount ≡ 8
annularCutoffErrorTargetCountIs8 =
  refl

annularCutoffErrorTargetText : String
annularCutoffErrorTargetText =
  "Annular cutoff target: every derivative of phi or eta is supported outside the core, priced by r^-1 or r^-2 local energy, and routed to localizationCutoffBudget or pressureTailBudget"

data EpsilonGradientAbsorptionTarget : Set where
  epsilonTimesLocalizedNablaOmegaSquared :
    EpsilonGradientAbsorptionTarget
  epsilonTimesLocalizedNablaUSquared :
    EpsilonGradientAbsorptionTarget
  commutatorDerivativeMovedToDissipation :
    EpsilonGradientAbsorptionTarget
  pressureGradientAbsorbedByDissipation :
    EpsilonGradientAbsorptionTarget
  remainingConstantDependsOnEpsilon :
    EpsilonGradientAbsorptionTarget
  lowerOrderResidualBelowCriticalScale :
    EpsilonGradientAbsorptionTarget
  noAbsorptionAtEpsilonEqualsZero :
    EpsilonGradientAbsorptionTarget

canonicalEpsilonGradientAbsorptionTargets :
  List EpsilonGradientAbsorptionTarget
canonicalEpsilonGradientAbsorptionTargets =
  epsilonTimesLocalizedNablaOmegaSquared
  ∷ epsilonTimesLocalizedNablaUSquared
  ∷ commutatorDerivativeMovedToDissipation
  ∷ pressureGradientAbsorbedByDissipation
  ∷ remainingConstantDependsOnEpsilon
  ∷ lowerOrderResidualBelowCriticalScale
  ∷ noAbsorptionAtEpsilonEqualsZero
  ∷ []

epsilonGradientAbsorptionTargetCount : Nat
epsilonGradientAbsorptionTargetCount =
  listLength canonicalEpsilonGradientAbsorptionTargets

epsilonGradientAbsorptionTargetCountIs7 :
  epsilonGradientAbsorptionTargetCount ≡ 7
epsilonGradientAbsorptionTargetCountIs7 =
  refl

epsilonGradientAbsorptionTargetText : String
epsilonGradientAbsorptionTargetText =
  "Epsilon-gradient target: pressure commutator and cutoff derivatives are bounded by epsilon localized gradient dissipation plus C_epsilon lower-order residuals already owned by the A6 composite budget"

------------------------------------------------------------------------
-- Residual routing into NSA6ErrorBudgetCompositeBoundary.

data PressureResidualRoute : Set where
  routeCutoffCommutatorToLocalizationCutoffBudget :
    PressureResidualRoute
  routeRieszCommutatorToPressureCommutatorBudget :
    PressureResidualRoute
  routeLocalCZResidualToPressureCommutatorBudget :
    PressureResidualRoute
  routeHarmonicTailToPressureTailBudget :
    PressureResidualRoute
  routeAnnularPressureToPressureTailBudget :
    PressureResidualRoute
  routeAnnularCutoffToLocalizationCutoffBudget :
    PressureResidualRoute
  routeEpsilonGradientToOffDiagonalAbsorptionBudget :
    PressureResidualRoute
  routeLowerOrderResidualToAggregateA6Budget :
    PressureResidualRoute

canonicalPressureResidualRoutes :
  List PressureResidualRoute
canonicalPressureResidualRoutes =
  routeCutoffCommutatorToLocalizationCutoffBudget
  ∷ routeRieszCommutatorToPressureCommutatorBudget
  ∷ routeLocalCZResidualToPressureCommutatorBudget
  ∷ routeHarmonicTailToPressureTailBudget
  ∷ routeAnnularPressureToPressureTailBudget
  ∷ routeAnnularCutoffToLocalizationCutoffBudget
  ∷ routeEpsilonGradientToOffDiagonalAbsorptionBudget
  ∷ routeLowerOrderResidualToAggregateA6Budget
  ∷ []

pressureResidualRouteCount : Nat
pressureResidualRouteCount =
  listLength canonicalPressureResidualRoutes

pressureResidualRouteCountIs8 :
  pressureResidualRouteCount ≡ 8
pressureResidualRouteCountIs8 =
  refl

record ErrorBudgetRoutingAnchor : Set where
  field
    localizationCutoffBudgetRow :
      ErrorBudget.NSA6ErrorBudgetTaxonomyRow
    localizationCutoffBudgetRowIsCanonical :
      localizationCutoffBudgetRow
        ≡ ErrorBudget.localizationCutoffBudgetRow
    pressureCommutatorBudgetRow :
      ErrorBudget.NSA6ErrorBudgetTaxonomyRow
    pressureCommutatorBudgetRowIsCanonical :
      pressureCommutatorBudgetRow
        ≡ ErrorBudget.pressureCommutatorBudgetRow
    pressureTailBudgetRow :
      ErrorBudget.NSA6ErrorBudgetTaxonomyRow
    pressureTailBudgetRowIsCanonical :
      pressureTailBudgetRow
        ≡ ErrorBudget.pressureTailBudgetRow
    offDiagonalAbsorptionBudgetRow :
      ErrorBudget.NSA6ErrorBudgetTaxonomyRow
    offDiagonalAbsorptionBudgetRowIsCanonical :
      offDiagonalAbsorptionBudgetRow
        ≡ ErrorBudget.offDiagonalAbsorptionBudgetRow
    aggregateBudgetPromoted :
      ErrorBudget.aggregateErrorBudgetProved ≡ true

canonicalErrorBudgetRoutingAnchor :
  ErrorBudgetRoutingAnchor
canonicalErrorBudgetRoutingAnchor =
  record
    { localizationCutoffBudgetRow =
        ErrorBudget.localizationCutoffBudgetRow
    ; localizationCutoffBudgetRowIsCanonical =
        refl
    ; pressureCommutatorBudgetRow =
        ErrorBudget.pressureCommutatorBudgetRow
    ; pressureCommutatorBudgetRowIsCanonical =
        refl
    ; pressureTailBudgetRow =
        ErrorBudget.pressureTailBudgetRow
    ; pressureTailBudgetRowIsCanonical =
        refl
    ; offDiagonalAbsorptionBudgetRow =
        ErrorBudget.offDiagonalAbsorptionBudgetRow
    ; offDiagonalAbsorptionBudgetRowIsCanonical =
        refl
    ; aggregateBudgetPromoted =
        refl
    }

residualRoutingTargetText : String
residualRoutingTargetText =
  "Residual routing target: cutoff commutators enter localizationCutoffBudget, Riesz/Leray/local-CZ defects enter pressureCommutatorBudget, harmonic and annular pressure tails enter pressureTailBudget, epsilon-gradient terms are matched to offDiagonalAbsorptionBudget, and aggregate A6 is promoted while downstream residual depletion remains guarded"

------------------------------------------------------------------------
-- Theorem-contract blockers and non-claim guards.

data NSPressureCommutatorEstimateBlocker : Set where
  missingCutoffRieszCommutatorEstimate :
    NSPressureCommutatorEstimateBlocker
  missingLocalCalderonZygmundPressureEstimate :
    NSPressureCommutatorEstimateBlocker
  missingHarmonicPressureInteriorDecayProof :
    NSPressureCommutatorEstimateBlocker
  missingAnnularCutoffErrorAbsorption :
    NSPressureCommutatorEstimateBlocker
  missingEpsilonGradientAbsorptionProof :
    NSPressureCommutatorEstimateBlocker
  missingUniformDyadicShellSummability :
    NSPressureCommutatorEstimateBlocker
  missingCompatibilityWithTriadicLeakageLedger :
    NSPressureCommutatorEstimateBlocker
  missingCompositeBudgetAggregation :
    NSPressureCommutatorEstimateBlocker
  missingLocalizationTheoremPromotion :
    NSPressureCommutatorEstimateBlocker
  clayAndTerminalPromotionClosed :
    NSPressureCommutatorEstimateBlocker

canonicalNSPressureCommutatorEstimateBlockers :
  List NSPressureCommutatorEstimateBlocker
canonicalNSPressureCommutatorEstimateBlockers =
  missingCutoffRieszCommutatorEstimate
  ∷ missingLocalCalderonZygmundPressureEstimate
  ∷ missingHarmonicPressureInteriorDecayProof
  ∷ missingAnnularCutoffErrorAbsorption
  ∷ missingEpsilonGradientAbsorptionProof
  ∷ missingUniformDyadicShellSummability
  ∷ missingCompatibilityWithTriadicLeakageLedger
  ∷ missingCompositeBudgetAggregation
  ∷ missingLocalizationTheoremPromotion
  ∷ clayAndTerminalPromotionClosed
  ∷ []

nsPressureCommutatorEstimateBlockerCount : Nat
nsPressureCommutatorEstimateBlockerCount =
  listLength canonicalNSPressureCommutatorEstimateBlockers

nsPressureCommutatorEstimateBlockerCountIs10 :
  nsPressureCommutatorEstimateBlockerCount ≡ 10
nsPressureCommutatorEstimateBlockerCountIs10 =
  refl

data NonClaimGuard : Set where
  noPressureCommutatorEstimateClaim :
    NonClaimGuard
  noPressureTailAbsorptionClaim :
    NonClaimGuard
  noLocalizationTheoremClaim :
    NonClaimGuard
  noTriadicCompensatedLeakageIdentityClaim :
    NonClaimGuard
  noAggregateA6BudgetClaim :
    NonClaimGuard
  noNSClayClaim :
    NonClaimGuard
  noTerminalPromotionClaim :
    NonClaimGuard

canonicalNonClaimGuards : List NonClaimGuard
canonicalNonClaimGuards =
  noPressureCommutatorEstimateClaim
  ∷ noPressureTailAbsorptionClaim
  ∷ noLocalizationTheoremClaim
  ∷ noTriadicCompensatedLeakageIdentityClaim
  ∷ noAggregateA6BudgetClaim
  ∷ noNSClayClaim
  ∷ noTerminalPromotionClaim
  ∷ []

nonClaimGuardCount : Nat
nonClaimGuardCount =
  listLength canonicalNonClaimGuards

nonClaimGuardCountIs7 :
  nonClaimGuardCount ≡ 7
nonClaimGuardCountIs7 =
  refl

------------------------------------------------------------------------
-- Explicit fail-closed status flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

importsRecorded : Bool
importsRecorded =
  true

cutoffRieszCommutatorContractRecorded : Bool
cutoffRieszCommutatorContractRecorded =
  true

localCalderonZygmundPressureContractRecorded : Bool
localCalderonZygmundPressureContractRecorded =
  true

harmonicPressureTailContractRecorded : Bool
harmonicPressureTailContractRecorded =
  true

annularCutoffErrorContractRecorded : Bool
annularCutoffErrorContractRecorded =
  true

epsilonGradientAbsorptionContractRecorded : Bool
epsilonGradientAbsorptionContractRecorded =
  true

errorBudgetRoutingRecorded : Bool
errorBudgetRoutingRecorded =
  true

pressureCommutatorEstimateProved : Bool
pressureCommutatorEstimateProved =
  false

pressureTailAbsorbed : Bool
pressureTailAbsorbed =
  false

localizationTheoremProved : Bool
localizationTheoremProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSPressureCommutatorEstimateContractStatus : Set where
  nsPressureCommutatorEstimateContractBoundaryRecorded_noPromotion :
    NSPressureCommutatorEstimateContractStatus

------------------------------------------------------------------------
-- Compact O/R/C/S/L/P/G/F ledger.

data ORCSLPGFRow : Set where
  O-laneOneTuringPressureLocalizationContractBoundary :
    ORCSLPGFRow
  R-recordLocalizedLerayPressureCommutatorTargets :
    ORCSLPGFRow
  C-importLocalizationOffDiagonalTriadicAndErrorBudget :
    ORCSLPGFRow
  S-pressureTailLocalizationTriadicClayTerminalAllFalse :
    ORCSLPGFRow
  L-contractRoutesResidualsIntoNSA6CompositeBudget :
    ORCSLPGFRow
  P-proveCommutatorCZTailAnnulusAndEpsilonAbsorption :
    ORCSLPGFRow
  G-noPromotionBeyondBoundaryContract :
    ORCSLPGFRow
  F-gapPressureLocalizationTheoremsRemainOpen :
    ORCSLPGFRow

canonicalORCSLPGFRows : List ORCSLPGFRow
canonicalORCSLPGFRows =
  O-laneOneTuringPressureLocalizationContractBoundary
  ∷ R-recordLocalizedLerayPressureCommutatorTargets
  ∷ C-importLocalizationOffDiagonalTriadicAndErrorBudget
  ∷ S-pressureTailLocalizationTriadicClayTerminalAllFalse
  ∷ L-contractRoutesResidualsIntoNSA6CompositeBudget
  ∷ P-proveCommutatorCZTailAnnulusAndEpsilonAbsorption
  ∷ G-noPromotionBeyondBoundaryContract
  ∷ F-gapPressureLocalizationTheoremsRemainOpen
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
  "O Lane 1 Turing NS A6 pressure/localization theorem-contract boundary; R record [P_j,phi] R_i R_l, local CZ pressure, harmonic pressure tail, annular cutoff error, epsilon-gradient absorption, and residual budget routing; C imports localization, off-diagonal absorption, triadic shell target, and NSA6 error-budget composite boundaries; S pressureCommutatorEstimateProved=false, pressureTailAbsorbed=false, localizationTheoremProved=false, triadicCompensatedLeakageIdentityProved=false, nsClayPromoted=false, terminalPromotion=false; L residuals route into localizationCutoffBudget, pressureCommutatorBudget, pressureTailBudget, and offDiagonalAbsorptionBudget before aggregate A6; P prove commutator, CZ, tail decay, annular cutoff, epsilon absorption, and budget aggregation; G no theorem or terminal promotion; F analytic pressure/localization theorems remain open."

nsPressureCommutatorEstimateContractSummary : String
nsPressureCommutatorEstimateContractSummary =
  "Records the NS A6 pressure/localization theorem contract for localized Leray pressure commutators: [P_j,phi] R_i R_l, local Calderon-Zygmund pressure, harmonic pressure tails, annular cutoff errors, epsilon-gradient absorption, and lower-order residual routing into the NSA6 composite error budget."

------------------------------------------------------------------------
-- Canonical contract boundary.

record NSPressureCommutatorEstimateContractBoundary : Set where
  field
    status :
      NSPressureCommutatorEstimateContractStatus
    statusIsCanonical :
      status
        ≡ nsPressureCommutatorEstimateContractBoundaryRecorded_noPromotion
    importedSupport :
      ImportedNSPressureCommutatorEstimateSupport
    pressureCommutatorOperators :
      List PressureCommutatorOperator
    pressureCommutatorOperatorCountProof :
      pressureCommutatorOperatorCount ≡ 9
    cutoffRieszCommutatorRequirements :
      List CutoffRieszCommutatorRequirement
    cutoffRieszCommutatorRequirementCountProof :
      cutoffRieszCommutatorRequirementCount ≡ 8
    localPressureEstimateTargets :
      List LocalPressureEstimateTarget
    localPressureEstimateTargetCountProof :
      localPressureEstimateTargetCount ≡ 8
    harmonicPressureTailTargets :
      List HarmonicPressureTailTarget
    harmonicPressureTailTargetCountProof :
      harmonicPressureTailTargetCount ≡ 7
    annularCutoffErrorTargets :
      List AnnularCutoffErrorTarget
    annularCutoffErrorTargetCountProof :
      annularCutoffErrorTargetCount ≡ 8
    epsilonGradientAbsorptionTargets :
      List EpsilonGradientAbsorptionTarget
    epsilonGradientAbsorptionTargetCountProof :
      epsilonGradientAbsorptionTargetCount ≡ 7
    pressureResidualRoutes :
      List PressureResidualRoute
    pressureResidualRouteCountProof :
      pressureResidualRouteCount ≡ 8
    errorBudgetRoutingAnchor :
      ErrorBudgetRoutingAnchor
    blockers :
      List NSPressureCommutatorEstimateBlocker
    blockerCountProof :
      nsPressureCommutatorEstimateBlockerCount ≡ 10
    nonClaimGuards :
      List NonClaimGuard
    nonClaimGuardCountProof :
      nonClaimGuardCount ≡ 7
    orcsLpgfRows :
      List ORCSLPGFRow
    orcsLpgfRowCountProof :
      orcsLpgfRowCount ≡ 8
    cutoffRieszCommutatorTarget :
      String
    localCalderonZygmundPressureTarget :
      String
    harmonicPressureTailTarget :
      String
    annularCutoffErrorTarget :
      String
    epsilonGradientAbsorptionTarget :
      String
    residualRoutingTarget :
      String
    orcsLpgfSummary :
      String
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsPressureCommutatorEstimateContractSummary
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    importsRecordedIsTrue :
      importsRecorded ≡ true
    cutoffRieszCommutatorContractRecordedIsTrue :
      cutoffRieszCommutatorContractRecorded ≡ true
    localCalderonZygmundPressureContractRecordedIsTrue :
      localCalderonZygmundPressureContractRecorded ≡ true
    harmonicPressureTailContractRecordedIsTrue :
      harmonicPressureTailContractRecorded ≡ true
    annularCutoffErrorContractRecordedIsTrue :
      annularCutoffErrorContractRecorded ≡ true
    epsilonGradientAbsorptionContractRecordedIsTrue :
      epsilonGradientAbsorptionContractRecorded ≡ true
    errorBudgetRoutingRecordedIsTrue :
      errorBudgetRoutingRecorded ≡ true
    pressureCommutatorEstimateProvedIsFalse :
      pressureCommutatorEstimateProved ≡ false
    pressureTailAbsorbedIsFalse :
      pressureTailAbsorbed ≡ false
    localizationTheoremProvedIsFalse :
      localizationTheoremProved ≡ false
    triadicCompensatedLeakageIdentityProvedIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

canonicalNSPressureCommutatorEstimateContractBoundary :
  NSPressureCommutatorEstimateContractBoundary
canonicalNSPressureCommutatorEstimateContractBoundary =
  record
    { status =
        nsPressureCommutatorEstimateContractBoundaryRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; importedSupport =
        canonicalImportedNSPressureCommutatorEstimateSupport
    ; pressureCommutatorOperators =
        canonicalPressureCommutatorOperators
    ; pressureCommutatorOperatorCountProof =
        refl
    ; cutoffRieszCommutatorRequirements =
        canonicalCutoffRieszCommutatorRequirements
    ; cutoffRieszCommutatorRequirementCountProof =
        refl
    ; localPressureEstimateTargets =
        canonicalLocalPressureEstimateTargets
    ; localPressureEstimateTargetCountProof =
        refl
    ; harmonicPressureTailTargets =
        canonicalHarmonicPressureTailTargets
    ; harmonicPressureTailTargetCountProof =
        refl
    ; annularCutoffErrorTargets =
        canonicalAnnularCutoffErrorTargets
    ; annularCutoffErrorTargetCountProof =
        refl
    ; epsilonGradientAbsorptionTargets =
        canonicalEpsilonGradientAbsorptionTargets
    ; epsilonGradientAbsorptionTargetCountProof =
        refl
    ; pressureResidualRoutes =
        canonicalPressureResidualRoutes
    ; pressureResidualRouteCountProof =
        refl
    ; errorBudgetRoutingAnchor =
        canonicalErrorBudgetRoutingAnchor
    ; blockers =
        canonicalNSPressureCommutatorEstimateBlockers
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
    ; cutoffRieszCommutatorTarget =
        cutoffRieszCommutatorTargetText
    ; localCalderonZygmundPressureTarget =
        localCalderonZygmundPressureTargetText
    ; harmonicPressureTailTarget =
        harmonicPressureTailTargetText
    ; annularCutoffErrorTarget =
        annularCutoffErrorTargetText
    ; epsilonGradientAbsorptionTarget =
        epsilonGradientAbsorptionTargetText
    ; residualRoutingTarget =
        residualRoutingTargetText
    ; orcsLpgfSummary =
        canonicalORCSLPGFSummary
    ; summary =
        nsPressureCommutatorEstimateContractSummary
    ; summaryIsCanonical =
        refl
    ; boundaryRecordedIsTrue =
        refl
    ; importsRecordedIsTrue =
        refl
    ; cutoffRieszCommutatorContractRecordedIsTrue =
        refl
    ; localCalderonZygmundPressureContractRecordedIsTrue =
        refl
    ; harmonicPressureTailContractRecordedIsTrue =
        refl
    ; annularCutoffErrorContractRecordedIsTrue =
        refl
    ; epsilonGradientAbsorptionContractRecordedIsTrue =
        refl
    ; errorBudgetRoutingRecordedIsTrue =
        refl
    ; pressureCommutatorEstimateProvedIsFalse =
        refl
    ; pressureTailAbsorbedIsFalse =
        refl
    ; localizationTheoremProvedIsFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedIsFalse =
        refl
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this boundary is not a theorem promotion.

postulate
  pressureCommutatorEstimateContractDoesNotProveEstimate :
    pressureCommutatorEstimateProved ≡ true →
    ⊥

  pressureCommutatorEstimateContractDoesNotAbsorbTail :
    pressureTailAbsorbed ≡ true →
    ⊥

  pressureCommutatorEstimateContractDoesNotProveLocalization :
    localizationTheoremProved ≡ true →
    ⊥

  pressureCommutatorEstimateContractDoesNotProveTriadicLeakage :
    triadicCompensatedLeakageIdentityProved ≡ true →
    ⊥

  pressureCommutatorEstimateContractDoesNotPromoteNSClay :
    nsClayPromoted ≡ true →
    ⊥

  pressureCommutatorEstimateContractDoesNotPromoteTerminal :
    terminalPromotion ≡ true →
    ⊥
