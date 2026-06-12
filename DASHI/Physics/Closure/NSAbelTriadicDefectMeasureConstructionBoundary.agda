module DASHI.Physics.Closure.NSAbelTriadicDefectMeasureConstructionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary as LRT
import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary as Sheaf
import DASHI.Physics.Closure.NSTriadicLeakageSquareFunctionCoercivityBoundary as Square
import DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol as Symbol

------------------------------------------------------------------------
-- NS Abel triadic defect-measure construction boundary.
--
-- This module records the next analytic measure-construction obligation
-- for the corrected triadic Navier-Stokes route:
--
--   AbelTriadicDefectMeasureConstruction
--
-- The target is an Abel-weighted Littlewood-Paley interaction measure on
-- the true Leray resonant triadic phase space with:
--
--   bounded total variation uniformly in r,
--   weak-* compactness along r -> 0,
--   normalization against the critical dissipation D_r,
--   quantitative off-diagonal control,
--   Lei-Ren-Tian output-support transfer from high-vorticity directions to
--   pi_out(supp mu),
--   and enough structure to feed the A1/A3 bootstrap and the triadic
--   leakage square-function coercivity theorem.
--
-- This is a fail-closed boundary receipt only.  It does not construct the
-- measure, prove bounded mass or weak-* compactness, prove output support
-- transfer, prove off-diagonal error summability, prove normalization or the
-- quantitative control needed by the A1/A3 bootstrap, prove residual
-- depletion, or promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- LP/Abel triadic interaction carriers.

data SuitableWeakBlowupProfileCarrier : Set where
  residualPositiveSuitableWeakBlowupProfile :
    SuitableWeakBlowupProfileCarrier

data ParabolicScaleCarrier : Set where
  shrinkingCriticalParabolicScale :
    SuitableWeakBlowupProfileCarrier →
    ParabolicScaleCarrier

data CriticalDissipationCarrier : Set where
  localDissipationDr :
    ParabolicScaleCarrier →
    CriticalDissipationCarrier

data DyadicLittlewoodPaleyShell : Set where
  dyadicShellAtReciprocalScale :
    ParabolicScaleCarrier →
    DyadicLittlewoodPaleyShell
  neighboringDyadicShell :
    DyadicLittlewoodPaleyShell →
    DyadicLittlewoodPaleyShell
  offDiagonalDyadicShell :
    DyadicLittlewoodPaleyShell →
    DyadicLittlewoodPaleyShell

data AbelWeightCarrier : Set where
  abelExponentialScaleWeight :
    ParabolicScaleCarrier →
    AbelWeightCarrier

data TriadicInteractionBlockCarrier : Set where
  trueLerayLPInteractionBlock :
    Symbol.TrueNSBilinearSymbol →
    DyadicLittlewoodPaleyShell →
    DyadicLittlewoodPaleyShell →
    Sheaf.TriadicResonantSite →
    TriadicInteractionBlockCarrier

data AbelTriadicDefectMeasureCarrier : Set where
  abelAveragedLPInteractionDefectMeasure :
    AbelWeightCarrier →
    TriadicInteractionBlockCarrier →
    Sheaf.TriadicPatch →
    AbelTriadicDefectMeasureCarrier

canonicalBlowupProfile : SuitableWeakBlowupProfileCarrier
canonicalBlowupProfile =
  residualPositiveSuitableWeakBlowupProfile

canonicalParabolicScale : ParabolicScaleCarrier
canonicalParabolicScale =
  shrinkingCriticalParabolicScale canonicalBlowupProfile

canonicalDissipationDr : CriticalDissipationCarrier
canonicalDissipationDr =
  localDissipationDr canonicalParabolicScale

canonicalCentralLPShell : DyadicLittlewoodPaleyShell
canonicalCentralLPShell =
  dyadicShellAtReciprocalScale canonicalParabolicScale

canonicalNeighborLPShell : DyadicLittlewoodPaleyShell
canonicalNeighborLPShell =
  neighboringDyadicShell canonicalCentralLPShell

canonicalOffDiagonalLPShell : DyadicLittlewoodPaleyShell
canonicalOffDiagonalLPShell =
  offDiagonalDyadicShell canonicalCentralLPShell

canonicalAbelWeight : AbelWeightCarrier
canonicalAbelWeight =
  abelExponentialScaleWeight canonicalParabolicScale

canonicalTriadicInteractionBlock : TriadicInteractionBlockCarrier
canonicalTriadicInteractionBlock =
  trueLerayLPInteractionBlock
    Symbol.canonicalTrueNSBilinearSymbol
    canonicalCentralLPShell
    canonicalNeighborLPShell
    Sheaf.canonicalTriadicResonantSite

canonicalAbelTriadicDefectMeasure :
  AbelTriadicDefectMeasureCarrier
canonicalAbelTriadicDefectMeasure =
  abelAveragedLPInteractionDefectMeasure
    canonicalAbelWeight
    canonicalTriadicInteractionBlock
    Sheaf.canonicalResonantPatch

------------------------------------------------------------------------
-- Measure obligations: tightness, normalization, support, and errors.

data AbelTriadicMeasureConstructionObligation : Set where
  selectResidualPositiveBlowupProfile :
    AbelTriadicMeasureConstructionObligation
  chooseReciprocalLittlewoodPaleyShells :
    AbelTriadicMeasureConstructionObligation
  buildTrueLerayDyadicTriadicBlocks :
    AbelTriadicMeasureConstructionObligation
  applyAbelScaleAveragingWeights :
    AbelTriadicMeasureConstructionObligation
  proveUniformFiniteVariationBound :
    AbelTriadicMeasureConstructionObligation
  recordA11BoundedAbelWeightedDefectMassContract :
    AbelTriadicMeasureConstructionObligation
  routeBoundedAbelMassIntoWeakStarCompactness :
    AbelTriadicMeasureConstructionObligation
  recordA12WeakStarTightnessContract :
    AbelTriadicMeasureConstructionObligation
  extractWeakStarTriadicMeasure :
    AbelTriadicMeasureConstructionObligation
  recordA13QuantitativeShellTailContract :
    AbelTriadicMeasureConstructionObligation
  prepareSereginEpsilonRateIntake :
    AbelTriadicMeasureConstructionObligation
  prepareStationarityRateMapOnAbelWindows :
    AbelTriadicMeasureConstructionObligation
  quantifyCompactnessStrongEnoughForA1A3Bootstrap :
    AbelTriadicMeasureConstructionObligation
  normalizeMeasureAgainstCriticalDissipationDr :
    AbelTriadicMeasureConstructionObligation
  proveOffDiagonalInteractionErrorSmall :
    AbelTriadicMeasureConstructionObligation
  transferLeiRenTianOutputSupportCondition :
    AbelTriadicMeasureConstructionObligation
  connectMeasureToTriadicLeakageFunctional :
    AbelTriadicMeasureConstructionObligation
  feedSquareFunctionCoercivityBoundary :
    AbelTriadicMeasureConstructionObligation

canonicalAbelTriadicMeasureConstructionObligations :
  List AbelTriadicMeasureConstructionObligation
canonicalAbelTriadicMeasureConstructionObligations =
  selectResidualPositiveBlowupProfile
  ∷ chooseReciprocalLittlewoodPaleyShells
  ∷ buildTrueLerayDyadicTriadicBlocks
  ∷ applyAbelScaleAveragingWeights
  ∷ proveUniformFiniteVariationBound
  ∷ recordA11BoundedAbelWeightedDefectMassContract
  ∷ routeBoundedAbelMassIntoWeakStarCompactness
  ∷ recordA12WeakStarTightnessContract
  ∷ extractWeakStarTriadicMeasure
  ∷ recordA13QuantitativeShellTailContract
  ∷ prepareSereginEpsilonRateIntake
  ∷ prepareStationarityRateMapOnAbelWindows
  ∷ quantifyCompactnessStrongEnoughForA1A3Bootstrap
  ∷ normalizeMeasureAgainstCriticalDissipationDr
  ∷ proveOffDiagonalInteractionErrorSmall
  ∷ transferLeiRenTianOutputSupportCondition
  ∷ connectMeasureToTriadicLeakageFunctional
  ∷ feedSquareFunctionCoercivityBoundary
  ∷ []

abelTriadicMeasureConstructionObligationCount : Nat
abelTriadicMeasureConstructionObligationCount =
  listLength canonicalAbelTriadicMeasureConstructionObligations

abelTriadicMeasureConstructionObligationCountIs18 :
  abelTriadicMeasureConstructionObligationCount ≡ 18
abelTriadicMeasureConstructionObligationCountIs18 =
  refl

data AbelTriadicA1MeasureSocketClause : Set where
  a11BoundedAbelMassSocket :
    String → AbelTriadicA1MeasureSocketClause
  a11BoundedMassConstantSocket :
    String → AbelTriadicA1MeasureSocketClause
  a12WeakStarTightnessSocket :
    String → AbelTriadicA1MeasureSocketClause
  a12TightnessModulusSocket :
    String → AbelTriadicA1MeasureSocketClause
  a13QuantitativeShellTailSocket :
    String → AbelTriadicA1MeasureSocketClause
  a13ShellTailRateSocket :
    String → AbelTriadicA1MeasureSocketClause
  shellTailFeedsWeakStarTightnessSocket :
    AbelTriadicA1MeasureSocketClause
  shellTailFeedsA1A3BootstrapSocket :
    AbelTriadicA1MeasureSocketClause

a11BoundedAbelMassSocketText : String
a11BoundedAbelMassSocketText =
  "A1.1 socket: the Abel-weighted defect measures mu_r must satisfy sup_r ||mu_r||_TV <= C_A1(R,M)."

a11BoundedMassConstantSocketText : String
a11BoundedMassConstantSocketText =
  "A1.1 constant socket: C_A1(R,M) is uniform in the shrinking scale r."

a12WeakStarTightnessSocketText : String
a12WeakStarTightnessSocketText =
  "A1.2 socket: {mu_r}_r must be weak-* precompact in finite Radon measures once uniform tightness is recorded."

a12TightnessModulusSocketText : String
a12TightnessModulusSocketText =
  "A1.2 modulus socket: Tight_A1(epsilon;R,M) chooses a reciprocal shell cutoff K with tail mass <= epsilon uniformly in r."

a13QuantitativeShellTailSocketText : String
a13QuantitativeShellTailSocketText =
  "A1.3 socket: shell-tail mass outside the reciprocal Abel window is <= Tail_A1(K;R,M)."

a13ShellTailRateSocketText : String
a13ShellTailRateSocketText =
  "A1.3 rate socket: Tail_A1(K;R,M) -> 0 as K -> infinity uniformly in r."

canonicalAbelTriadicA1MeasureSocketClauses :
  List AbelTriadicA1MeasureSocketClause
canonicalAbelTriadicA1MeasureSocketClauses =
  a11BoundedAbelMassSocket a11BoundedAbelMassSocketText
  ∷ a11BoundedMassConstantSocket a11BoundedMassConstantSocketText
  ∷ a12WeakStarTightnessSocket a12WeakStarTightnessSocketText
  ∷ a12TightnessModulusSocket a12TightnessModulusSocketText
  ∷ a13QuantitativeShellTailSocket a13QuantitativeShellTailSocketText
  ∷ a13ShellTailRateSocket a13ShellTailRateSocketText
  ∷ shellTailFeedsWeakStarTightnessSocket
  ∷ shellTailFeedsA1A3BootstrapSocket
  ∷ []

abelTriadicA1MeasureSocketClauseCount : Nat
abelTriadicA1MeasureSocketClauseCount =
  listLength canonicalAbelTriadicA1MeasureSocketClauses

abelTriadicA1MeasureSocketClauseCountIs8 :
  abelTriadicA1MeasureSocketClauseCount ≡ 8
abelTriadicA1MeasureSocketClauseCountIs8 =
  refl

data CandidateA1A3BootstrapHandoff : Set where
  typeIOrCKNToBoundedAbelMassHandoff :
    CandidateA1A3BootstrapHandoff
  boundedAbelMassToWeakStarCompactnessHandoff :
    CandidateA1A3BootstrapHandoff
  weakStarCompactnessToSereginEpsilonRateHandoff :
    CandidateA1A3BootstrapHandoff
  sereginEpsilonRateToStationarityMapHandoff :
    CandidateA1A3BootstrapHandoff
  stationarityMapToMultiscaleAbelSummationIssueHandoff :
    CandidateA1A3BootstrapHandoff

canonicalCandidateA1A3BootstrapHandoffs :
  List CandidateA1A3BootstrapHandoff
canonicalCandidateA1A3BootstrapHandoffs =
  typeIOrCKNToBoundedAbelMassHandoff
  ∷ boundedAbelMassToWeakStarCompactnessHandoff
  ∷ weakStarCompactnessToSereginEpsilonRateHandoff
  ∷ sereginEpsilonRateToStationarityMapHandoff
  ∷ stationarityMapToMultiscaleAbelSummationIssueHandoff
  ∷ []

candidateA1A3BootstrapHandoffCount : Nat
candidateA1A3BootstrapHandoffCount =
  listLength canonicalCandidateA1A3BootstrapHandoffs

candidateA1A3BootstrapHandoffCountIs5 :
  candidateA1A3BootstrapHandoffCount ≡ 5
candidateA1A3BootstrapHandoffCountIs5 = refl

data NormalizationAgainstDrBoundary : Set where
  totalVariationControlledByCriticalDissipation :
    AbelTriadicDefectMeasureCarrier →
    CriticalDissipationCarrier →
    NormalizationAgainstDrBoundary
  nonzeroMassWhenResidualCascadePersists :
    AbelTriadicDefectMeasureCarrier →
    CriticalDissipationCarrier →
    NormalizationAgainstDrBoundary
  scaleInvariantDefectMassQuotient :
    AbelTriadicDefectMeasureCarrier →
    CriticalDissipationCarrier →
    NormalizationAgainstDrBoundary

canonicalTotalVariationNormalization :
  NormalizationAgainstDrBoundary
canonicalTotalVariationNormalization =
  totalVariationControlledByCriticalDissipation
    canonicalAbelTriadicDefectMeasure
    canonicalDissipationDr

canonicalNonzeroResidualMassNormalization :
  NormalizationAgainstDrBoundary
canonicalNonzeroResidualMassNormalization =
  nonzeroMassWhenResidualCascadePersists
    canonicalAbelTriadicDefectMeasure
    canonicalDissipationDr

canonicalScaleInvariantQuotientNormalization :
  NormalizationAgainstDrBoundary
canonicalScaleInvariantQuotientNormalization =
  scaleInvariantDefectMassQuotient
    canonicalAbelTriadicDefectMeasure
    canonicalDissipationDr

canonicalNormalizationBoundaries :
  List NormalizationAgainstDrBoundary
canonicalNormalizationBoundaries =
  canonicalTotalVariationNormalization
  ∷ canonicalNonzeroResidualMassNormalization
  ∷ canonicalScaleInvariantQuotientNormalization
  ∷ []

normalizationBoundaryCount : Nat
normalizationBoundaryCount =
  listLength canonicalNormalizationBoundaries

normalizationBoundaryCountIs3 :
  normalizationBoundaryCount ≡ 3
normalizationBoundaryCountIs3 =
  refl

data OffDiagonalInteractionErrorBoundary : Set where
  highLowParaproductErrorControlled :
    DyadicLittlewoodPaleyShell →
    DyadicLittlewoodPaleyShell →
    OffDiagonalInteractionErrorBoundary
  lowHighParaproductErrorControlled :
    DyadicLittlewoodPaleyShell →
    DyadicLittlewoodPaleyShell →
    OffDiagonalInteractionErrorBoundary
  widelySeparatedShellErrorVanishesInAbelAverage :
    DyadicLittlewoodPaleyShell →
    DyadicLittlewoodPaleyShell →
    AbelWeightCarrier →
    OffDiagonalInteractionErrorBoundary
  pressureNonlocalityOffDiagonalRemainderSeparated :
    Symbol.LerayProjector →
    DyadicLittlewoodPaleyShell →
    OffDiagonalInteractionErrorBoundary

canonicalOffDiagonalInteractionErrors :
  List OffDiagonalInteractionErrorBoundary
canonicalOffDiagonalInteractionErrors =
  highLowParaproductErrorControlled
    canonicalCentralLPShell
    canonicalOffDiagonalLPShell
  ∷ lowHighParaproductErrorControlled
    canonicalOffDiagonalLPShell
    canonicalCentralLPShell
  ∷ widelySeparatedShellErrorVanishesInAbelAverage
    canonicalCentralLPShell
    canonicalOffDiagonalLPShell
    canonicalAbelWeight
  ∷ pressureNonlocalityOffDiagonalRemainderSeparated
    Symbol.canonicalLerayProjector
    canonicalOffDiagonalLPShell
  ∷ []

offDiagonalInteractionErrorCount : Nat
offDiagonalInteractionErrorCount =
  listLength canonicalOffDiagonalInteractionErrors

offDiagonalInteractionErrorCountIs4 :
  offDiagonalInteractionErrorCount ≡ 4
offDiagonalInteractionErrorCountIs4 =
  refl

------------------------------------------------------------------------
-- Output support transfer and relation to Lei-Ren-Tian.

data OutputSupportTransferBoundary : Set where
  highVorticityDirectionsProjectToTriadicOutputs :
    LRT.HighVorticityDirectionSet →
    Sheaf.OutputProjection →
    OutputSupportTransferBoundary
  lrtGreatCircleHittingTransfersToPiOutSupport :
    LRT.GreatCircleHittingProperty →
    AbelTriadicDefectMeasureCarrier →
    Sheaf.OutputProjection →
    OutputSupportTransferBoundary
  outputSupportCannotAvoidGreatCircleForSingularProfile :
    AbelTriadicDefectMeasureCarrier →
    LRT.SingularityNecessaryConditionBoundary →
    OutputSupportTransferBoundary

canonicalHighVorticityOutputProjectionTransfer :
  OutputSupportTransferBoundary
canonicalHighVorticityOutputProjectionTransfer =
  highVorticityDirectionsProjectToTriadicOutputs
    LRT.canonicalHighVorticityDirectionSet
    Sheaf.canonicalOutputProjection

canonicalLRTGreatCircleOutputSupportTransfer :
  OutputSupportTransferBoundary
canonicalLRTGreatCircleOutputSupportTransfer =
  lrtGreatCircleHittingTransfersToPiOutSupport
    LRT.canonicalGreatCircleHittingProperty
    canonicalAbelTriadicDefectMeasure
    Sheaf.canonicalOutputProjection

canonicalSingularOutputSupportNonAvoidance :
  OutputSupportTransferBoundary
canonicalSingularOutputSupportNonAvoidance =
  outputSupportCannotAvoidGreatCircleForSingularProfile
    canonicalAbelTriadicDefectMeasure
    LRT.canonicalSingularityNecessaryConditionBoundary

canonicalOutputSupportTransferBoundaries :
  List OutputSupportTransferBoundary
canonicalOutputSupportTransferBoundaries =
  canonicalHighVorticityOutputProjectionTransfer
  ∷ canonicalLRTGreatCircleOutputSupportTransfer
  ∷ canonicalSingularOutputSupportNonAvoidance
  ∷ []

outputSupportTransferBoundaryCount : Nat
outputSupportTransferBoundaryCount =
  listLength canonicalOutputSupportTransferBoundaries

outputSupportTransferBoundaryCountIs3 :
  outputSupportTransferBoundaryCount ≡ 3
outputSupportTransferBoundaryCountIs3 =
  refl

data DefectMeasureToLeakageFunctionalBoundary : Set where
  measureIntegratesTriadicLeakageEigenvalue :
    AbelTriadicDefectMeasureCarrier →
    Sheaf.TriadicLeakageEigenvalueCarrier →
    DefectMeasureToLeakageFunctionalBoundary
  positiveWidthTurnsLRTSupportIntoLeakagePatchMass :
    Sheaf.CascadeClosedZeroModePositiveWidthDependency →
    OutputSupportTransferBoundary →
    Sheaf.OutputLeakageFunctional →
    DefectMeasureToLeakageFunctionalBoundary
  leakageMassFeedsSquareFunctionCoercivityTarget :
    AbelTriadicDefectMeasureCarrier →
    Square.BilinearLeakageSquareFunctionCarrier →
    DefectMeasureToLeakageFunctionalBoundary

canonicalMeasureIntegratesLeakage :
  DefectMeasureToLeakageFunctionalBoundary
canonicalMeasureIntegratesLeakage =
  measureIntegratesTriadicLeakageEigenvalue
    canonicalAbelTriadicDefectMeasure
    Sheaf.canonicalTriadicLeakageEigenvalue

canonicalPositiveWidthToLeakagePatchMass :
  DefectMeasureToLeakageFunctionalBoundary
canonicalPositiveWidthToLeakagePatchMass =
  positiveWidthTurnsLRTSupportIntoLeakagePatchMass
    Sheaf.canonicalPositiveWidthDependency
    canonicalLRTGreatCircleOutputSupportTransfer
    Sheaf.canonicalOutputLeakageFunctional

canonicalLeakageMassFeedsSquareFunction :
  DefectMeasureToLeakageFunctionalBoundary
canonicalLeakageMassFeedsSquareFunction =
  leakageMassFeedsSquareFunctionCoercivityTarget
    canonicalAbelTriadicDefectMeasure
    Square.canonicalBilinearLeakageSquareFunction

canonicalDefectMeasureToLeakageBoundaries :
  List DefectMeasureToLeakageFunctionalBoundary
canonicalDefectMeasureToLeakageBoundaries =
  canonicalMeasureIntegratesLeakage
  ∷ canonicalPositiveWidthToLeakagePatchMass
  ∷ canonicalLeakageMassFeedsSquareFunction
  ∷ []

defectMeasureToLeakageBoundaryCount : Nat
defectMeasureToLeakageBoundaryCount =
  listLength canonicalDefectMeasureToLeakageBoundaries

defectMeasureToLeakageBoundaryCountIs3 :
  defectMeasureToLeakageBoundaryCount ≡ 3
defectMeasureToLeakageBoundaryCountIs3 =
  refl

------------------------------------------------------------------------
-- Blockers, support rows, and status rows.

data AbelTriadicDefectMeasureBlocker : Set where
  missingResidualPositiveBlowupProfileSelection :
    AbelTriadicDefectMeasureBlocker
  missingLPAbelBoundedMassAndFiniteVariation :
    AbelTriadicDefectMeasureBlocker
  missingA11ConcreteBoundedAbelMassGrammar :
    AbelTriadicDefectMeasureBlocker
  missingWeakStarTriadicMeasureExtraction :
    AbelTriadicDefectMeasureBlocker
  missingA12ConcreteWeakStarTightnessGrammar :
    AbelTriadicDefectMeasureBlocker
  missingQuantitativeCompactnessForA1A3Bootstrap :
    AbelTriadicDefectMeasureBlocker
  missingA13ConcreteQuantitativeShellTailGrammar :
    AbelTriadicDefectMeasureBlocker
  missingA1ConstantAndRateNamesOnMeasureSocket :
    AbelTriadicDefectMeasureBlocker
  missingNormalizationAgainstCriticalDissipation :
    AbelTriadicDefectMeasureBlocker
  missingOffDiagonalInteractionErrorEstimate :
    AbelTriadicDefectMeasureBlocker
  missingPressureNonlocalityRemainderControl :
    AbelTriadicDefectMeasureBlocker
  missingLeiRenTianOutputSupportTransfer :
    AbelTriadicDefectMeasureBlocker
  missingPositiveOutputWidthConsumer :
    AbelTriadicDefectMeasureBlocker
  missingPlancherelTriadicToSquareFunction :
    AbelTriadicDefectMeasureBlocker
  missingTriadicLeakageSquareFunctionCoercivity :
    AbelTriadicDefectMeasureBlocker
  missingExactAbelWindowExponentForClosure :
    AbelTriadicDefectMeasureBlocker
  missingMultiscaleAbelSummationClosure :
    AbelTriadicDefectMeasureBlocker
  missingCriticalResidualNonPositive :
    AbelTriadicDefectMeasureBlocker
  clayNavierStokesPromotionClosed :
    AbelTriadicDefectMeasureBlocker

canonicalAbelTriadicDefectMeasureBlockers :
  List AbelTriadicDefectMeasureBlocker
canonicalAbelTriadicDefectMeasureBlockers =
  missingResidualPositiveBlowupProfileSelection
  ∷ missingLPAbelBoundedMassAndFiniteVariation
  ∷ missingA11ConcreteBoundedAbelMassGrammar
  ∷ missingWeakStarTriadicMeasureExtraction
  ∷ missingA12ConcreteWeakStarTightnessGrammar
  ∷ missingQuantitativeCompactnessForA1A3Bootstrap
  ∷ missingA13ConcreteQuantitativeShellTailGrammar
  ∷ missingA1ConstantAndRateNamesOnMeasureSocket
  ∷ missingNormalizationAgainstCriticalDissipation
  ∷ missingOffDiagonalInteractionErrorEstimate
  ∷ missingPressureNonlocalityRemainderControl
  ∷ missingLeiRenTianOutputSupportTransfer
  ∷ missingPositiveOutputWidthConsumer
  ∷ missingPlancherelTriadicToSquareFunction
  ∷ missingTriadicLeakageSquareFunctionCoercivity
  ∷ missingExactAbelWindowExponentForClosure
  ∷ missingMultiscaleAbelSummationClosure
  ∷ missingCriticalResidualNonPositive
  ∷ clayNavierStokesPromotionClosed
  ∷ []

abelTriadicDefectMeasureBlockerCount : Nat
abelTriadicDefectMeasureBlockerCount =
  listLength canonicalAbelTriadicDefectMeasureBlockers

abelTriadicDefectMeasureBlockerCountIs19 :
  abelTriadicDefectMeasureBlockerCount ≡ 19
abelTriadicDefectMeasureBlockerCountIs19 =
  refl

data AbelTriadicDefectMeasureSupportRow : Set where
  trueLerayTriadicSymbolSupport :
    AbelTriadicDefectMeasureSupportRow
  microlocalDefectMassBoundarySupport :
    AbelTriadicDefectMeasureSupportRow
  triadicDefectSheafLeakageSupport :
    AbelTriadicDefectMeasureSupportRow
  leiRenTianGreatCircleCriterionSupport :
    AbelTriadicDefectMeasureSupportRow
  squareFunctionCoercivityBoundarySupport :
    AbelTriadicDefectMeasureSupportRow
  taoAveragedNSGuardSupport :
    AbelTriadicDefectMeasureSupportRow
  noClayPromotionSupport :
    AbelTriadicDefectMeasureSupportRow

canonicalAbelTriadicDefectMeasureSupportRows :
  List AbelTriadicDefectMeasureSupportRow
canonicalAbelTriadicDefectMeasureSupportRows =
  trueLerayTriadicSymbolSupport
  ∷ microlocalDefectMassBoundarySupport
  ∷ triadicDefectSheafLeakageSupport
  ∷ leiRenTianGreatCircleCriterionSupport
  ∷ squareFunctionCoercivityBoundarySupport
  ∷ taoAveragedNSGuardSupport
  ∷ noClayPromotionSupport
  ∷ []

abelTriadicDefectMeasureSupportRowCount : Nat
abelTriadicDefectMeasureSupportRowCount =
  listLength canonicalAbelTriadicDefectMeasureSupportRows

abelTriadicDefectMeasureSupportRowCountIs7 :
  abelTriadicDefectMeasureSupportRowCount ≡ 7
abelTriadicDefectMeasureSupportRowCountIs7 =
  refl

data AbelTriadicDefectMeasureStatusRow : Set where
  boundaryReceiptRecordedStatus :
    AbelTriadicDefectMeasureStatusRow
  lpAbelTriadicMeasureObligationTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  outputSupportTransferObligationTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  offDiagonalErrorObligationTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  normalizationAgainstDrObligationTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  compactnessFeedsA1A3BootstrapTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  relationToLeiRenTianTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  relationToSquareFunctionCoercivityTypedStatus :
    AbelTriadicDefectMeasureStatusRow
  measureConstructedFalseStatus :
    AbelTriadicDefectMeasureStatusRow
  outputSupportTransferFalseStatus :
    AbelTriadicDefectMeasureStatusRow
  offDiagonalErrorClosedFalseStatus :
    AbelTriadicDefectMeasureStatusRow
  normalizationProvedFalseStatus :
    AbelTriadicDefectMeasureStatusRow
  clayPromotionFalseStatus :
    AbelTriadicDefectMeasureStatusRow

canonicalAbelTriadicDefectMeasureStatusRows :
  List AbelTriadicDefectMeasureStatusRow
canonicalAbelTriadicDefectMeasureStatusRows =
  boundaryReceiptRecordedStatus
  ∷ lpAbelTriadicMeasureObligationTypedStatus
  ∷ outputSupportTransferObligationTypedStatus
  ∷ offDiagonalErrorObligationTypedStatus
  ∷ normalizationAgainstDrObligationTypedStatus
  ∷ compactnessFeedsA1A3BootstrapTypedStatus
  ∷ relationToLeiRenTianTypedStatus
  ∷ relationToSquareFunctionCoercivityTypedStatus
  ∷ measureConstructedFalseStatus
  ∷ outputSupportTransferFalseStatus
  ∷ offDiagonalErrorClosedFalseStatus
  ∷ normalizationProvedFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

abelTriadicDefectMeasureStatusRowCount : Nat
abelTriadicDefectMeasureStatusRowCount =
  listLength canonicalAbelTriadicDefectMeasureStatusRows

abelTriadicDefectMeasureStatusRowCountIs12 :
  abelTriadicDefectMeasureStatusRowCount ≡ 13
abelTriadicDefectMeasureStatusRowCountIs12 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSAbelTriadicDefectMeasureConstructionBoundary : Set where
  constructor nsAbelTriadicDefectMeasureConstructionBoundary
  field
    blowupProfile :
      SuitableWeakBlowupProfileCarrier
    blowupProfileIsCanonical :
      blowupProfile ≡ canonicalBlowupProfile
    parabolicScale :
      ParabolicScaleCarrier
    parabolicScaleIsCanonical :
      parabolicScale ≡ canonicalParabolicScale
    criticalDissipation :
      CriticalDissipationCarrier
    criticalDissipationIsCanonical :
      criticalDissipation ≡ canonicalDissipationDr
    abelWeight :
      AbelWeightCarrier
    abelWeightIsCanonical :
      abelWeight ≡ canonicalAbelWeight
    triadicInteractionBlock :
      TriadicInteractionBlockCarrier
    triadicInteractionBlockIsCanonical :
      triadicInteractionBlock ≡ canonicalTriadicInteractionBlock
    abelTriadicMeasure :
      AbelTriadicDefectMeasureCarrier
    abelTriadicMeasureIsCanonical :
      abelTriadicMeasure ≡ canonicalAbelTriadicDefectMeasure
    constructionObligations :
      List AbelTriadicMeasureConstructionObligation
    constructionObligationsAreCanonical :
      constructionObligations ≡ canonicalAbelTriadicMeasureConstructionObligations
    a1MeasureSocketClauses :
      List AbelTriadicA1MeasureSocketClause
    a1MeasureSocketClausesAreCanonical :
      a1MeasureSocketClauses ≡ canonicalAbelTriadicA1MeasureSocketClauses
    normalizationBoundaries :
      List NormalizationAgainstDrBoundary
    normalizationBoundariesAreCanonical :
      normalizationBoundaries ≡ canonicalNormalizationBoundaries
    offDiagonalErrorBoundaries :
      List OffDiagonalInteractionErrorBoundary
    offDiagonalErrorBoundariesAreCanonical :
      offDiagonalErrorBoundaries ≡ canonicalOffDiagonalInteractionErrors
    outputSupportTransferBoundaries :
      List OutputSupportTransferBoundary
    outputSupportTransferBoundariesAreCanonical :
      outputSupportTransferBoundaries ≡ canonicalOutputSupportTransferBoundaries
    leakageFunctionalBoundaries :
      List DefectMeasureToLeakageFunctionalBoundary
    leakageFunctionalBoundariesAreCanonical :
      leakageFunctionalBoundaries ≡ canonicalDefectMeasureToLeakageBoundaries
    blockerRows :
      List AbelTriadicDefectMeasureBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalAbelTriadicDefectMeasureBlockers
    statusRows :
      List AbelTriadicDefectMeasureStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalAbelTriadicDefectMeasureStatusRows
    boundaryRecorded :
      Bool
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    lpAbelTriadicObligationTyped :
      Bool
    lpAbelTriadicObligationTypedIsTrue :
      lpAbelTriadicObligationTyped ≡ true
    relationToLeiRenTianTyped :
      Bool
    relationToLeiRenTianTypedIsTrue :
      relationToLeiRenTianTyped ≡ true
    relationToSquareFunctionTyped :
      Bool
    relationToSquareFunctionTypedIsTrue :
      relationToSquareFunctionTyped ≡ true
    abelTriadicMeasureConstructed :
      Bool
    abelTriadicMeasureConstructedIsFalse :
      abelTriadicMeasureConstructed ≡ false
    outputSupportTransferProved :
      Bool
    outputSupportTransferProvedIsFalse :
      outputSupportTransferProved ≡ false
    offDiagonalErrorClosed :
      Bool
    offDiagonalErrorClosedIsFalse :
      offDiagonalErrorClosed ≡ false
    normalizationAgainstDrProved :
      Bool
    normalizationAgainstDrProvedIsFalse :
      normalizationAgainstDrProved ≡ false
    boundaryClayNavierStokesPromoted :
      Bool
    boundaryClayNavierStokesPromotedIsFalse :
      boundaryClayNavierStokesPromoted ≡ false

open NSAbelTriadicDefectMeasureConstructionBoundary public

canonicalNSAbelTriadicDefectMeasureConstructionBoundary :
  NSAbelTriadicDefectMeasureConstructionBoundary
canonicalNSAbelTriadicDefectMeasureConstructionBoundary =
  nsAbelTriadicDefectMeasureConstructionBoundary
    canonicalBlowupProfile
    refl
    canonicalParabolicScale
    refl
    canonicalDissipationDr
    refl
    canonicalAbelWeight
    refl
    canonicalTriadicInteractionBlock
    refl
    canonicalAbelTriadicDefectMeasure
    refl
    canonicalAbelTriadicMeasureConstructionObligations
    refl
    canonicalAbelTriadicA1MeasureSocketClauses
    refl
    canonicalNormalizationBoundaries
    refl
    canonicalOffDiagonalInteractionErrors
    refl
    canonicalOutputSupportTransferBoundaries
    refl
    canonicalDefectMeasureToLeakageBoundaries
    refl
    canonicalAbelTriadicDefectMeasureBlockers
    refl
    canonicalAbelTriadicDefectMeasureStatusRows
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Public fail-closed flags and imported anchors.

NSAbelTriadicDefectMeasureConstructionBoundaryRecorded : Bool
NSAbelTriadicDefectMeasureConstructionBoundaryRecorded =
  true

LPAbelTriadicMeasureObligationTyped : Bool
LPAbelTriadicMeasureObligationTyped =
  true

OutputSupportTransferObligationTyped : Bool
OutputSupportTransferObligationTyped =
  true

OffDiagonalInteractionErrorObligationTyped : Bool
OffDiagonalInteractionErrorObligationTyped =
  true

NormalizationAgainstDrObligationTyped : Bool
NormalizationAgainstDrObligationTyped =
  true

RelationToLeiRenTianTyped : Bool
RelationToLeiRenTianTyped =
  true

RelationToSquareFunctionCoercivityTyped : Bool
RelationToSquareFunctionCoercivityTyped =
  true

AbelTriadicDefectMeasureConstructed : Bool
AbelTriadicDefectMeasureConstructed =
  false

OutputSupportTransferProved : Bool
OutputSupportTransferProved =
  false

OffDiagonalInteractionErrorClosed : Bool
OffDiagonalInteractionErrorClosed =
  false

NormalizationAgainstDrProved : Bool
NormalizationAgainstDrProved =
  false

PlancherelTriadicToSquareFunctionProved : Bool
PlancherelTriadicToSquareFunctionProved =
  false

TriadicLeakageSquareFunctionCoercivityProved : Bool
TriadicLeakageSquareFunctionCoercivityProved =
  false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive =
  false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

symbolExactLerayTriadicAnchor : Bool
symbolExactLerayTriadicAnchor =
  Symbol.exactSymbolRecordedFlag

symbolWidthStillFalseAnchor : Bool
symbolWidthStillFalseAnchor =
  Symbol.widthProvedFlag

microDefectMassStillFalseAnchor : Bool
microDefectMassStillFalseAnchor =
  Micro.MicrolocalDefectMassConstructed

lrtBoundaryRecordedAnchor : Bool
lrtBoundaryRecordedAnchor =
  LRT.NSLeiRenTianGreatCircleCriterionBoundaryRecorded

lrtDirectionSetMeasureTransferStillFalseAnchor : Bool
lrtDirectionSetMeasureTransferStillFalseAnchor =
  LRT.DirectionSetIToMicrolocalMeasureTransferProved

sheafAbelMeasureRecordedAnchor : Bool
sheafAbelMeasureRecordedAnchor =
  Sheaf.abelTriadicMeasureRecorded

sheafAbelMeasureConstructedStillFalseAnchor : Bool
sheafAbelMeasureConstructedStillFalseAnchor =
  Sheaf.abelMeasureConstructedFromBlowupSequence

squareFunctionCoercivityStillFalseAnchor : Bool
squareFunctionCoercivityStillFalseAnchor =
  Square.leakageToResidualProved

recordsAbelTriadicDefectMeasureBoundary :
  NSAbelTriadicDefectMeasureConstructionBoundaryRecorded ≡ true
recordsAbelTriadicDefectMeasureBoundary =
  refl

typesLPAbelTriadicMeasureObligation :
  LPAbelTriadicMeasureObligationTyped ≡ true
typesLPAbelTriadicMeasureObligation =
  refl

typesOutputSupportTransferObligation :
  OutputSupportTransferObligationTyped ≡ true
typesOutputSupportTransferObligation =
  refl

typesOffDiagonalInteractionErrorObligation :
  OffDiagonalInteractionErrorObligationTyped ≡ true
typesOffDiagonalInteractionErrorObligation =
  refl

typesNormalizationAgainstDrObligation :
  NormalizationAgainstDrObligationTyped ≡ true
typesNormalizationAgainstDrObligation =
  refl

typesRelationToLeiRenTian :
  RelationToLeiRenTianTyped ≡ true
typesRelationToLeiRenTian =
  refl

typesRelationToSquareFunctionCoercivity :
  RelationToSquareFunctionCoercivityTyped ≡ true
typesRelationToSquareFunctionCoercivity =
  refl

keepsAbelTriadicDefectMeasureConstructionFalse :
  AbelTriadicDefectMeasureConstructed ≡ false
keepsAbelTriadicDefectMeasureConstructionFalse =
  refl

keepsOutputSupportTransferFalse :
  OutputSupportTransferProved ≡ false
keepsOutputSupportTransferFalse =
  refl

keepsOffDiagonalInteractionErrorFalse :
  OffDiagonalInteractionErrorClosed ≡ false
keepsOffDiagonalInteractionErrorFalse =
  refl

keepsNormalizationAgainstDrFalse :
  NormalizationAgainstDrProved ≡ false
keepsNormalizationAgainstDrFalse =
  refl

keepsPlancherelTriadicToSquareFunctionFalse :
  PlancherelTriadicToSquareFunctionProved ≡ false
keepsPlancherelTriadicToSquareFunctionFalse =
  refl

keepsTriadicLeakageSquareFunctionCoercivityFalse :
  TriadicLeakageSquareFunctionCoercivityProved ≡ false
keepsTriadicLeakageSquareFunctionCoercivityFalse =
  refl

keepsCriticalResidualFalse :
  NSCriticalResidualNonPositive ≡ false
keepsCriticalResidualFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  FullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsMechanismExhaustionFalse :
  MechanismExhaustionForFullClayNS ≡ false
keepsMechanismExhaustionFalse =
  refl

keepsClayNavierStokesPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

anchorsExactTrueLeraySymbol :
  symbolExactLerayTriadicAnchor ≡ true
anchorsExactTrueLeraySymbol =
  refl

anchorsWidthStillFalse :
  symbolWidthStillFalseAnchor ≡ false
anchorsWidthStillFalse =
  refl

anchorsMicrolocalMeasureStillFalse :
  microDefectMassStillFalseAnchor ≡ false
anchorsMicrolocalMeasureStillFalse =
  refl

anchorsLRTBoundaryRecorded :
  lrtBoundaryRecordedAnchor ≡ true
anchorsLRTBoundaryRecorded =
  refl

anchorsLRTMeasureTransferStillFalse :
  lrtDirectionSetMeasureTransferStillFalseAnchor ≡ false
anchorsLRTMeasureTransferStillFalse =
  refl

anchorsSheafAbelMeasureRecorded :
  sheafAbelMeasureRecordedAnchor ≡ true
anchorsSheafAbelMeasureRecorded =
  refl

anchorsSheafAbelMeasureConstructedStillFalse :
  sheafAbelMeasureConstructedStillFalseAnchor ≡ false
anchorsSheafAbelMeasureConstructedStillFalse =
  refl

anchorsSquareFunctionCoercivityStillFalse :
  squareFunctionCoercivityStillFalseAnchor ≡ false
anchorsSquareFunctionCoercivityStillFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F control card.

organizationString : String
organizationString =
  "O: NSAbelTriadicDefectMeasureConstructionBoundary is coding lane 4's isolated fail-closed receipt for the Abel/LP triadic measure construction."

requirementString : String
requirementString =
  "R: Record the Abel-weighted defect-measure contract: bounded mass, weak-* compactness, D_r normalization, quantitative off-diagonal control, Lei-Ren-Tian output-support transfer, and the feed into the A1/A3 bootstrap, without proving them."

codeArtifactString : String
codeArtifactString =
  "C: The module exports carriers for blowup profiles, parabolic scales, LP shells, Abel weights, true Leray triadic blocks, measure boundaries, support transfer, error rows, blockers, status rows, and imported anchors."

stateString : String
stateString =
  "S: True Leray symbol, triadic sheaf, LRT boundary, microlocal boundary, and square-function boundary are linked; bounded mass, weak-* extraction, quantitative compactness for A1/A3, normalization, transfer, off-diagonal control, Plancherel, residual depletion, and Clay promotion remain false."

latticeString : String
latticeString =
  "L: residual cascade -> LP shells -> Abel weighted true-Leray triadic blocks -> bounded-mass weak-* compactness of mu_r -> D_r normalization and off-diagonal control -> A1/A3 bootstrap feed -> LRT output support -> leakage mass -> square-function coercivity blocker."

proposalString : String
proposalString =
  "P: Promote only the typed obligation surface and imported fail-closed anchors; route downstream proof work first to bounded mass plus weak-* compactness with quantitative A1/A3 control, then to output support transfer, off-diagonal estimates, and Plancherel-to-square-function coercivity."

governanceString : String
governanceString =
  "G: The receipt is non-promotional; theorem-completion, residual, monotonicity, mechanism-exhaustion, and Clay flags are all false."

gapString : String
gapString =
  "F: Missing evidence is the Abel-weighted bounded-mass estimate, weak-* extraction with quantitative control strong enough for the A1/A3 bootstrap, D_r-normalized nonzero mass, off-diagonal interaction decay, LRT direction-set to pi_out support transfer, and Plancherel identification with the leakage square function."

record AbelTriadicDefectMeasureORCSLPGF : Set where
  constructor abelTriadicDefectMeasureORCSLPGF
  field
    O : String
    R : String
    C : String
    S : String
    L : String
    P : String
    G : String
    F : String

canonicalAbelTriadicDefectMeasureORCSLPGF :
  AbelTriadicDefectMeasureORCSLPGF
canonicalAbelTriadicDefectMeasureORCSLPGF =
  abelTriadicDefectMeasureORCSLPGF
    organizationString
    requirementString
    codeArtifactString
    stateString
    latticeString
    proposalString
    governanceString
    gapString

canonicalNSAbelTriadicDefectMeasureConstructionBoundaryReceipt :
  NSAbelTriadicDefectMeasureConstructionBoundary
canonicalNSAbelTriadicDefectMeasureConstructionBoundaryReceipt =
  canonicalNSAbelTriadicDefectMeasureConstructionBoundary
