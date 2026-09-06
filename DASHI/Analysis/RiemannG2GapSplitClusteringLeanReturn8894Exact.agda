module DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38

------------------------------------------------------------------------
-- CHECKED-LEAN RETURN: OPTIMIZED GAP SPLIT / TAPER-SHAPE NO-GO / DENSITY CUT
--
-- The §35 clustering inequality
--
--   (4/pi^2) * highGapMass < lowGapMass
--
-- is a NECESSARY condition for the gap-split LOWER BOUND to be positive.
-- Positivity of that lower bound is used by the checked Lean no-go theorems to
-- refute the small signed-scalar hypothesis when the floor reaches the consumer
-- threshold. Therefore clustering is an obstruction diagnostic for this route,
-- NOT a forward RH producer.
--
-- §37 closes the J*Lambda compatibility question and §38 owns zeta upper local
-- counting. Those facts narrow the obstruction audit, but they do not turn the
-- clustering condition into a proof obligation for RH.
------------------------------------------------------------------------

data CrossProverAuthority8894 : Set where
  checkedLeanReturn8894 openAgdaTransport : CrossProverAuthority8894

data GapSplitRouteState : Set where
  optimizedCriterionAvailable
  quadraticDecayDonorPruned
  clusteringRequired
  densityConstantWindowConditional
  : GapSplitRouteState

record GapSplitClusteringLeanReturn8894 : Set where
  constructor gap-split-clustering-lean-return-8894
  field
    aggregateJobs : String
    optimizationOwner : String
    shapeNoGoOwner : String
    densityCutOwner : String
    authority : CrossProverAuthority8894
    machineCheckedInLean : Bool
    machineCheckedInLeanIsTrue : machineCheckedInLean ≡ true
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

    optimizedThresholdOwned : Bool
    optimizedThresholdOwnedIsTrue : optimizedThresholdOwned ≡ true

    lowGapMultiplicityFloorOwned : Bool
    lowGapMultiplicityFloorOwnedIsTrue : lowGapMultiplicityFloorOwned ≡ true

    compactSupportShapeInequalityOwned : Bool
    compactSupportShapeInequalityOwnedIsTrue :
      compactSupportShapeInequalityOwned ≡ true

    optimizedPositiveCriterionFailsAtUnitLocalCount : Bool
    optimizedPositiveCriterionFailsAtUnitLocalCountIsTrue :
      optimizedPositiveCriterionFailsAtUnitLocalCount ≡ true

    positiveGapSplitRequiresLowGapClustering : Bool
    positiveGapSplitRequiresLowGapClusteringIsTrue :
      positiveGapSplitRequiresLowGapClustering ≡ true

    clusteringConditionIsGapSplitObstructionDiagnostic : Bool
    clusteringConditionIsGapSplitObstructionDiagnosticIsTrue :
      clusteringConditionIsGapSplitObstructionDiagnostic ≡ true

    clusteringDirectlyPaysRHScalarConsumer : Bool
    clusteringDirectlyPaysRHScalarConsumerIsFalse :
      clusteringDirectlyPaysRHScalarConsumer ≡ false

    densityBoundsCapCutoffOnInverseWidthScale : Bool
    densityBoundsCapCutoffOnInverseWidthScaleIsTrue :
      densityBoundsCapCutoffOnInverseWidthScale ≡ true

    quadraticDecaySharpeningCanRepairCriterion : Bool
    quadraticDecaySharpeningCanRepairCriterionIsFalse :
      quadraticDecaySharpeningCanRepairCriterion ≡ false

    taperWidthOrProfileRetuningCanRepairShapeLoss : Bool
    taperWidthOrProfileRetuningCanRepairShapeLossIsFalse :
      taperWidthOrProfileRetuningCanRepairShapeLoss ≡ false

    coarseCountingAloneSuppliesRequiredClustering : Bool
    coarseCountingAloneSuppliesRequiredClusteringIsFalse :
      coarseCountingAloneSuppliesRequiredClustering ≡ false

    densityCutRefutesEveryAdaptiveInverseWidthRoute : Bool
    densityCutRefutesEveryAdaptiveInverseWidthRouteIsFalse :
      densityCutRefutesEveryAdaptiveInverseWidthRoute ≡ false

    gammaPrecisionChangedByThisReturn : Bool
    gammaPrecisionChangedByThisReturnIsFalse :
      gammaPrecisionChangedByThisReturn ≡ false

    canonicalTestModulationChangedByThisReturn : Bool
    canonicalTestModulationChangedByThisReturnIsFalse :
      canonicalTestModulationChangedByThisReturn ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    optimizedCriterionReading : String
    shapeNoGoReading : String
    clusteringReading : String
    densityCutReading : String
    adaptiveReconciliationReading : String

open GapSplitClusteringLeanReturn8894 public

canonicalGapSplitClusteringLeanReturn8894 : GapSplitClusteringLeanReturn8894
canonicalGapSplitClusteringLeanReturn8894 =
  gap-split-clustering-lean-return-8894
    "8894"
    "Zeta23Bridge.NearCoreGapSplitOptimization"
    "Zeta23Bridge.NearCoreTaperShapeNoGo"
    "Zeta23Bridge.NearCoreClusteringDensityCut"
    checkedLeanReturn8894
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "At D = pi/(3 Lambda), lowGapMass * integral(q)/2 - escapeTerm <= integral(q*S), with lowGapMass >= 1 when a target-carrying near zero lies inside the optimized threshold."
    "The checked Lean return proves integral(q) <= Lambda^2 * integral(abs(q'')); applied to the determinant taper this makes the optimized POSITIVITY criterion impossible at unit local count. This prunes the transported quadratic-decay sufficient criterion; it does not prove the desired signed cancellation estimate."
    "If the gap-split lower bound is positive, then necessarily (4/pi^2) * highGapMass < lowGapMass. This quantifies when the NO-GO lower-bound mechanism could bite. It is not a theorem that this clustering holds, and proving it would not by itself pay the forward RH signed-scalar consumer."
    "With explicit short-window upper density A and long-window lower density c, positivity of the gap-split lower bound forces J < 1 + D + pi^2 A (2D+2)/(4c)."
    "The checked §37 return resolves the constant-window compatibility question and §38 resolves zeta upper local counting. These close two obstruction-audit coordinates. The forward RH leaf remains a consumer-sufficient signed target-centred scalar estimate on the literal G2 object, not the clustering diagnostic."

------------------------------------------------------------------------
-- 8896 return-to-owner welds.
------------------------------------------------------------------------

quarterDensityReconciliationChecked :
  Q37.QuarterPeriodDensityWindowReturn.machineCheckedInLean
    Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
quarterDensityReconciliationChecked = refl

quarterDensityComparisonNotAgdaProof :
  Q37.QuarterPeriodDensityWindowReturn.transportedIntoAgda
    Q37.canonicalQuarterPeriodDensityWindowReturn ≡ false
quarterDensityComparisonNotAgdaProof = refl

integerJointWindowOwnedInLean :
  Q37.QuarterPeriodDensityWindowReturn.explicitIntegerCutoffExistenceOwnedInLean
    Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
integerJointWindowOwnedInLean = refl

zetaUpperLocalCountChecked :
  Z38.ZetaLocalCountLeanReturn.importedProducerCheckedInLean
    Z38.canonicalZetaLocalCountLeanReturn ≡ true
zetaUpperLocalCountChecked = refl

zetaShortWindowUpperCountChecked :
  Z38.ZetaLocalCountLeanReturn.zetaShortWindowUpperCountOwnedInLean
    Z38.canonicalZetaLocalCountLeanReturn ≡ true
zetaShortWindowUpperCountChecked = refl

zetaLongWindowLowerDensityStillOpen :
  Z38.ZetaLocalCountLeanReturn.zetaLongWindowLowerDensityClosed
    Z38.canonicalZetaLocalCountLeanReturn ≡ false
zetaLongWindowLowerDensityStillOpen = refl

actualZetaClusteringStillOpen :
  Z38.ZetaLocalCountLeanReturn.actualZetaClusteringClosed
    Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringStillOpen = refl

clusteringIsObstructionDiagnostic :
  clusteringConditionIsGapSplitObstructionDiagnostic
    canonicalGapSplitClusteringLeanReturn8894 ≡ true
clusteringIsObstructionDiagnostic = refl

clusteringDoesNotDirectlyPayRH :
  clusteringDirectlyPaysRHScalarConsumer
    canonicalGapSplitClusteringLeanReturn8894 ≡ false
clusteringDoesNotDirectlyPayRH = refl

------------------------------------------------------------------------
-- Search classification.
------------------------------------------------------------------------

data GapSplitSearchAction : Set where
  sharpenSameQuadraticDecayDonor
  retuneTaperWidthOrProfile
  deriveClusteringFromCoarseCountingOnly
  reuseOptimizedGapSplitAsGrowingCutoffClosure
  recoverZetaUpperLocalCount
  compareQuarterPeriodLowerConstantWithDensityUpperConstant
  auditActualLowGapClusteringForObstruction
  supplyLongWindowLowerDensityForObstructionAudit
  pursueDifferentSignedMechanism
  repairGammaPrecisionInParallel
  continueCanonicalTestModulationInParallel
  : GapSplitSearchAction

GapSplitRelevant : GapSplitSearchAction → Set
GapSplitRelevant sharpenSameQuadraticDecayDonor = ⊥
GapSplitRelevant retuneTaperWidthOrProfile = ⊥
GapSplitRelevant deriveClusteringFromCoarseCountingOnly = ⊥
GapSplitRelevant reuseOptimizedGapSplitAsGrowingCutoffClosure = ⊥
GapSplitRelevant recoverZetaUpperLocalCount = ⊥
GapSplitRelevant compareQuarterPeriodLowerConstantWithDensityUpperConstant = ⊥
GapSplitRelevant auditActualLowGapClusteringForObstruction = ⊤
GapSplitRelevant supplyLongWindowLowerDensityForObstructionAudit = ⊤
GapSplitRelevant pursueDifferentSignedMechanism = ⊤
GapSplitRelevant repairGammaPrecisionInParallel = ⊤
GapSplitRelevant continueCanonicalTestModulationInParallel = ⊤

sameQuadraticDecayDonorPruned :
  GapSplitRelevant sharpenSameQuadraticDecayDonor → ⊥
sameQuadraticDecayDonorPruned x = x

taperRetuningPruned :
  GapSplitRelevant retuneTaperWidthOrProfile → ⊥
taperRetuningPruned x = x

coarseCountingClusteringPruned :
  GapSplitRelevant deriveClusteringFromCoarseCountingOnly → ⊥
coarseCountingClusteringPruned x = x

optimizedGapSplitGrowingCutoffClosurePruned :
  GapSplitRelevant reuseOptimizedGapSplitAsGrowingCutoffClosure → ⊥
optimizedGapSplitGrowingCutoffClosurePruned x = x

zetaUpperLocalCountSearchPruned :
  GapSplitRelevant recoverZetaUpperLocalCount → ⊥
zetaUpperLocalCountSearchPruned x = x

quarterDensityConstantComparisonPruned :
  GapSplitRelevant compareQuarterPeriodLowerConstantWithDensityUpperConstant → ⊥
quarterDensityConstantComparisonPruned x = x

-- Compatibility alias for older downstream code. The route-state constructor
-- `clusteringRequired` means required for POSITIVITY of the gap-split lower-bound
-- obstruction, not required as an RH proof producer.
currentGapSplitRouteState : GapSplitRouteState
currentGapSplitRouteState = clusteringRequired
