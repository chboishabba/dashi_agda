module DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38

------------------------------------------------------------------------
-- CHECKED-LEAN RETURN: OPTIMIZED GAP SPLIT / TAPER-SHAPE NO-GO / DENSITY CUT
--
-- Original 8894 return:
--   NearCoreGapSplitOptimization.lean
--   NearCoreTaperShapeNoGo.lean
--   NearCoreClusteringDensityCut.lean
--
-- BIDI UPDATE (8896): this existing owner now consumes the checked §37 and §38
-- returns directly.  The old constant-window comparison is no longer a live
-- search leaf, and the zeta upper-count producer is no longer a hypothesis.
-- The first live zero-side analytic obligation is therefore the actual-zeta
-- clustering inequality itself.
--
-- Lean proofs remain Lean-owned; these imports synchronize theorem status and
-- search routing without pretending the real-analysis proofs were replayed in
-- Agda.
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
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "At D = pi/(3 Lambda), lowGapMass * integral(q)/2 - escapeTerm <= integral(q*S), with lowGapMass >= 1 when a target-carrying near zero lies inside the optimized threshold."
    "The checked Lean return proves integral(q) <= Lambda^2 * integral(abs(q'')); applied to the determinant taper this forces the optimized positivity criterion to imply (2J+1) A log(|t|+J+4) < pi^2/18, so the transported quadratic-decay sufficient criterion cannot be repaired by taper width or profile tuning once unit local count is present."
    "Any positive gap-split floor requires (4/pi^2) * highGapMass < lowGapMass. This is a genuine local clustering requirement; coarse counting, absolute envelopes, and sharper use of the same quadratic-decay donor do not supply it."
    "With explicit short-window upper density A and long-window lower density c, positivity forces J < 1 + D + pi^2 A (2D+2)/(4c). At D = pi/(3 Lambda) this is an inverse-width-scale cap J = O(1/Lambda)."
    "The later checked §37 return resolves the constant-window comparison: inverse-width scaling is compatible under its stated hypotheses, including an actual Nat cutoff existence theorem. The comparison leaf is therefore closed; genuine zeta clustering remains the live analytic payment."

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

------------------------------------------------------------------------
-- Search pruning / live route selection.
------------------------------------------------------------------------

data GapSplitSearchAction : Set where
  sharpenSameQuadraticDecayDonor
  retuneTaperWidthOrProfile
  deriveClusteringFromCoarseCountingOnly
  reuseOptimizedGapSplitAsGrowingCutoffClosure
  recoverZetaUpperLocalCount
  compareQuarterPeriodLowerConstantWithDensityUpperConstant
  proveNewLowGapClustering
  supplyLongWindowLowerDensity
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
GapSplitRelevant proveNewLowGapClustering = ⊤
GapSplitRelevant supplyLongWindowLowerDensity = ⊤
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

currentGapSplitRouteState : GapSplitRouteState
currentGapSplitRouteState = clusteringRequired
