module DASHI.Analysis.RiemannG2ScalarDonorRegimeReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Inventory
import DASHI.Analysis.RiemannG2NarrowWindowNoCancellationReturnExact as Narrow
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth

------------------------------------------------------------------------
-- SCALAR DONOR / WINDOW-REGIME RECONCILIATION
--
-- The inventory previously left open the possibility that some already-owned
-- exact target-centred scalar donor could simply be attached to the literal G2
-- problem. The checked narrow-window Lean return now refines that search:
-- on the literal regime J*Lambda <= pi/2, the correct exact theorem is a
-- positive pin/no-cancellation theorem. Therefore a cancellation donor cannot
-- close that unchanged narrow problem by sharper analysis alone.
--
-- A useful future donor must be attached either to a quarter-period-crossed
-- oscillatory problem, or to an explicitly changed comparison/problem object.
------------------------------------------------------------------------

data DonorRegime : Set where
  narrowPinnedProblem
  quarterPeriodCrossedProblem
  changedComparisonProblem
  : DonorRegime

data DonorUseDisposition : Set where
  noCancellationDonorPossibleBySharpening
  cancellationDonorSearchLive
  changedProblemDonorSearchLive
  : DonorUseDisposition

disposition : DonorRegime -> DonorUseDisposition
disposition narrowPinnedProblem = noCancellationDonorPossibleBySharpening
disposition quarterPeriodCrossedProblem = cancellationDonorSearchLive
disposition changedComparisonProblem = changedProblemDonorSearchLive

NarrowCancellationSearchRelevant : DonorRegime -> Set
NarrowCancellationSearchRelevant narrowPinnedProblem = ⊥
NarrowCancellationSearchRelevant quarterPeriodCrossedProblem = ⊤
NarrowCancellationSearchRelevant changedComparisonProblem = ⊤

narrowCancellationDonorSearchPruned :
  NarrowCancellationSearchRelevant narrowPinnedProblem -> ⊥
narrowCancellationDonorSearchPruned x = x

inventoryHasNoConcreteExactDonor :
  Inventory.concreteExactLiteralDonorIdentifiedInCurrentInventory ≡ false
inventoryHasNoConcreteExactDonor =
  Inventory.concreteExactLiteralDonorIdentifiedInCurrentInventoryIsFalse

quarterPeriodCrossingNecessary :
  Narrow.survivingRouteRequiresQuarterPeriodCrossing
    Narrow.canonicalNarrowWindowNoCancellationReturn ≡ true
quarterPeriodCrossingNecessary =
  Narrow.survivingRouteRequiresQuarterPeriodCrossingIsTrue
    Narrow.canonicalNarrowWindowNoCancellationReturn

currentGrowthStageRequiresCrossing :
  Growth.currentCutoffGrowthStage ≡ Growth.crossingLawRequired
currentGrowthStageRequiresCrossing = refl

record ScalarDonorRegimeBoundary : Set where
  constructor scalar-donor-regime-boundary
  field
    currentInventoryContainsNarrowCancellationDonor : Bool
    currentInventoryContainsNarrowCancellationDonorIsFalse :
      currentInventoryContainsNarrowCancellationDonor ≡ false

    sharperAnalysisCanTurnPinnedNarrowScalarIntoCancellation : Bool
    sharperAnalysisCanTurnPinnedNarrowScalarIntoCancellationIsFalse :
      sharperAnalysisCanTurnPinnedNarrowScalarIntoCancellation ≡ false

    usefulExactCancellationDonorMustCrossQuarterPeriodOrChangeProblem : Bool
    usefulExactCancellationDonorMustCrossQuarterPeriodOrChangeProblemIsTrue :
      usefulExactCancellationDonorMustCrossQuarterPeriodOrChangeProblem ≡ true

    donorSearchOnUnchangedNarrowProblemIsHighestAlpha : Bool
    donorSearchOnUnchangedNarrowProblemIsHighestAlphaIsFalse :
      donorSearchOnUnchangedNarrowProblemIsHighestAlpha ≡ false

    cutoffGrowthAndDownstreamCompatibilityAreHighestAlpha : Bool
    cutoffGrowthAndDownstreamCompatibilityAreHighestAlphaIsTrue :
      cutoffGrowthAndDownstreamCompatibilityAreHighestAlpha ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalScalarDonorRegimeBoundary : ScalarDonorRegimeBoundary
canonicalScalarDonorRegimeBoundary =
  scalar-donor-regime-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    "The exact-donor inventory and the checked Lean narrow-window theorem now agree: there is no useful cancellation theorem to discover on the unchanged regime J*Lambda <= pi/2, because the literal scalar is positively pinned there. A future exact donor must live after quarter-period crossing, or explicitly change the scalar/comparison problem. Hence the immediate RH search target is the same-object cutoff-growth law together with compatibility of the enlarged cutoff across near/far, Gamma, cluster, and explicit-formula consumers."
