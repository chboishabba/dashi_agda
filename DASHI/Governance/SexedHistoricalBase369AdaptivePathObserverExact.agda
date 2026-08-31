module DASHI.Governance.SexedHistoricalBase369AdaptivePathObserverExact where

------------------------------------------------------------------------
-- BASE369-INDEXED ADAPTIVE OBSERVER FOR HISTORICAL CONSTRUCTION PATHS
--
-- Two ordered cross-construction histories can have the same coarse crossing
-- count and the same Base369 geometric stratum while differing in composite
-- endpoint.  The ternary neutral/refinement state therefore selects a
-- discriminating endpoint/sequence measurement instead of forcing a binary
-- conclusion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.SexedHistoricalBase369TransitionPathExact as Path
import DASHI.Governance.SexedHistoricalAdaptiveMeasurementRefinementExact as Existing

------------------------------------------------------------------------
-- 1. Two hidden path histories.
------------------------------------------------------------------------

data HiddenConstructionPath : Set where
  hiddenMasculineCrossBack
  hiddenFeminineCrossBack
  : HiddenConstructionPath

pathCode : HiddenConstructionPath → Path.CrossPath
pathCode hiddenMasculineCrossBack = Path.masculineCrossBack
pathCode hiddenFeminineCrossBack = Path.feminineCrossBack

trueComposite : HiddenConstructionPath → Path.CompositeChannel
trueComposite h = Path.compositeChannel (pathCode h)

coarseCrossSurface : HiddenConstructionPath → Path.CrossCountSurface
coarseCrossSurface h = Path.crossCount (pathCode h)

coarseCrossCannotRecoverComposite :
  INF.FactorsThrough coarseCrossSurface trueComposite → ⊥
coarseCrossCannotRecoverComposite =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      hiddenMasculineCrossBack
      hiddenFeminineCrossBack
      refl
      (λ ()))

------------------------------------------------------------------------
-- 2. Base369 coarse stratum also erases the endpoint distinction.  Both
--    admitted composites live on a corner, even though one closes at M->M and
--    the other at F->F.
------------------------------------------------------------------------

compositePoint : HiddenConstructionPath → Path.CompositeChannel → Strata.Geometry.Ternary27Point
compositePoint hiddenMasculineCrossBack _ = Path.mmAdmittedPoint
compositePoint hiddenFeminineCrossBack _ = Path.ffAdmittedPoint

compositeStratum : HiddenConstructionPath → Strata.VoxelStratum
compositeStratum h = Strata.voxelStratum (compositePoint h (trueComposite h))

sameCompositeStratum :
  compositeStratum hiddenMasculineCrossBack
  ≡ compositeStratum hiddenFeminineCrossBack
sameCompositeStratum = refl

base369StratumCannotRecoverComposite :
  INF.FactorsThrough compositeStratum trueComposite → ⊥
base369StratumCannotRecoverComposite =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      hiddenMasculineCrossBack
      hiddenFeminineCrossBack
      refl
      (λ ()))

------------------------------------------------------------------------
-- 3. Candidate observations.
------------------------------------------------------------------------

data PathMeasurement : Set where
  coarseStratumOnly
  crossingCountOnly
  endpointIdentity
  orderedSequence
  admissibilityReceipt
  : PathMeasurement

data PathMeasurementResult : Set where
  sameCornerStratum
  sameDoubleCrossing
  closesAtMasculine
  closesAtFeminine
  masculineFirstSequence
  feminineFirstSequence
  admittedReceipt
  : PathMeasurementResult

observe : PathMeasurement → HiddenConstructionPath → PathMeasurementResult
observe coarseStratumOnly _ = sameCornerStratum
observe crossingCountOnly _ = sameDoubleCrossing
observe endpointIdentity hiddenMasculineCrossBack = closesAtMasculine
observe endpointIdentity hiddenFeminineCrossBack = closesAtFeminine
observe orderedSequence hiddenMasculineCrossBack = masculineFirstSequence
observe orderedSequence hiddenFeminineCrossBack = feminineFirstSequence
observe admissibilityReceipt _ = admittedReceipt

coarseStratumDoesNotSeparate :
  observe coarseStratumOnly hiddenMasculineCrossBack
  ≡ observe coarseStratumOnly hiddenFeminineCrossBack
coarseStratumDoesNotSeparate = refl

admissibilityAloneDoesNotSeparate :
  observe admissibilityReceipt hiddenMasculineCrossBack
  ≡ observe admissibilityReceipt hiddenFeminineCrossBack
admissibilityAloneDoesNotSeparate = refl

endpointMeasurementSeparates :
  observe endpointIdentity hiddenMasculineCrossBack
  ≡ observe endpointIdentity hiddenFeminineCrossBack → ⊥
endpointMeasurementSeparates ()

sequenceMeasurementSeparates :
  observe orderedSequence hiddenMasculineCrossBack
  ≡ observe orderedSequence hiddenFeminineCrossBack → ⊥
sequenceMeasurementSeparates ()

------------------------------------------------------------------------
-- 4. Adaptive ternary selector.
------------------------------------------------------------------------

data PathResearchQuestion : Set where
  recoverCompositeEndpoint
  recoverConstructionOrder
  recoverAdmissibility
  : PathResearchQuestion

nextPathMeasurement :
  PathResearchQuestion → Suspension.EpistemicDisposition → PathMeasurement
nextPathMeasurement recoverCompositeEndpoint Suspension.suspendAndRefine = endpointIdentity
nextPathMeasurement recoverConstructionOrder Suspension.suspendAndRefine = orderedSequence
nextPathMeasurement recoverAdmissibility Suspension.suspendAndRefine = admissibilityReceipt
nextPathMeasurement _ Suspension.rejectHere = coarseStratumOnly
nextPathMeasurement _ Suspension.acceptHere = coarseStratumOnly

neutralCompositeQuestionSelectsEndpoint :
  nextPathMeasurement recoverCompositeEndpoint Suspension.suspendAndRefine
  ≡ endpointIdentity
neutralCompositeQuestionSelectsEndpoint = refl

neutralOrderQuestionSelectsSequence :
  nextPathMeasurement recoverConstructionOrder Suspension.suspendAndRefine
  ≡ orderedSequence
neutralOrderQuestionSelectsSequence = refl

selectedEndpointMeasurementSeparates :
  observe
    (nextPathMeasurement recoverCompositeEndpoint Suspension.suspendAndRefine)
    hiddenMasculineCrossBack
  ≡ observe
    (nextPathMeasurement recoverCompositeEndpoint Suspension.suspendAndRefine)
    hiddenFeminineCrossBack → ⊥
selectedEndpointMeasurementSeparates = endpointMeasurementSeparates

selectedSequenceMeasurementSeparates :
  observe
    (nextPathMeasurement recoverConstructionOrder Suspension.suspendAndRefine)
    hiddenMasculineCrossBack
  ≡ observe
    (nextPathMeasurement recoverConstructionOrder Suspension.suspendAndRefine)
    hiddenFeminineCrossBack → ⊥
selectedSequenceMeasurementSeparates = sequenceMeasurementSeparates

------------------------------------------------------------------------
-- 5. Cross-pollination with the earlier path-order observer.  The same design
--    principle is retained: the useful next measurement depends on the
--    consumer question, and a separator does not manufacture causal mechanism.
------------------------------------------------------------------------

existingPathQuestionStillSelectsSequence =
  Existing.unresolvedPathSelectsSequenceMeasurement

data Base369SeparatorPromotesCausalMechanism : Set where

data SameStratumPromotesSameHistory : Set where

data SameAdmissibilityPromotesSameComposite : Set where

base369SeparatorDoesNotPromoteCausalMechanism :
  Base369SeparatorPromotesCausalMechanism → ⊥
base369SeparatorDoesNotPromoteCausalMechanism ()

sameStratumDoesNotPromoteSameHistory : SameStratumPromotesSameHistory → ⊥
sameStratumDoesNotPromoteSameHistory ()

sameAdmissibilityDoesNotPromoteSameComposite :
  SameAdmissibilityPromotesSameComposite → ⊥
sameAdmissibilityDoesNotPromoteSameComposite ()

record SexedHistoricalBase369AdaptivePathObserverBoundary : Set where
  constructor sexed-historical-base369-adaptive-path-observer-boundary
  field
    sameCrossCountRecoversComposite : Bool
    sameVoxelStratumRecoversComposite : Bool
    admissibilityAloneRecoversComposite : Bool
    endpointMeasurementSeparatesCanonicalPaths : Bool
    sequenceMeasurementSeparatesCanonicalPaths : Bool
    neutralCanSelectQuestionIndexedMeasurement : Bool
    separatingMeasurementEstablishesCausalMechanism : Bool

canonicalSexedHistoricalBase369AdaptivePathObserverBoundary :
  SexedHistoricalBase369AdaptivePathObserverBoundary
canonicalSexedHistoricalBase369AdaptivePathObserverBoundary =
  sexed-historical-base369-adaptive-path-observer-boundary
    false false false true true true false
