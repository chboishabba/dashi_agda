module DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- RECURSIVE SELECTIVE INVALIDATION / PARETO TRUTH MAINTENANCE
--
-- One maintenance round produces the next frontier. The ambient language may
-- grow recursively/self-indexedly, but the next round materialises only axes
-- declared relevant by the changed dependency frontier. Old materialised axes
-- retain their semantic meaning and old candidate costs unless an explicit
-- invalidation witness names that axis as changed.
------------------------------------------------------------------------

record RecursiveMaintenanceLayer : Set₁ where
  constructor recursive-maintenance-layer
  field
    layerIndex : Nat
    ambient : Pareto.AmbientAxisCapacity
    MaterialisedAxis : Set
    includeAxis : MaterialisedAxis → Pareto.FrontierAxis
    Candidate : Set
    includeCandidate : Candidate → Pareto.CertificateCandidate
    candidateClass : Candidate → Pareto.RecomputeClass
    axisReference : MaterialisedAxis → String
    candidateReference : Candidate → String

open RecursiveMaintenanceLayer public

record ExplicitAxisInvalidation
    (lower : RecursiveMaintenanceLayer) : Set₁ where
  constructor explicit-axis-invalidation
  field
    InvalidatedAxis : Set
    invalidatedAxis : InvalidatedAxis → MaterialisedAxis lower
    invalidationReference : InvalidatedAxis → String

open ExplicitAxisInvalidation public

NotInvalidated :
  {lower : RecursiveMaintenanceLayer} →
  ExplicitAxisInvalidation lower →
  MaterialisedAxis lower → Set
NotInvalidated invalidation axis =
  (i : InvalidatedAxis invalidation) →
  invalidatedAxis invalidation i ≡ axis → ⊥

record RecursiveMaintenanceStep
    (lower upper : RecursiveMaintenanceLayer)
    (invalidation : ExplicitAxisInvalidation lower) : Set₁ where
  constructor recursive-maintenance-step
  field
    liftAxis : MaterialisedAxis lower → MaterialisedAxis upper
    liftCandidate : Candidate lower → Candidate upper
    inheritedAxisMeaningPreserved :
      (axis : MaterialisedAxis lower) →
      NotInvalidated invalidation axis →
      includeAxis upper (liftAxis axis) ≡ includeAxis lower axis
    inheritedClassPreserved :
      (candidate : Candidate lower) →
      candidateClass upper (liftCandidate candidate) ≡ candidateClass lower candidate
    inheritedCostPreserved :
      (axis : MaterialisedAxis lower) →
      NotInvalidated invalidation axis →
      (candidate : Candidate lower) →
      Pareto.axisCost
        (includeAxis upper (liftAxis axis))
        (includeCandidate upper (liftCandidate candidate))
      ≡
      Pareto.axisCost
        (includeAxis lower axis)
        (includeCandidate lower candidate)
    newAxesAreResidualRelevant : MaterialisedAxis upper → Set
    stepReference : String

open RecursiveMaintenanceStep public

record RecursiveMaintenanceBoundary : Set where
  constructor recursive-maintenance-boundary
  field
    changedSubgraphMayOpenNextFrontier : Bool
    unaffectedAxesKeepMeaning : Bool
    unaffectedAxesKeepInheritedCosts : Bool
    ambientCapacityGrowthForcesFullMaterialisation : Bool
    recursiveParetoChoiceCreatesTruth : Bool
    recursiveParetoChoiceCreatesAuthority : Bool

canonicalRecursiveMaintenanceBoundary : RecursiveMaintenanceBoundary
canonicalRecursiveMaintenanceBoundary =
  recursive-maintenance-boundary true true true false false false

------------------------------------------------------------------------
-- Exact finite two-round calibration.
------------------------------------------------------------------------

data Axis0 : Set where
  consequence0 diagnostic0 authority0 cost0 : Axis0

data Candidate0 : Set where
  model0 frame0 : Candidate0

axis0ToFrontier : Axis0 → Pareto.FrontierAxis
axis0ToFrontier consequence0 = Pareto.consequenceAxis
axis0ToFrontier diagnostic0 = Pareto.diagnosticAxis
axis0ToFrontier authority0 = Pareto.authorityAxis
axis0ToFrontier cost0 = Pareto.recomputeCostAxis

candidate0ToCertificate : Candidate0 → Pareto.CertificateCandidate
candidate0ToCertificate model0 = Pareto.modelBranch
candidate0ToCertificate frame0 = Pareto.frameBranch

candidate0Class : Candidate0 → Pareto.RecomputeClass
candidate0Class model0 = Pareto.mustRecompute
candidate0Class frame0 = Pareto.provablyUnaffected

layer0 : RecursiveMaintenanceLayer
layer0 =
  recursive-maintenance-layer
    0
    Pareto.canonicalAmbientCapacity
    Axis0
    axis0ToFrontier
    Candidate0
    candidate0ToCertificate
    candidate0Class
    axisRef
    candidateRef
  where
    axisRef : Axis0 → String
    axisRef consequence0 = "consequence"
    axisRef diagnostic0 = "diagnostic residual"
    axisRef authority0 = "authority penalty"
    axisRef cost0 = "recompute cost"

    candidateRef : Candidate0 → String
    candidateRef model0 = "model branch"
    candidateRef frame0 = "frame branch"

-- A later dependency change explicitly invalidates only the diagnostic axis.
data Invalidated0 : Set where
  diagnosticChanged : Invalidated0

invalidation0 : ExplicitAxisInvalidation layer0
invalidation0 =
  explicit-axis-invalidation
    Invalidated0
    invalidated
    reference
  where
    invalidated : Invalidated0 → Axis0
    invalidated diagnosticChanged = diagnostic0

    reference : Invalidated0 → String
    reference diagnosticChanged =
      "later result changes diagnostic residual semantics on the reopened subgraph"

consequenceNotInvalidated : NotInvalidated invalidation0 consequence0
consequenceNotInvalidated diagnosticChanged ()

authorityNotInvalidated : NotInvalidated invalidation0 authority0
authorityNotInvalidated diagnosticChanged ()

costNotInvalidated : NotInvalidated invalidation0 cost0
costNotInvalidated diagnosticChanged ()

-- Upper layer materialises the inherited four axes plus one new residual axis.
data Axis1 : Set where
  consequence1 diagnostic1 authority1 cost1 lineageResidual1 : Axis1

data Candidate1 : Set where
  model1 frame1 lineageDebugger1 : Candidate1

axis1ToFrontier : Axis1 → Pareto.FrontierAxis
axis1ToFrontier consequence1 = Pareto.consequenceAxis
axis1ToFrontier diagnostic1 = Pareto.diagnosticAxis
axis1ToFrontier authority1 = Pareto.authorityAxis
axis1ToFrontier cost1 = Pareto.recomputeCostAxis
axis1ToFrontier lineageResidual1 = Pareto.diagnosticAxis

candidate1ToCertificate : Candidate1 → Pareto.CertificateCandidate
candidate1ToCertificate model1 = Pareto.modelBranch
candidate1ToCertificate frame1 = Pareto.frameBranch
candidate1ToCertificate lineageDebugger1 = Pareto.frameDebugger

candidate1Class : Candidate1 → Pareto.RecomputeClass
candidate1Class model1 = Pareto.mustRecompute
candidate1Class frame1 = Pareto.provablyUnaffected
candidate1Class lineageDebugger1 = Pareto.mayRecompute

layer1 : RecursiveMaintenanceLayer
layer1 =
  recursive-maintenance-layer
    1
    (Pareto.ambient-axis-capacity
      4
      (Pareto.selfIndexedCapacity 4)
      4
      19683
      "next recursive capacity level; semantic Pareto dimension remains four"
      true)
    Axis1
    axis1ToFrontier
    Candidate1
    candidate1ToCertificate
    candidate1Class
    axisRef
    candidateRef
  where
    axisRef : Axis1 → String
    axisRef consequence1 = "inherited consequence"
    axisRef diagnostic1 = "reopened diagnostic residual"
    axisRef authority1 = "inherited authority penalty"
    axisRef cost1 = "inherited recompute cost"
    axisRef lineageResidual1 = "new residual-relevant lineage diagnostic coordinate"

    candidateRef : Candidate1 → String
    candidateRef model1 = "lifted model branch"
    candidateRef frame1 = "lifted frame branch"
    candidateRef lineageDebugger1 = "new lineage debugger"

liftAxis01 : Axis0 → Axis1
liftAxis01 consequence0 = consequence1
liftAxis01 diagnostic0 = diagnostic1
liftAxis01 authority0 = authority1
liftAxis01 cost0 = cost1

liftCandidate01 : Candidate0 → Candidate1
liftCandidate01 model0 = model1
liftCandidate01 frame0 = frame1

recursiveStep01 : RecursiveMaintenanceStep layer0 layer1 invalidation0
recursiveStep01 =
  recursive-maintenance-step
    liftAxis01
    liftCandidate01
    meaning
    classPreserved
    costPreserved
    residualRelevant
    "recursive selective invalidation step: only diagnostic coordinate is explicitly invalidated; consequence/authority/cost semantics and costs are inherited; one new lineage residual is materialised"
  where
    meaning :
      (axis : Axis0) →
      NotInvalidated invalidation0 axis →
      axis1ToFrontier (liftAxis01 axis) ≡ axis0ToFrontier axis
    meaning consequence0 proof = refl
    meaning diagnostic0 proof = ⊥-elim (proof diagnosticChanged refl)
    meaning authority0 proof = refl
    meaning cost0 proof = refl

    classPreserved :
      (candidate : Candidate0) →
      candidate1Class (liftCandidate01 candidate) ≡ candidate0Class candidate
    classPreserved model0 = refl
    classPreserved frame0 = refl

    costPreserved :
      (axis : Axis0) →
      NotInvalidated invalidation0 axis →
      (candidate : Candidate0) →
      Pareto.axisCost
        (axis1ToFrontier (liftAxis01 axis))
        (candidate1ToCertificate (liftCandidate01 candidate))
      ≡
      Pareto.axisCost
        (axis0ToFrontier axis)
        (candidate0ToCertificate candidate)
    costPreserved consequence0 proof model0 = refl
    costPreserved consequence0 proof frame0 = refl
    costPreserved diagnostic0 proof candidate = ⊥-elim (proof diagnosticChanged refl)
    costPreserved authority0 proof model0 = refl
    costPreserved authority0 proof frame0 = refl
    costPreserved cost0 proof model0 = refl
    costPreserved cost0 proof frame0 = refl

    residualRelevant : Axis1 → Set
    residualRelevant consequence1 = ⊤
    residualRelevant diagnostic1 = ⊤
    residualRelevant authority1 = ⊤
    residualRelevant cost1 = ⊤
    residualRelevant lineageResidual1 = ⊤

inheritedConsequenceCostPreservedOnModel :
  Pareto.axisCost (axis1ToFrontier consequence1) Pareto.modelBranch
  ≡ Pareto.axisCost Pareto.consequenceAxis Pareto.modelBranch
inheritedConsequenceCostPreservedOnModel = refl

frameClassStillUnaffectedAfterRecursiveLift :
  candidateClass layer1 (liftCandidate recursiveStep01 frame0)
  ≡ Pareto.provablyUnaffected
frameClassStillUnaffectedAfterRecursiveLift = refl

newLineageAxisMaterialisedWithoutChangingParetoDimension :
  Pareto.declaredSemanticAxisCount (ambient layer1) ≡ 4
newLineageAxisMaterialisedWithoutChangingParetoDimension = refl

nextCapacityIsSymbolic :
  Pareto.capacityExpression (ambient layer1) ≡ Pareto.selfIndexedCapacity 4
nextCapacityIsSymbolic = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RecursiveLiftSilentlyChangesUnaffectedCosts : Set where
data NewResidualAxisChangesParetoDimensionAutomatically : Set where
data NextCapacityForcesEnumeratingCapacity : Set where
data UnaffectedCandidateBecomesDirtyByLiftAlone : Set where

recursiveLiftCannotSilentlyChangeUnaffectedCosts :
  RecursiveLiftSilentlyChangesUnaffectedCosts → ⊥
recursiveLiftCannotSilentlyChangeUnaffectedCosts ()

newResidualAxisDoesNotChangeParetoDimensionAutomatically :
  NewResidualAxisChangesParetoDimensionAutomatically → ⊥
newResidualAxisDoesNotChangeParetoDimensionAutomatically ()

nextCapacityDoesNotForceEnumeration : NextCapacityForcesEnumeratingCapacity → ⊥
nextCapacityDoesNotForceEnumeration ()

unaffectedCandidateDoesNotBecomeDirtyByLiftAlone :
  UnaffectedCandidateBecomesDirtyByLiftAlone → ⊥
unaffectedCandidateDoesNotBecomeDirtyByLiftAlone ()
