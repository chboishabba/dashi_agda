module DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact as Truth
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive

------------------------------------------------------------------------
-- DEPENDENCY-DERIVED MINIMAL INVALIDATION
--
-- The recursive owner previously accepted an ExplicitAxisInvalidation supplied
-- by the caller. This bridge removes the arbitrary-set seam. Applications
-- declare only the semantic dependency relation between graph artifacts and
-- currently materialised axes. A changed artifact invalidates exactly those
-- axes for which a proof-bearing affected path reaches an owning artifact.
------------------------------------------------------------------------

record DependencyInvalidationProblem
    (lower : Recursive.RecursiveMaintenanceLayer) : Set₁ where
  constructor dependency-invalidation-problem
  field
    Artifact : Set
    Depends : Artifact → Artifact → Set
    axisDependsOnArtifact : Artifact → Recursive.MaterialisedAxis lower → Set
    changedArtifact : Artifact
    problemReference : String

open DependencyInvalidationProblem public

AffectedSemanticAxis :
  {lower : Recursive.RecursiveMaintenanceLayer} →
  DependencyInvalidationProblem lower →
  Recursive.MaterialisedAxis lower → Set
AffectedSemanticAxis problem axis =
  Σ (Artifact problem) (λ target →
    Closure.AffectedClosure
      (Depends problem)
      (changedArtifact problem)
      target
    × axisDependsOnArtifact problem target axis)

DerivedInvalidatedAxis :
  {lower : Recursive.RecursiveMaintenanceLayer} →
  DependencyInvalidationProblem lower → Set
DerivedInvalidatedAxis {lower} problem =
  Σ (Recursive.MaterialisedAxis lower) (AffectedSemanticAxis problem)

derivedAxis :
  {lower : Recursive.RecursiveMaintenanceLayer}
  {problem : DependencyInvalidationProblem lower} →
  DerivedInvalidatedAxis problem → Recursive.MaterialisedAxis lower
derivedAxis (axis , witness) = axis

derivedExplicitInvalidation :
  {lower : Recursive.RecursiveMaintenanceLayer} →
  (problem : DependencyInvalidationProblem lower) →
  Recursive.ExplicitAxisInvalidation lower
derivedExplicitInvalidation problem =
  Recursive.explicit-axis-invalidation
    (DerivedInvalidatedAxis problem)
    derivedAxis
    (λ item → "dependency-derived invalidation: changed artifact reaches an artifact on which this semantic axis depends")

------------------------------------------------------------------------
-- Minimality: any sound invalidation predicate that covers all dependency-
-- affected axes contains the derived invalidation set.
------------------------------------------------------------------------

record InvalidationCover
    {lower : Recursive.RecursiveMaintenanceLayer}
    (problem : DependencyInvalidationProblem lower) : Set₁ where
  constructor invalidation-cover
  field
    invalidates : Recursive.MaterialisedAxis lower → Set
    coversAffected :
      (axis : Recursive.MaterialisedAxis lower) →
      AffectedSemanticAxis problem axis →
      invalidates axis
    coverReference : String

open InvalidationCover public

derivedInvalidationIsContainedInEveryCover :
  {lower : Recursive.RecursiveMaintenanceLayer}
  {problem : DependencyInvalidationProblem lower} →
  (cover : InvalidationCover problem) →
  (item : DerivedInvalidatedAxis problem) →
  invalidates cover (derivedAxis item)
derivedInvalidationIsContainedInEveryCover cover (axis , witness) =
  coversAffected cover axis witness

record MinimalInvalidationReceipt
    {lower : Recursive.RecursiveMaintenanceLayer}
    (problem : DependencyInvalidationProblem lower) : Set₁ where
  constructor minimal-invalidation-receipt
  field
    invalidation : Recursive.ExplicitAxisInvalidation lower
    invalidationIsDerived : invalidation ≡ derivedExplicitInvalidation problem
    everySoundCoverContainsDerived :
      (cover : InvalidationCover problem) →
      (item : DerivedInvalidatedAxis problem) →
      invalidates cover (derivedAxis item)
    receiptReference : String

open MinimalInvalidationReceipt public

canonicalMinimalInvalidationReceipt :
  {lower : Recursive.RecursiveMaintenanceLayer} →
  (problem : DependencyInvalidationProblem lower) →
  MinimalInvalidationReceipt problem
canonicalMinimalInvalidationReceipt problem =
  minimal-invalidation-receipt
    (derivedExplicitInvalidation problem)
    refl
    derivedInvalidationIsContainedInEveryCover
    "least dependency-derived invalidation: no caller-chosen extra axes are required"

------------------------------------------------------------------------
-- Exact fixture over the current incremental truth-maintenance graph.
--
-- For this consumer, only the diagnostic semantic coordinate is declared to
-- depend on the model artifact. The changed observation reaches model by the
-- existing typed edge, so diagnostic invalidation is derived mechanically.
-- Other semantic axes have no ownership declaration in this application-level
-- problem and therefore cannot appear in its derived minimal invalidation set.
------------------------------------------------------------------------

data AxisArtifactDependency :
    Truth.Artifact → Recursive.Axis0 → Set where
  modelOwnsDiagnostic :
    AxisArtifactDependency Truth.model Recursive.diagnostic0

observationReachesModel :
  Closure.AffectedClosure Truth.Depends Truth.observation Truth.model
observationReachesModel =
  Closure.affectedStep Truth.observationToModel Closure.affectedRefl

canonicalDependencyInvalidationProblem :
  DependencyInvalidationProblem Recursive.layer0
canonicalDependencyInvalidationProblem =
  dependency-invalidation-problem
    Truth.Artifact
    Truth.Depends
    AxisArtifactDependency
    Truth.observation
    "changed observation; derive affected semantic axes from typed reachability and application-declared axis ownership"

derivedDiagnosticInvalidation :
  DerivedInvalidatedAxis canonicalDependencyInvalidationProblem
derivedDiagnosticInvalidation =
  Recursive.diagnostic0 ,
    (Truth.model , (observationReachesModel , modelOwnsDiagnostic))

everyDerivedAxisInFixtureIsDiagnostic :
  (item : DerivedInvalidatedAxis canonicalDependencyInvalidationProblem) →
  derivedAxis item ≡ Recursive.diagnostic0
everyDerivedAxisInFixtureIsDiagnostic
  (Recursive.diagnostic0 , (Truth.model , (path , modelOwnsDiagnostic))) = refl

canonicalDerivedInvalidation : Recursive.ExplicitAxisInvalidation Recursive.layer0
canonicalDerivedInvalidation =
  derivedExplicitInvalidation canonicalDependencyInvalidationProblem

canonicalDerivedInvalidationTargetsDiagnostic :
  Recursive.invalidatedAxis canonicalDerivedInvalidation derivedDiagnosticInvalidation
  ≡ Recursive.diagnostic0
canonicalDerivedInvalidationTargetsDiagnostic = refl

------------------------------------------------------------------------
-- Worklist interpretation: each derived invalidation witness is already one
-- complete proof-bearing task. Grouping/rendering may reorder tasks but cannot
-- create or discard the underlying invalidation obligation.
------------------------------------------------------------------------

record InvalidationTask
    {lower : Recursive.RecursiveMaintenanceLayer}
    (problem : DependencyInvalidationProblem lower) : Set₁ where
  constructor invalidation-task
  field
    item : DerivedInvalidatedAxis problem
    taskReference : String

open InvalidationTask public

taskFromDerivedInvalidation :
  {lower : Recursive.RecursiveMaintenanceLayer}
  {problem : DependencyInvalidationProblem lower} →
  DerivedInvalidatedAxis problem → InvalidationTask problem
taskFromDerivedInvalidation item =
  invalidation-task item
    "worklist task is exactly one dependency-derived invalidation obligation"

data WorklistGroupingMayDeleteInvalidationObligation : Set where
data DependencyReachabilityCreatesAuthority : Set where
data AxisOwnershipAloneCreatesInvalidationWithoutChangedPath : Set where

worklistGroupingDoesNotDeleteObligation :
  WorklistGroupingMayDeleteInvalidationObligation → ⊥
worklistGroupingDoesNotDeleteObligation ()

dependencyReachabilityDoesNotCreateAuthority :
  DependencyReachabilityCreatesAuthority → ⊥
dependencyReachabilityDoesNotCreateAuthority ()

axisOwnershipNeedsReachableChangedPath :
  AxisOwnershipAloneCreatesInvalidationWithoutChangedPath → ⊥
axisOwnershipNeedsReachableChangedPath ()
