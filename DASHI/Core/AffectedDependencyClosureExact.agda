module DASHI.Core.AffectedDependencyClosureExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact reverse-dependency closure for selective reopening.  The relation is
-- proof-bearing: `Depends source dependent` means changing `source` can require
-- reconsidering `dependent`.  Its reflexive/transitive closure is the minimal
-- mathematical object needed before any runtime algorithm claims selective
-- invalidation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)


data AffectedClosure
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    : Artifact → Artifact → Set where
  affectedRefl :
    ∀ {artifact} → AffectedClosure Depends artifact artifact
  affectedStep :
    ∀ {source middle target} →
    Depends source middle →
    AffectedClosure Depends middle target →
    AffectedClosure Depends source target

appendAffected :
  ∀ {Artifact}
    {Depends : Artifact → Artifact → Set}
    {source middle target} →
  AffectedClosure Depends source middle →
  AffectedClosure Depends middle target →
  AffectedClosure Depends source target
appendAffected affectedRefl right = right
appendAffected (affectedStep edge rest) right =
  affectedStep edge (appendAffected rest right)

record ReopeningObligation
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (changed target : Artifact) : Set where
  constructor reopeningObligation
  field
    dependencyPath : AffectedClosure Depends changed target

open ReopeningObligation public

oneEdgeCreatesReopeningObligation :
  ∀ {Artifact}
    {Depends : Artifact → Artifact → Set}
    {changed target} →
  Depends changed target →
  ReopeningObligation Depends changed target
oneEdgeCreatesReopeningObligation edge =
  reopeningObligation (affectedStep edge affectedRefl)

obligationsCompose :
  ∀ {Artifact}
    {Depends : Artifact → Artifact → Set}
    {changed middle target} →
  ReopeningObligation Depends changed middle →
  ReopeningObligation Depends middle target →
  ReopeningObligation Depends changed target
obligationsCompose first second =
  reopeningObligation
    (appendAffected
      (dependencyPath first)
      (dependencyPath second))

record DependencyClosureBoundary : Set where
  constructor dependencyClosureBoundary
  field
    directDependencyIsNotTheWholeAffectedRegion : Bool
    transitiveDependentsMustReopen : Bool
    unrelatedRetentionNeedsAbsenceOfDependencyPathEvidence : Bool
    covarianceOrCorrelationDoesNotReplaceDependencyProof : Bool

canonicalDependencyClosureBoundary : DependencyClosureBoundary
canonicalDependencyClosureBoundary =
  dependencyClosureBoundary true true true true
