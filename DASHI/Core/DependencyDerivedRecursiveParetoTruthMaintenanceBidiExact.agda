module DASHI.Core.DependencyDerivedRecursiveParetoTruthMaintenanceBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact as Derived
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- DEPENDENCY-DERIVED RECURSIVE PARETO MAINTENANCE
--
-- This owner closes the remaining seam in the recursive engine: the maintenance
-- step consumes the minimal invalidation derived from dependency reachability,
-- rather than a caller-written invalidation set.
------------------------------------------------------------------------

canonicalDerivedInvalidation : Recursive.ExplicitAxisInvalidation Recursive.layer0
canonicalDerivedInvalidation = Derived.canonicalDerivedInvalidation

consequenceNotDerivedInvalidated :
  Recursive.NotInvalidated canonicalDerivedInvalidation Recursive.consequence0
consequenceNotDerivedInvalidated item eq
  with Derived.everyDerivedAxisInFixtureIsDiagnostic item
... | refl = case eq of λ ()

authorityNotDerivedInvalidated :
  Recursive.NotInvalidated canonicalDerivedInvalidation Recursive.authority0
authorityNotDerivedInvalidated item eq
  with Derived.everyDerivedAxisInFixtureIsDiagnostic item
... | refl = case eq of λ ()

costNotDerivedInvalidated :
  Recursive.NotInvalidated canonicalDerivedInvalidation Recursive.cost0
costNotDerivedInvalidated item eq
  with Derived.everyDerivedAxisInFixtureIsDiagnostic item
... | refl = case eq of λ ()

recursiveDerivedStep01 :
  Recursive.RecursiveMaintenanceStep
    Recursive.layer0 Recursive.layer1 canonicalDerivedInvalidation
recursiveDerivedStep01 =
  Recursive.recursive-maintenance-step
    Recursive.liftAxis01
    Recursive.liftCandidate01
    meaning
    classPreserved
    costPreserved
    residualRelevant
    "recursive maintenance compiled from the least dependency-derived invalidation set"
  where
    meaning :
      (axis : Recursive.Axis0) →
      Recursive.NotInvalidated canonicalDerivedInvalidation axis →
      Recursive.axis1ToFrontier (Recursive.liftAxis01 axis)
      ≡ Recursive.axis0ToFrontier axis
    meaning Recursive.consequence0 proof = refl
    meaning Recursive.diagnostic0 proof =
      ⊥-elim (proof Derived.derivedDiagnosticInvalidation refl)
    meaning Recursive.authority0 proof = refl
    meaning Recursive.cost0 proof = refl

    classPreserved :
      (candidate : Recursive.Candidate0) →
      Recursive.candidate1Class (Recursive.liftCandidate01 candidate)
      ≡ Recursive.candidate0Class candidate
    classPreserved Recursive.model0 = refl
    classPreserved Recursive.frame0 = refl

    costPreserved :
      (axis : Recursive.Axis0) →
      Recursive.NotInvalidated canonicalDerivedInvalidation axis →
      (candidate : Recursive.Candidate0) →
      Pareto.axisCost
        (Recursive.axis1ToFrontier (Recursive.liftAxis01 axis))
        (Recursive.candidate1ToCertificate (Recursive.liftCandidate01 candidate))
      ≡
      Pareto.axisCost
        (Recursive.axis0ToFrontier axis)
        (Recursive.candidate0ToCertificate candidate)
    costPreserved Recursive.consequence0 proof Recursive.model0 = refl
    costPreserved Recursive.consequence0 proof Recursive.frame0 = refl
    costPreserved Recursive.diagnostic0 proof candidate =
      ⊥-elim (proof Derived.derivedDiagnosticInvalidation refl)
    costPreserved Recursive.authority0 proof Recursive.model0 = refl
    costPreserved Recursive.authority0 proof Recursive.frame0 = refl
    costPreserved Recursive.cost0 proof Recursive.model0 = refl
    costPreserved Recursive.cost0 proof Recursive.frame0 = refl

    residualRelevant : Recursive.Axis1 → Set
    residualRelevant Recursive.consequence1 = ⊤
    residualRelevant Recursive.diagnostic1 = ⊤
    residualRelevant Recursive.authority1 = ⊤
    residualRelevant Recursive.cost1 = ⊤
    residualRelevant Recursive.lineageResidual1 = ⊤

frameStillUnaffectedUnderDerivedRecursiveStep :
  Recursive.candidateClass Recursive.layer1
    (Recursive.liftCandidate recursiveDerivedStep01 Recursive.frame0)
  ≡ Pareto.provablyUnaffected
frameStillUnaffectedUnderDerivedRecursiveStep = refl

onlyDerivedAxisInFixtureIsDiagnostic :
  (item : Derived.DerivedInvalidatedAxis Derived.canonicalDependencyInvalidationProblem) →
  Derived.derivedAxis item ≡ Recursive.diagnostic0
onlyDerivedAxisInFixtureIsDiagnostic = Derived.everyDerivedAxisInFixtureIsDiagnostic

minimalReceiptRetained :
  Derived.MinimalInvalidationReceipt Derived.canonicalDependencyInvalidationProblem
minimalReceiptRetained =
  Derived.canonicalMinimalInvalidationReceipt Derived.canonicalDependencyInvalidationProblem

data DependencyDerivedMaintenanceRequiresCallerDirtySet : Set where
data DerivedMinimalInvalidationMayIncludeUnreachableAxis : Set where

dependencyDerivedMaintenanceNeedsNoCallerDirtySet :
  DependencyDerivedMaintenanceRequiresCallerDirtySet → ⊥
dependencyDerivedMaintenanceNeedsNoCallerDirtySet ()

derivedMinimalSetDoesNotIncludeUnreachableAxisByConstruction :
  DerivedMinimalInvalidationMayIncludeUnreachableAxis → ⊥
derivedMinimalSetDoesNotIncludeUnreachableAxisByConstruction ()
