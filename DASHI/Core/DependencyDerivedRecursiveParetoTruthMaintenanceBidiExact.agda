module DASHI.Core.DependencyDerivedRecursiveParetoTruthMaintenanceBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact as Derived
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- DEPENDENCY-DERIVED RECURSIVE PARETO MAINTENANCE
--
-- The recursive maintenance step consumes the minimal invalidation derived from
-- dependency reachability, rather than a caller-written dirty set.
------------------------------------------------------------------------

diagnosticNotConsequence : Recursive.diagnostic0 ≡ Recursive.consequence0 → ⊥
diagnosticNotConsequence ()

diagnosticNotAuthority : Recursive.diagnostic0 ≡ Recursive.authority0 → ⊥
diagnosticNotAuthority ()

diagnosticNotCost : Recursive.diagnostic0 ≡ Recursive.cost0 → ⊥
diagnosticNotCost ()

------------------------------------------------------------------------
-- Reusable compiler for application problems whose derived minimal set is
-- exactly the diagnostic coordinate.
------------------------------------------------------------------------

diagnosticOnlyDerivedStep :
  (problem : Derived.DependencyInvalidationProblem Recursive.layer0) →
  (diagnosticWitness : Derived.DerivedInvalidatedAxis problem) →
  (diagnosticWitnessIsDiagnostic :
    Derived.derivedAxis diagnosticWitness ≡ Recursive.diagnostic0) →
  (allDerivedAreDiagnostic :
    (item : Derived.DerivedInvalidatedAxis problem) →
    Derived.derivedAxis item ≡ Recursive.diagnostic0) →
  Recursive.RecursiveMaintenanceStep
    Recursive.layer0 Recursive.layer1 (Derived.derivedExplicitInvalidation problem)
diagnosticOnlyDerivedStep problem diagnosticWitness diagnosticWitnessIsDiagnostic allDerivedAreDiagnostic =
  Recursive.recursive-maintenance-step
    Recursive.liftAxis01
    Recursive.liftCandidate01
    meaning
    classPreserved
    costPreserved
    residualRelevant
    "recursive maintenance compiled from the least dependency-derived diagnostic invalidation"
  where
    notConsequence :
      Recursive.NotInvalidated
        (Derived.derivedExplicitInvalidation problem)
        Recursive.consequence0
    notConsequence item eq with allDerivedAreDiagnostic item
    ... | refl = diagnosticNotConsequence eq

    notAuthority :
      Recursive.NotInvalidated
        (Derived.derivedExplicitInvalidation problem)
        Recursive.authority0
    notAuthority item eq with allDerivedAreDiagnostic item
    ... | refl = diagnosticNotAuthority eq

    notCost :
      Recursive.NotInvalidated
        (Derived.derivedExplicitInvalidation problem)
        Recursive.cost0
    notCost item eq with allDerivedAreDiagnostic item
    ... | refl = diagnosticNotCost eq

    meaning :
      (axis : Recursive.Axis0) →
      Recursive.NotInvalidated (Derived.derivedExplicitInvalidation problem) axis →
      Recursive.axis1ToFrontier (Recursive.liftAxis01 axis)
      ≡ Recursive.axis0ToFrontier axis
    meaning Recursive.consequence0 proof = refl
    meaning Recursive.diagnostic0 proof =
      ⊥-elim (proof diagnosticWitness diagnosticWitnessIsDiagnostic)
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
      Recursive.NotInvalidated (Derived.derivedExplicitInvalidation problem) axis →
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
      ⊥-elim (proof diagnosticWitness diagnosticWitnessIsDiagnostic)
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

canonicalDerivedInvalidation : Recursive.ExplicitAxisInvalidation Recursive.layer0
canonicalDerivedInvalidation = Derived.canonicalDerivedInvalidation

recursiveDerivedStep01 :
  Recursive.RecursiveMaintenanceStep
    Recursive.layer0 Recursive.layer1 canonicalDerivedInvalidation
recursiveDerivedStep01 =
  diagnosticOnlyDerivedStep
    Derived.canonicalDependencyInvalidationProblem
    Derived.derivedDiagnosticInvalidation
    refl
    Derived.everyDerivedAxisInFixtureIsDiagnostic

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
