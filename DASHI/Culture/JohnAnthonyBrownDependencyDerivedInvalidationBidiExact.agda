module DASHI.Culture.JohnAnthonyBrownDependencyDerivedInvalidationBidiExact where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown
import DASHI.Culture.JohnAnthonyBrownTemporalDiagnosisDependencyLineageBidiExact as Lineage
import DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact as Derived
import DASHI.Core.DependencyDerivedRecursiveParetoTruthMaintenanceBidiExact as Compiler
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN DEPENDENCY-DERIVED INVALIDATION
--
-- The current H1 diagnostic coordinate depends on the H1 association consumer.
-- A changed outcome-measurement artifact reaches that consumer through the
-- existing literal BrownDepends edge/path, so the recursive diagnostic
-- invalidation is graph-derived rather than hand selected.
------------------------------------------------------------------------

data BrownAxisDependency :
    Brown.BrownArtifact → Recursive.Axis0 → Set where
  h1OwnsDiagnostic :
    BrownAxisDependency Brown.h1AssociationClaim Recursive.diagnostic0

brownInvalidationProblem : Derived.DependencyInvalidationProblem Recursive.layer0
brownInvalidationProblem =
  Derived.dependency-invalidation-problem
    Brown.BrownArtifact
    Brown.BrownDepends
    BrownAxisDependency
    Brown.outcomeMeasurementEvidence
    "John Brown H1 outcome-measurement change; derive semantic invalidation from exact outcome -> H1 path"

brownDerivedDiagnosticInvalidation :
  Derived.DerivedInvalidatedAxis brownInvalidationProblem
brownDerivedDiagnosticInvalidation =
  Recursive.diagnostic0 ,
    (Brown.h1AssociationClaim , (Lineage.outcomeToH1Path , h1OwnsDiagnostic))

allBrownDerivedAxesAreDiagnostic :
  (item : Derived.DerivedInvalidatedAxis brownInvalidationProblem) →
  Derived.derivedAxis item ≡ Recursive.diagnostic0
allBrownDerivedAxesAreDiagnostic
  (Recursive.diagnostic0 , (Brown.h1AssociationClaim , (path , h1OwnsDiagnostic))) = refl

brownMinimalInvalidationReceipt : Derived.MinimalInvalidationReceipt brownInvalidationProblem
brownMinimalInvalidationReceipt = Derived.canonicalMinimalInvalidationReceipt brownInvalidationProblem

brownDerivedRecursiveStep :
  Recursive.RecursiveMaintenanceStep
    Recursive.layer0 Recursive.layer1
    (Derived.derivedExplicitInvalidation brownInvalidationProblem)
brownDerivedRecursiveStep =
  Compiler.diagnosticOnlyDerivedStep
    brownInvalidationProblem
    brownDerivedDiagnosticInvalidation
    refl
    allBrownDerivedAxesAreDiagnostic

historicalExposureAndH5RemainOutsideDerivedDirtySet :
  Recursive.candidateClass Recursive.layer1
    (Recursive.liftCandidate brownDerivedRecursiveStep Recursive.frame0)
  ≡ Pareto.provablyUnaffected
historicalExposureAndH5RemainOutsideDerivedDirtySet = refl

data H1OutcomeChangeMayDirtyUnreachableBrownAxis : Set where
data BrownDerivedInvalidationTransfersPolicyAuthority : Set where

h1OutcomeChangeDoesNotDirtyUnreachableAxisByMinimalConstruction :
  H1OutcomeChangeMayDirtyUnreachableBrownAxis → ⊥
h1OutcomeChangeDoesNotDirtyUnreachableAxisByMinimalConstruction ()

brownDerivedInvalidationDoesNotTransferPolicyAuthority :
  BrownDerivedInvalidationTransfersPolicyAuthority → ⊥
brownDerivedInvalidationDoesNotTransferPolicyAuthority ()
