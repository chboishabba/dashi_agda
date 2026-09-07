module DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownTemporalDiagnosisDependencyLineageBidiExact as Alice
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact as Derived
import DASHI.Core.DependencyDerivedRecursiveParetoTruthMaintenanceBidiExact as Compiler
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- ALICE BROWN DEPENDENCY-DERIVED INVALIDATION
--
-- Current application declaration: the diagnostic Pareto coordinate for the
-- voice/agency maintenance round depends on the student-voice audit surface.
-- The changed survey feedback artifact reaches that surface through the exact
-- existing AliceDepends edge, so the diagnostic invalidation is derived rather
-- than caller-supplied.
------------------------------------------------------------------------

data AliceAxisDependency :
    Alice.AliceAuditArtifact → Recursive.Axis0 → Set where
  voiceOwnsDiagnostic :
    AliceAxisDependency Alice.studentVoiceSurface Recursive.diagnostic0

surveyToVoicePath :
  Closure.AffectedClosure
    Alice.AliceDepends Alice.surveyFeedbackSurface Alice.studentVoiceSurface
surveyToVoicePath =
  Closure.affectedStep Alice.surveyFeedsVoiceAudit Closure.affectedRefl

aliceInvalidationProblem : Derived.DependencyInvalidationProblem Recursive.layer0
aliceInvalidationProblem =
  Derived.dependency-invalidation-problem
    Alice.AliceAuditArtifact
    Alice.AliceDepends
    AliceAxisDependency
    Alice.surveyFeedbackSurface
    "Alice survey-feedback change; derive semantic invalidation from survey -> student-voice reachability"

aliceDerivedDiagnosticInvalidation :
  Derived.DerivedInvalidatedAxis aliceInvalidationProblem
aliceDerivedDiagnosticInvalidation =
  Recursive.diagnostic0 ,
    (Alice.studentVoiceSurface , (surveyToVoicePath , voiceOwnsDiagnostic))

allAliceDerivedAxesAreDiagnostic :
  (item : Derived.DerivedInvalidatedAxis aliceInvalidationProblem) →
  Derived.derivedAxis item ≡ Recursive.diagnostic0
allAliceDerivedAxesAreDiagnostic
  (Recursive.diagnostic0 , (Alice.studentVoiceSurface , (path , voiceOwnsDiagnostic))) = refl

aliceMinimalInvalidationReceipt : Derived.MinimalInvalidationReceipt aliceInvalidationProblem
aliceMinimalInvalidationReceipt = Derived.canonicalMinimalInvalidationReceipt aliceInvalidationProblem

aliceDerivedRecursiveStep :
  Recursive.RecursiveMaintenanceStep
    Recursive.layer0 Recursive.layer1
    (Derived.derivedExplicitInvalidation aliceInvalidationProblem)
aliceDerivedRecursiveStep =
  Compiler.diagnosticOnlyDerivedStep
    aliceInvalidationProblem
    aliceDerivedDiagnosticInvalidation
    refl
    allAliceDerivedAxesAreDiagnostic

aliceParentObserverCandidateStillUnaffected :
  Recursive.candidateClass Recursive.layer1
    (Recursive.liftCandidate aliceDerivedRecursiveStep Recursive.frame0)
  ≡ Pareto.provablyUnaffected
aliceParentObserverCandidateStillUnaffected = refl

data AliceSurveyChangeMayDirtyUnreachableAxis : Set where
data AliceDerivedInvalidationCreatesStudentAuthority : Set where

aliceSurveyChangeDoesNotDirtyUnreachableAxisByMinimalConstruction :
  AliceSurveyChangeMayDirtyUnreachableAxis → ⊥
aliceSurveyChangeDoesNotDirtyUnreachableAxisByMinimalConstruction ()

aliceDerivedInvalidationDoesNotCreateStudentAuthority :
  AliceDerivedInvalidationCreatesStudentAuthority → ⊥
aliceDerivedInvalidationDoesNotCreateStudentAuthority ()
