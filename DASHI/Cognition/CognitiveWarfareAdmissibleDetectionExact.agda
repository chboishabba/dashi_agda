module DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact where

------------------------------------------------------------------------
-- COGNITIVE / INFLUENCE DETECTION AS AN OBSERVER-RELATIVE ADEQUACY PROBLEM
--
-- This is a finite structural instance only.  It does not classify any live
-- campaign, person, platform or state actor.
--
-- The point is to reuse the generic DASHI theorem spine:
--
--   target-visible collision
--     -> query-indexed non-factorability
--     -> add a source-native provenance coordinate
--     -> strict observer refinement
--     -> retest the same pair under admissible future evidence acquisition.
--
-- "Undetectable" is therefore never unqualified: it is relative to an
-- observation surface, a query and an admissible future evidence language.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerFutureAdequacyExact as Adequacy
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as FutureLanguage
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Fine histories and a target-local observation surface.
------------------------------------------------------------------------

data History : Set where
  organicHidden : History
  influenceHidden : History
  organicExposed : History
  influenceExposed : History

data TargetObservation : Set where
  sameTargetSurface : TargetObservation
  organicProvenanceVisible : TargetObservation
  influenceProvenanceVisible : TargetObservation

targetProject : History → TargetObservation
targetProject organicHidden = sameTargetSurface
targetProject influenceHidden = sameTargetSurface
targetProject organicExposed = organicProvenanceVisible
targetProject influenceExposed = influenceProvenanceVisible

data Origin : Set where
  organicOrigin : Origin
  influenceOrigin : Origin

origin : History → Origin
origin organicHidden = organicOrigin
origin influenceHidden = influenceOrigin
origin organicExposed = organicOrigin
origin influenceExposed = influenceOrigin

organicOriginNotInfluence :
  organicOrigin ≡ influenceOrigin → ⊥
organicOriginNotInfluence ()

targetLocalCollision :
  targetProject organicHidden
  ≡ targetProject influenceHidden
targetLocalCollision = refl

------------------------------------------------------------------------
-- Query-indexed present adequacy.
------------------------------------------------------------------------

data DetectionQuery : Set where
  originQuery : DetectionQuery

detectionSemantics :
  Query.QuerySemantics History DetectionQuery Origin
detectionSemantics =
  Query.querySemantics answer
  where
    answer : DetectionQuery → History → Origin
    answer originQuery = origin

data EvidenceAction : Set where
  inspectProvenance : EvidenceAction

data EvidencePrecondition : History → EvidenceAction → Set where
  organicInspectionReady :
    EvidencePrecondition organicHidden inspectProvenance
  influenceInspectionReady :
    EvidencePrecondition influenceHidden inspectProvenance

data EvidencePostcondition :
    History → EvidenceAction → History → Set where
  organicInspectionExposes :
    EvidencePostcondition
      organicHidden inspectProvenance organicExposed
  influenceInspectionExposes :
    EvidencePostcondition
      influenceHidden inspectProvenance influenceExposed

actionLabel : EvidenceAction → String
actionLabel inspectProvenance = "inspect-provenance"

evidenceSystem :
  Dependency.DependentActionSystem History EvidenceAction
evidenceSystem = record
  { Dependency.Precondition = EvidencePrecondition
  ; Dependency.Postcondition = EvidencePostcondition
  ; Dependency.actionLabel = actionLabel
  }

detectionProblem :
  Adequacy.AdmissibleConsumerProblem
    History EvidenceAction TargetObservation DetectionQuery Origin
detectionProblem =
  Adequacy.admissible-consumer-problem
    evidenceSystem
    targetProject
    detectionSemantics
    (λ query → ⊤)

originAdequacyDefect :
  Query.QueryAdequacyDefect
    targetProject
    detectionSemantics
    originQuery
originAdequacyDefect =
  Query.queryAdequacyDefect
    organicHidden
    influenceHidden
    refl
    organicOriginNotInfluence

canonicalAdmissibleDetectionDefect :
  Adequacy.AdmissibleAdequacyDefect
    detectionProblem
    originQuery
canonicalAdmissibleDetectionDefect =
  Adequacy.admissible-adequacy-defect
    tt
    originAdequacyDefect

targetSurfaceCannotDetermineOrigin :
  Adequacy.AdmissibleAdequateNow
    detectionProblem
    originQuery →
  ⊥
targetSurfaceCannotDetermineOrigin =
  Adequacy.admissibilityDoesNotRepairNonFactorability
    canonicalAdmissibleDetectionDefect

------------------------------------------------------------------------
-- Source-native refinement: retain the provenance/origin coordinate.
------------------------------------------------------------------------

targetPlusOriginStrictlyRefinesTarget :
  Observer.StrictRefinement
    targetProject
    (Observer.pairObserver targetProject origin)
targetPlusOriginStrictlyRefinesTarget =
  Observer.strictPairRefinement
    targetProject
    origin
    organicHidden
    influenceHidden
    refl
    organicOriginNotInfluence

------------------------------------------------------------------------
-- The same admissible future evidence action separates the collided histories.
------------------------------------------------------------------------

organicInspection :
  Dependency.AdmissibleAction
    evidenceSystem organicHidden inspectProvenance
organicInspection = record
  { Dependency.precondition = organicInspectionReady
  ; Dependency.after = organicExposed
  ; Dependency.postcondition = organicInspectionExposes
  ; Dependency.dependencyReceipt = "organic provenance inspection"
  }

influenceInspection :
  Dependency.AdmissibleAction
    evidenceSystem influenceHidden inspectProvenance
influenceInspection = record
  { Dependency.precondition = influenceInspectionReady
  ; Dependency.after = influenceExposed
  ; Dependency.postcondition = influenceInspectionExposes
  ; Dependency.dependencyReceipt = "influence provenance inspection"
  }

organicInspectionExecution :
  Reachability.Executes
    evidenceSystem
    (inspectProvenance ∷ [])
    organicHidden
    organicExposed
organicInspectionExecution =
  Reachability.executesCons
    organicInspection
    Reachability.executesNil

influenceInspectionExecution :
  Reachability.Executes
    evidenceSystem
    (inspectProvenance ∷ [])
    influenceHidden
    influenceExposed
influenceInspectionExecution =
  Reachability.executesCons
    influenceInspection
    Reachability.executesNil

futureTargetObservationsDiffer :
  targetProject organicExposed
  ≡ targetProject influenceExposed →
  ⊥
futureTargetObservationsDiffer ()

targetLocalCollisionIsNotFutureEquivalent :
  Future.FutureEquivalent
    evidenceSystem
    targetProject
    organicHidden
    influenceHidden →
  ⊥
targetLocalCollisionIsNotFutureEquivalent future =
  futureTargetObservationsDiffer
    (future
      organicInspectionExecution
      influenceInspectionExecution)

------------------------------------------------------------------------
-- Future-language observations are literally inside the admissible causal cone.
------------------------------------------------------------------------

organicFutureObservation :
  FutureLanguage.FutureObservation
    evidenceSystem
    targetProject
    organicHidden
    (inspectProvenance ∷ [])
    organicProvenanceVisible
organicFutureObservation =
  FutureLanguage.futureObservation
    organicExposed
    organicInspectionExecution
    refl

influenceFutureObservation :
  FutureLanguage.FutureObservation
    evidenceSystem
    targetProject
    influenceHidden
    (inspectProvenance ∷ [])
    influenceProvenanceVisible
influenceFutureObservation =
  FutureLanguage.futureObservation
    influenceExposed
    influenceInspectionExecution
    refl

organicObservationLiesInAdmissibleCone :
  Adequacy.AdmissibleConeObservation
    evidenceSystem
    targetProject
    organicHidden
    organicProvenanceVisible
organicObservationLiesInAdmissibleCone =
  Adequacy.futureObservationLiesInAdmissibleCone
    organicFutureObservation

influenceObservationLiesInAdmissibleCone :
  Adequacy.AdmissibleConeObservation
    evidenceSystem
    targetProject
    influenceHidden
    influenceProvenanceVisible
influenceObservationLiesInAdmissibleCone =
  Adequacy.futureObservationLiesInAdmissibleCone
    influenceFutureObservation

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record CognitiveDetectionBoundary : Set where
  constructor cognitive-detection-boundary
  field
    targetLocalEqualityImpliesOriginEquality : Bool
    targetLocalEqualityImpliesFutureEquivalence : Bool
    provenanceCoordinateCanStrictlyRefine : Bool
    futureEvidenceUsesAdmissibleReachability : Bool

canonicalCognitiveDetectionBoundary : CognitiveDetectionBoundary
canonicalCognitiveDetectionBoundary =
  cognitive-detection-boundary
    false false true true
