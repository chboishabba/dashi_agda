module DASHI.Biology.TargetRecognitionFibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as Category
import DASHI.Core.ContextIndexedObservationFibrationExact as Fibration
import DASHI.Biology.TargetIndexedRecognitionGeometryExact as Geometry
import DASHI.Biology.ContextIndexedRecognitionGeometryExact as Context

------------------------------------------------------------------------
-- TARGET / CONTEXT BASE -> RECOGNITION-GEOMETRY FIBRE
--
-- This is a strict indexed/fibration-shaped DASHI extension.
-- It intentionally consumes ContextIndexedObservationFibrationExact rather
-- than claiming a new full Benabou/Grothendieck fibration theorem.
--
-- Base objects are target contexts.
-- Fine points are recognition mismatch vectors.
-- Public surface points retain the same mismatch vector.
-- Context-dependent recognition decisions are consumers of that indexed
-- observation, not part of the observation identity itself.
------------------------------------------------------------------------

data RecognitionBaseObject : Set where
  permissiveContextObject : RecognitionBaseObject
  strictContextObject : RecognitionBaseObject

-- Thin base category.  A morphism exists between any two context objects.
-- The categorical laws are trivial because the hom carrier is Unit.
recognitionBaseCategory : Category.ProjectionCategory
recognitionBaseCategory =
  record
    { Obj = RecognitionBaseObject
    ; Hom = λ _ _ → ⊤
    ; id = tt
    ; _∘_ = λ _ _ → tt
    ; id-left = λ _ → refl
    ; id-right = λ _ → refl
    ; assoc = λ _ _ _ → refl
    ; categoryReading =
        "Recognition-context base category: two context objects with a unique abstract context-change arrow."
    }

recognitionIndexedObservation :
  Fibration.ContextIndexedObservation recognitionBaseCategory
recognitionIndexedObservation =
  record
    { Fine = λ _ → Geometry.RecognitionMismatch
    ; Surface = λ _ → Geometry.RecognitionMismatch
    ; restrictFine = λ _ x → x
    ; restrictSurface = λ _ x → x
    ; observe = λ _ x → x
    ; restrictFineIdentity = λ _ → refl
    ; restrictSurfaceIdentity = λ _ → refl
    ; restrictFineComposition = λ _ _ _ → refl
    ; restrictSurfaceComposition = λ _ _ _ → refl
    ; observationNaturality = λ _ _ → refl
    }

------------------------------------------------------------------------
-- Canonical split lift is inherited directly from the repo-native fibration
-- owner.  The pair is transported without changing chemical identity/mismatch.
------------------------------------------------------------------------

permissiveToStrictChange :
  Category.Hom recognitionBaseCategory
    permissiveContextObject
    strictContextObject
permissiveToStrictChange = tt

canonicalRecognitionSplitLift :
  Fibration.TotalFineArrow recognitionIndexedObservation
    (Fibration.cartesianSource
      recognitionIndexedObservation
      permissiveToStrictChange
      Geometry.canonicalPairMismatch)
    (strictContextObject , Geometry.canonicalPairMismatch)
canonicalRecognitionSplitLift =
  Fibration.canonicalSplitLift
    recognitionIndexedObservation
    permissiveToStrictChange
    Geometry.canonicalPairMismatch

canonicalRecognitionObservationNaturality :
  Fibration.observe recognitionIndexedObservation permissiveContextObject
    (Fibration.restrictFine
      recognitionIndexedObservation
      permissiveToStrictChange
      Geometry.canonicalPairMismatch)
  ≡
  Fibration.restrictSurface
    recognitionIndexedObservation
    permissiveToStrictChange
    (Fibration.observe
      recognitionIndexedObservation
      strictContextObject
      Geometry.canonicalPairMismatch)
canonicalRecognitionObservationNaturality =
  Fibration.observationCommutesWithSplitLift
    recognitionIndexedObservation
    permissiveToStrictChange
    Geometry.canonicalPairMismatch

------------------------------------------------------------------------
-- Context-dependent recognition decision.
--
-- The transported fine point is identical, but its admission status changes
-- because the target/context fibre changes.
------------------------------------------------------------------------

data RecognitionAdmission : Set where
  admitted : RecognitionAdmission
  rejected : RecognitionAdmission

recognitionAdmissionAt :
  RecognitionBaseObject →
  Geometry.RecognitionMismatch →
  RecognitionAdmission
recognitionAdmissionAt permissiveContextObject mismatch =
  admitted
recognitionAdmissionAt strictContextObject mismatch =
  rejected

sameMismatchAcrossContextChange :
  Fibration.restrictFine
    recognitionIndexedObservation
    permissiveToStrictChange
    Geometry.canonicalPairMismatch
  ≡
  Geometry.canonicalPairMismatch
sameMismatchAcrossContextChange = refl

canonicalAdmissionChangesAcrossContext :
  recognitionAdmissionAt
    permissiveContextObject
    Geometry.canonicalPairMismatch
  ≡
  recognitionAdmissionAt
    strictContextObject
    Geometry.canonicalPairMismatch
  →
  ⊥
canonicalAdmissionChangesAcrossContext ()

------------------------------------------------------------------------
-- Bind the finite decision witness to the already-proved domain facts.
------------------------------------------------------------------------

permissiveContextDomainWitness :
  Context.AdmittedInContext
    Context.targetInContext0
    Geometry.canonicalPairMismatch
permissiveContextDomainWitness =
  Context.canonicalPairAdmittedInContext0

strictContextDomainRefutation :
  Context.AdmittedInContext
    Context.targetInContext1
    Geometry.canonicalPairMismatch
  →
  ⊥
strictContextDomainRefutation =
  Context.canonicalPairRejectedInContext1

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record TargetRecognitionFibrationBoundary : Set where
  constructor targetRecognitionFibrationBoundary
  field
    baseIsTargetContext : Bool
    baseIsTargetContextIsTrue :
      baseIsTargetContext ≡ true

    finePointTransportPreservesPairMismatch : Bool
    finePointTransportPreservesPairMismatchIsTrue :
      finePointTransportPreservesPairMismatch ≡ true

    recognitionDecisionCanChangeAcrossBaseContext : Bool
    recognitionDecisionCanChangeAcrossBaseContextIsTrue :
      recognitionDecisionCanChangeAcrossBaseContext ≡ true

    fullBenabouCartesianUniquenessClaimed : Bool
    fullBenabouCartesianUniquenessClaimedIsFalse :
      fullBenabouCartesianUniquenessClaimed ≡ false

    fullGrothendieckEquivalenceClaimed : Bool
    fullGrothendieckEquivalenceClaimedIsFalse :
      fullGrothendieckEquivalenceClaimed ≡ false

open TargetRecognitionFibrationBoundary public

canonicalTargetRecognitionFibrationBoundary :
  TargetRecognitionFibrationBoundary
canonicalTargetRecognitionFibrationBoundary =
  targetRecognitionFibrationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
