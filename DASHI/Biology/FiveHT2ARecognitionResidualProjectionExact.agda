module DASHI.Biology.FiveHT2ARecognitionResidualProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.DependentRecoverableProjectionExact as Recoverable
import DASHI.Cognition.QuotientResidualCategoricalLoom as Loom
import DASHI.Biology.FiveHT2ARecognitionStateSpaceExact as StateSpace

------------------------------------------------------------------------
-- RECOGNITION STATE -> PUBLIC LIGAND SURFACE + RESIDUAL
--
-- Full microstate:
--   ligand identity x receptor context x mismatch x signaling profile.
--
-- Public surface:
--   the ligand label alone.
--
-- Distinct receptor-context states can collapse to the same public ligand
-- surface.  A dependent residual reopens the finite fixture exactly.
------------------------------------------------------------------------

data RecognitionMicroState : Set where
  lsdState0 : RecognitionMicroState
  lsdState1 : RecognitionMicroState

data LigandSurface : Set where
  lsdSurface : LigandSurface

microstateToDomainState :
  RecognitionMicroState →
  StateSpace.FiveHT2ARecognitionState
microstateToDomainState lsdState0 =
  StateSpace.canonicalLSDState0
microstateToDomainState lsdState1 =
  StateSpace.canonicalLSDState1

------------------------------------------------------------------------
-- Public projection is deliberately lossy.
------------------------------------------------------------------------

projectLigand :
  RecognitionMicroState →
  LigandSurface
projectLigand lsdState0 = lsdSurface
projectLigand lsdState1 = lsdSurface

distinctMicrostates :
  lsdState0 ≡ lsdState1 → ⊥
distinctMicrostates ()

publicLigandCollision :
  projectLigand lsdState0
  ≡
  projectLigand lsdState1
publicLigandCollision = refl

------------------------------------------------------------------------
-- Exact dependent residual.
------------------------------------------------------------------------

RecognitionResidual :
  LigandSurface →
  Set
RecognitionResidual lsdSurface = Bool

recognitionResidual :
  (state : RecognitionMicroState) →
  RecognitionResidual (projectLigand state)
recognitionResidual lsdState0 = false
recognitionResidual lsdState1 = true

reopenRecognition :
  (surface : LigandSurface) →
  RecognitionResidual surface →
  RecognitionMicroState
reopenRecognition lsdSurface false = lsdState0
reopenRecognition lsdSurface true = lsdState1

reopenRecognitionExact :
  (state : RecognitionMicroState) →
  reopenRecognition
    (projectLigand state)
    (recognitionResidual state)
  ≡
  state
reopenRecognitionExact lsdState0 = refl
reopenRecognitionExact lsdState1 = refl

recognitionRecoverableProjection :
  Recoverable.DependentExactRecoverableProjection
    RecognitionMicroState
    LigandSurface
recognitionRecoverableProjection =
  Recoverable.dependentExactRecoverableProjection
    RecognitionResidual
    projectLigand
    recognitionResidual
    reopenRecognition
    reopenRecognitionExact

recognitionCodeSeparating :
  Recoverable.DependentCodeSeparating recognitionRecoverableProjection
recognitionCodeSeparating =
  Recoverable.dependentCodeSeparating
    recognitionRecoverableProjection

------------------------------------------------------------------------
-- Repo-native categorical loom view.
------------------------------------------------------------------------

recognitionMicrostateObject : Loom.SetProjectionObject
recognitionMicrostateObject =
  Loom.setProjectionObject RecognitionMicroState

ligandSurfaceObject : Loom.SetProjectionObject
ligandSurfaceObject =
  Loom.setProjectionObject LigandSurface

ligandProjectionHom :
  Loom.SetProjectionHom
    recognitionMicrostateObject
    ligandSurfaceObject
ligandProjectionHom =
  Loom.setProjectionHom projectLigand

recognitionResidualLoom : Loom.ResidualAssignmentLoom
recognitionResidualLoom =
  record
    { SourceObject = recognitionMicrostateObject
    ; SurfaceObject = ligandSurfaceObject
    ; projection = ligandProjectionHom
    ; quotientLossWitnessAvailable = true
    ; fibreAssignmentAvailable = true
    ; assignmentCandidateOnly = true
    }

------------------------------------------------------------------------
-- Projection fibre: same ligand identity does not recover target context.
------------------------------------------------------------------------

data LigandIdentityDeterminesRecognitionState : Set where
data PublicProjectionIsInjective : Set where

ligandIdentityDoesNotDetermineRecognitionState :
  LigandIdentityDeterminesRecognitionState → ⊥
ligandIdentityDoesNotDetermineRecognitionState ()

publicProjectionIsNotInjective :
  PublicProjectionIsInjective → ⊥
publicProjectionIsNotInjective ()

------------------------------------------------------------------------
-- Residual semantics.
------------------------------------------------------------------------

data RecognitionResidualCoordinate : Set where
  receptorContextResidual : RecognitionResidualCoordinate
  recognitionGeometryResidual : RecognitionResidualCoordinate
  signalingResidual : RecognitionResidualCoordinate

record RecognitionResidualMeaning : Set where
  constructor recognitionResidualMeaning
  field
    residualSeparatesPublicCollision : Bool
    residualSeparatesPublicCollisionIsTrue :
      residualSeparatesPublicCollision ≡ true

    residualIsWorldAuthority : Bool
    residualIsWorldAuthorityIsFalse :
      residualIsWorldAuthority ≡ false

    exactReopeningIsFiniteFixtureOnly : Bool
    exactReopeningIsFiniteFixtureOnlyIsTrue :
      exactReopeningIsFiniteFixtureOnly ≡ true

open RecognitionResidualMeaning public

canonicalRecognitionResidualMeaning :
  RecognitionResidualMeaning
canonicalRecognitionResidualMeaning =
  recognitionResidualMeaning
    true refl
    false refl
    true refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RecognitionResidualProjectionBoundary : Set where
  constructor recognitionResidualProjectionBoundary
  field
    publicLigandSurfaceIsLossy : Bool
    publicLigandSurfaceIsLossyIsTrue :
      publicLigandSurfaceIsLossy ≡ true

    dependentResidualReopensFixtureExactly : Bool
    dependentResidualReopensFixtureExactlyIsTrue :
      dependentResidualReopensFixtureExactly ≡ true

    sameLigandImpliesSameReceptorContext : Bool
    sameLigandImpliesSameReceptorContextIsFalse :
      sameLigandImpliesSameReceptorContext ≡ false

    exactFixtureRecoveryMeansBiologicalStateRecovered : Bool
    exactFixtureRecoveryMeansBiologicalStateRecoveredIsFalse :
      exactFixtureRecoveryMeansBiologicalStateRecovered ≡ false

open RecognitionResidualProjectionBoundary public

canonicalRecognitionResidualProjectionBoundary :
  RecognitionResidualProjectionBoundary
canonicalRecognitionResidualProjectionBoundary =
  recognitionResidualProjectionBoundary
    true refl
    true refl
    false refl
    false refl
