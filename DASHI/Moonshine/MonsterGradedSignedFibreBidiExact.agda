module DASHI.Moonshine.MonsterGradedSignedFibreBidiExact where

------------------------------------------------------------------------
-- MONSTER GRADED REPRESENTATION / SIGNED-FIBRE BIDI
--
-- The repository already owns grade-wise representations and traces.  This
-- module places a finite signed/gluing observer on each grade without
-- identifying that observer with the representation itself.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Foundations.Base369SignedMembershipExact as Signed
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Gluing

------------------------------------------------------------------------
-- 1. Fibre observer over every homogeneous grade.
------------------------------------------------------------------------

record GradedSignedFibreObserver
  {G K : Set}
  (group : GR.Group G)
  (graded : GR.GradedRepresentation G K group) : Setω where
  field
    signedOrientationAt : Nat → Signed.FibredOrientation
    gluingAt : Nat → Gluing.GluingState
    observerUsesSameGradeIndex : Bool

open GradedSignedFibreObserver public

record GradeFibreSnapshot
  {G K : Set}
  {group : GR.Group G}
  {graded : GR.GradedRepresentation G K group}
  (observer : GradedSignedFibreObserver group graded)
  (n : Nat) : Setω where
  constructor grade-fibre-snapshot
  field
    representation : GR.FiniteDimensionalRepresentation G K group
    representationIsGrade : representation ≡ GR.grade graded n
    signedOrientation : Signed.FibredOrientation
    signedOrientationIsObserved : signedOrientation ≡ signedOrientationAt observer n
    gluing : Gluing.GluingState
    gluingIsObserved : gluing ≡ gluingAt observer n

open GradeFibreSnapshot public

snapshotAt :
  {G K : Set} →
  {group : GR.Group G} →
  {graded : GR.GradedRepresentation G K group} →
  (observer : GradedSignedFibreObserver group graded) →
  (n : Nat) →
  GradeFibreSnapshot observer n
snapshotAt {graded = graded} observer n =
  grade-fibre-snapshot
    (GR.grade graded n)
    refl
    (signedOrientationAt observer n)
    refl
    (gluingAt observer n)
    refl

------------------------------------------------------------------------
-- 2. Same grade can carry a richer observer fibre than its dimension alone.
------------------------------------------------------------------------

record GradeObserverAdequacy : Set where
  constructor grade-observer-adequacy
  field
    dimensionAloneDeterminesSignedFibre : Bool
    traceAloneDeterminesBoundaryGluing : Bool
    signedFibreMayBeAdditionalCoordinate : Bool

canonicalGradeObserverAdequacy : GradeObserverAdequacy
canonicalGradeObserverAdequacy =
  grade-observer-adequacy false false true

------------------------------------------------------------------------
-- 3. BIDI: forward from graded representation, backward from modular j.
------------------------------------------------------------------------

data MonsterSignedFibreResidual : Set where
  missingGradeWiseSignedObserverFromMonsterAction : MonsterSignedFibreResidual
  missingGradeWiseGluingObserverFromModularGeometry : MonsterSignedFibreResidual
  missingTraceCompatibilityWithSignedFibre : MonsterSignedFibreResidual
  missingJCoefficientSameObjectIntertwiner : MonsterSignedFibreResidual

firstMonsterSignedFibreResidual : MonsterSignedFibreResidual
firstMonsterSignedFibreResidual =
  missingGradeWiseSignedObserverFromMonsterAction

record MonsterSignedFibreBidiFrontier : Set where
  constructor monster-signed-fibre-bidi-frontier
  field
    gradedActionTraceOwnerExists : Bool
    fibreObserverCanBeIndexedBySameGrade : Bool
    dimensionAutomaticallyDeterminesFibre : Bool
    traceAutomaticallyDeterminesGluing : Bool
    actualMonsterIntertwinerPaid : Bool
    firstResidual : MonsterSignedFibreResidual

canonicalMonsterSignedFibreBidiFrontier : MonsterSignedFibreBidiFrontier
canonicalMonsterSignedFibreBidiFrontier =
  monster-signed-fibre-bidi-frontier
    true true false false false
    firstMonsterSignedFibreResidual

dimensionDoesNotAutomaticallyDetermineFibre :
  MonsterSignedFibreBidiFrontier.dimensionAutomaticallyDeterminesFibre
    canonicalMonsterSignedFibreBidiFrontier ≡ false
dimensionDoesNotAutomaticallyDetermineFibre = refl
