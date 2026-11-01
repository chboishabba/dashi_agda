module DASHI.Core.ObserverSituatedReasonablenessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- SITUATED OBSERVER / REASONABLENESS CORE
--
-- A reasonableness judgment is indexed by an institutional/source context,
-- reference perspective, relevant-factor set, threshold, consequence query and
-- review standard.  This owner proves only finite observer insufficiency and
-- refinement results; observer-dependence is not identified with arbitrariness
-- or contentlessness.
------------------------------------------------------------------------

record ReasonablenessIndex : Set where
  constructor reasonablenessIndex
  field
    institutionReference : String
    sourceContextReference : String
    referencePerspective : String
    relevantFactorSetReference : String
    thresholdReference : String
    consequenceQueryReference : String
    reviewStandardReference : String

open ReasonablenessIndex public

------------------------------------------------------------------------
-- Separate carriers: empirical frequency, institutional convention and legal
-- reasonableness are not one type and cannot be silently substituted.
------------------------------------------------------------------------

data EmpiricalNormality : Set where
  empiricallyCommon : EmpiricalNormality
  empiricallyUncommon : EmpiricalNormality

data InstitutionalNormality : Set where
  institutionallyConventional : InstitutionalNormality
  institutionallyUnconventional : InstitutionalNormality

data LegalReasonableness : Set where
  legallyWithinReasonableRange : LegalReasonableness
  legallyOutsideReasonableRange : LegalReasonableness

------------------------------------------------------------------------
-- Finite observer witness.
--
-- The two worlds collide under a deliberately coarse social-conformity
-- surface but differ on the declared reasonableness answer once a situated
-- coordinate is retained.  The worlds are intentionally not named after any
-- diagnosis, disability, trauma state, culture or historical group.
------------------------------------------------------------------------

data ReasonWorld : Set where
  firstSituatedWorld : ReasonWorld
  secondSituatedWorld : ReasonWorld

data SocialConformitySurface : Set where
  sameObservedConformity : SocialConformitySurface

data SituatedCoordinate : Set where
  firstSituatedCoordinate : SituatedCoordinate
  secondSituatedCoordinate : SituatedCoordinate

data ReasonQuery : Set where
  reasonablenessQuery : ReasonQuery

data ReasonAnswer : Set where
  withinDeclaredReasonableRange : ReasonAnswer
  outsideDeclaredReasonableRange : ReasonAnswer

socialConformitySurface : ReasonWorld → SocialConformitySurface
socialConformitySurface world = sameObservedConformity

situatedCoordinate : ReasonWorld → SituatedCoordinate
situatedCoordinate firstSituatedWorld = firstSituatedCoordinate
situatedCoordinate secondSituatedWorld = secondSituatedCoordinate

reasonAnswer : ReasonQuery → ReasonWorld → ReasonAnswer
reasonAnswer reasonablenessQuery firstSituatedWorld = withinDeclaredReasonableRange
reasonAnswer reasonablenessQuery secondSituatedWorld = outsideDeclaredReasonableRange

reasonSemantics : Query.QuerySemantics ReasonWorld ReasonQuery ReasonAnswer
reasonSemantics = Query.querySemantics reasonAnswer

ReasonablenessQueryAdequacyDefect : Set₁
ReasonablenessQueryAdequacyDefect =
  Query.QueryAdequacyDefect
    socialConformitySurface
    reasonSemantics
    reasonablenessQuery

reasonablenessQueryAdequacyDefect : ReasonablenessQueryAdequacyDefect
reasonablenessQueryAdequacyDefect =
  Query.queryAdequacyDefect
    firstSituatedWorld
    secondSituatedWorld
    refl
    (λ ())

ReasonablenessQueryAdequate : Set₁
ReasonablenessQueryAdequate =
  Query.AdequateFor
    socialConformitySurface
    reasonSemantics
    reasonablenessQuery

reasonablenessNotAdequate : ReasonablenessQueryAdequate → ⊥
reasonablenessNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation reasonablenessQueryAdequacyDefect

situatedReasonablenessObserver :
  ReasonWorld → (SocialConformitySurface × SituatedCoordinate)
situatedReasonablenessObserver =
  Observer.pairObserver socialConformitySurface situatedCoordinate

SituatedReasonablenessStrictRefinement : Set
SituatedReasonablenessStrictRefinement =
  Observer.StrictRefinement socialConformitySurface situatedReasonablenessObserver

situatedReasonablenessStrictlyRefinesSocialConformity :
  SituatedReasonablenessStrictRefinement
situatedReasonablenessStrictlyRefinesSocialConformity =
  Observer.strictPairRefinement
    socialConformitySurface
    situatedCoordinate
    firstSituatedWorld
    secondSituatedWorld
    refl
    (λ ())

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record SituatedReasonablenessBoundary : Set where
  constructor situatedReasonablenessBoundary
  field
    observedFrequencyAutomaticallyReasonable : Bool
    institutionalConventionAutomaticallyReasonable : Bool
    socialNormConformityAutomaticallyCredible : Bool
    atypicalAffectAutomaticallyDishonest : Bool
    literalResponseAutomaticallyNonCooperative : Bool
    dysregulationAutomaticallyDangerous : Bool
    narrativeFragmentationAutomaticallyFalse : Bool
    observerDependenceAutomaticallyContentless : Bool
    reasonablenessRequiresDeclaredIndex : Bool
    joinedObserverCanRetainSituatedCoordinate : Bool

open SituatedReasonablenessBoundary public

canonicalSituatedReasonablenessBoundary : SituatedReasonablenessBoundary
canonicalSituatedReasonablenessBoundary =
  situatedReasonablenessBoundary
    false
    false
    false
    false
    false
    false
    false
    false
    true
    true
