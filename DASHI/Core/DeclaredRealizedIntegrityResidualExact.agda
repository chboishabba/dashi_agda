module DASHI.Core.DeclaredRealizedIntegrityResidualExact where

------------------------------------------------------------------------
-- DECLARED / REALIZED INTEGRITY RESIDUAL
--
-- Generic social-ecological observer owner.  A declared rule or public label
-- and the realised affordance available to a situated person are deliberately
-- separate observations.  Their residual is relational: it is not a property
-- of the person alone and it is not a theorem about institutional intent.
--
-- This module is source-neutral.  Solis/SCN, hostile architecture, public-space
-- governance, accessibility, and similar domains may instantiate it without
-- becoming definitionally identical to one another.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record SituatedIntegrityObserver
    (Person Environment Declared Realized Residual : Set) : Set where
  constructor situatedIntegrityObserver
  field
    declaredObservation : Environment → Declared
    realizedObservation : Person → Environment → Realized
    residual : Declared → Realized → Residual

open SituatedIntegrityObserver public

integrityResidual :
  ∀ {Person Environment Declared Realized Residual : Set} →
  SituatedIntegrityObserver Person Environment Declared Realized Residual →
  Person → Environment → Residual
integrityResidual observer person environment =
  residual observer
    (declaredObservation observer environment)
    (realizedObservation observer person environment)

------------------------------------------------------------------------
-- Exact finite social-ecology specimen.
--
-- Both environments nominally declare public access.  The realised ability to
-- remain differs for the same person.  This witnesses that a policy/access
-- label can be too coarse to determine situated accessibility.
------------------------------------------------------------------------

data SituatedPerson : Set where
  canonicalPerson : SituatedPerson

data PublicEnvironment : Set where
  lowDemandThirdPlace highDemandRestrictedSpace : PublicEnvironment

data DeclaredAccess : Set where
  nominallyPublic : DeclaredAccess

data RealizedAccess : Set where
  remainAvailable remainBlocked : RealizedAccess

data ResidualStatus : Set where
  declaredRealizedAligned declaredRealizedMismatch : ResidualStatus

declaredAccess : PublicEnvironment → DeclaredAccess
declaredAccess lowDemandThirdPlace = nominallyPublic
declaredAccess highDemandRestrictedSpace = nominallyPublic

realizedAccess : SituatedPerson → PublicEnvironment → RealizedAccess
realizedAccess canonicalPerson lowDemandThirdPlace = remainAvailable
realizedAccess canonicalPerson highDemandRestrictedSpace = remainBlocked

accessResidual : DeclaredAccess → RealizedAccess → ResidualStatus
accessResidual nominallyPublic remainAvailable = declaredRealizedAligned
accessResidual nominallyPublic remainBlocked = declaredRealizedMismatch

publicAccessObserver :
  SituatedIntegrityObserver
    SituatedPerson PublicEnvironment DeclaredAccess RealizedAccess ResidualStatus
publicAccessObserver =
  situatedIntegrityObserver declaredAccess realizedAccess accessResidual

sameDeclaredAccess :
  declaredObservation publicAccessObserver lowDemandThirdPlace
  ≡ declaredObservation publicAccessObserver highDemandRestrictedSpace
sameDeclaredAccess = refl

thirdPlaceResidualAligned :
  integrityResidual publicAccessObserver canonicalPerson lowDemandThirdPlace
  ≡ declaredRealizedAligned
thirdPlaceResidualAligned = refl

restrictedSpaceResidualMismatch :
  integrityResidual publicAccessObserver canonicalPerson highDemandRestrictedSpace
  ≡ declaredRealizedMismatch
restrictedSpaceResidualMismatch = refl

alignedIsNotMismatch :
  declaredRealizedAligned ≡ declaredRealizedMismatch → ⊥
alignedIsNotMismatch ()

declaredAccessDoesNotDetermineSituatedResidual :
  integrityResidual publicAccessObserver canonicalPerson lowDemandThirdPlace
  ≡ integrityResidual publicAccessObserver canonicalPerson highDemandRestrictedSpace →
  ⊥
declaredAccessDoesNotDetermineSituatedResidual ()

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record DeclaredRealizedBoundary : Set where
  constructor declared-realized-boundary
  field
    accessibilityIsPersonOnlyProperty : Bool
    accessibilityIsPersonOnlyPropertyIsFalse :
      accessibilityIsPersonOnlyProperty ≡ false
    declaredPermissionDeterminesRealizedAccess : Bool
    declaredPermissionDeterminesRealizedAccessIsFalse :
      declaredPermissionDeterminesRealizedAccess ≡ false
    realizedMismatchProvesHostileIntent : Bool
    realizedMismatchProvesHostileIntentIsFalse :
      realizedMismatchProvesHostileIntent ≡ false
    samePersonCanHaveDifferentResidualAcrossEnvironments : Bool
    samePersonCanHaveDifferentResidualAcrossEnvironmentsIsTrue :
      samePersonCanHaveDifferentResidualAcrossEnvironments ≡ true

canonicalDeclaredRealizedBoundary : DeclaredRealizedBoundary
canonicalDeclaredRealizedBoundary =
  declared-realized-boundary false refl false refl false refl true refl
