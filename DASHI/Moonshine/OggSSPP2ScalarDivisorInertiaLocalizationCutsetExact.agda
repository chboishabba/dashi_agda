module DASHI.Moonshine.OggSSPP2ScalarDivisorInertiaLocalizationCutsetExact where

------------------------------------------------------------------------
-- p=2 SCALAR DIVISOR vs FULL-INERTIA LOCALIZATION CUTSET
--
-- SOURCE FACT
--
-- Kobin--Zureick-Brown note that X(1) -> X(1)^rig is etale and induces an
-- isomorphism on (log) canonical rings, with a grading change.
--
-- CONSEQUENCE FOR THE 5-SECTOR CANDIDATE
--
-- The full-stack binary-tetrahedral inertia has five unoriented sectors, but
-- rigidification collapses them to three sectors.  A scalar modular form /
-- ordinary divisor living only on X(1)^rig is therefore not, by itself, a
-- five-sector localized object.
--
-- To sum one valuation copy over all five full-stack sectors, an admissible
-- theorem must introduce additional inertia/representation/gerbe-character
-- localization data (or an equivalent refinement) beyond the ordinary scalar
-- canonical ring.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Full
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralRigidificationQuotientExact as Rigidify
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulDivisorCutsetExact as Divisor
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Analytic object kinds.
------------------------------------------------------------------------

data LocalAnalyticObjectKind : Set where
  scalarRigidifiedDivisor :
    LocalAnalyticObjectKind
  inertiaLocalizedTerm :
    LocalAnalyticObjectKind
  representationValuedTerm :
    LocalAnalyticObjectKind
  gerbeCharacterRefinedTerm :
    LocalAnalyticObjectKind

------------------------------------------------------------------------
-- 2. Fine-sector classifier does not descend through rigidification.
------------------------------------------------------------------------

fullSectorIdentity :
  Full.BinaryTetrahedralInversionOrbit ->
  Full.BinaryTetrahedralInversionOrbit
fullSectorIdentity sector = sector

data FullSectorClassifierFactorsThroughRigidification : Set where

fullSectorClassifierDoesNotFactorThroughRigidification :
  FullSectorClassifierFactorsThroughRigidification -> ⊥
fullSectorClassifierDoesNotFactorThroughRigidification ()

------------------------------------------------------------------------
-- 3. Required localization authority.
------------------------------------------------------------------------

record P2FiveSectorAnalyticLocalizationAuthority : Set₁ where
  field
    LocalTerm : Set

    term :
      Full.BinaryTetrahedralInversionOrbit ->
      LocalTerm

    objectKind :
      LocalAnalyticObjectKind

    objectIsNotBareScalarRigidifiedDivisor :
      objectKind ≡ scalarRigidifiedDivisor -> ⊥

    identityCentralPairDistinguishedAnalytically :
      Bool
    identityCentralPairDistinguishedAnalyticallyIsTrue :
      identityCentralPairDistinguishedAnalytically ≡ true

    orderThreeSixPairDistinguishedAnalytically :
      Bool
    orderThreeSixPairDistinguishedAnalyticallyIsTrue :
      orderThreeSixPairDistinguishedAnalytically ≡ true

    localizationDerivedFromInertiaRepresentationOrGerbeData :
      Bool
    localizationDerivedFromInertiaRepresentationOrGerbeDataIsTrue :
      localizationDerivedFromInertiaRepresentationOrGerbeData ≡ true

open P2FiveSectorAnalyticLocalizationAuthority public

------------------------------------------------------------------------
-- 4. No scalar-divisor shortcut.
------------------------------------------------------------------------

data CanonicalRingIsomorphismCreatesFiveSectorLocalization : Set where
data ScalarLocalOrderAtJ0CountsFiveInertiaSectors : Set where
data OrdinaryHauptmodulDivisorAutomaticallyLivesOnInertiaStack : Set where

canonicalRingIsomorphismDoesNotCreateFiveSectorLocalization :
  CanonicalRingIsomorphismCreatesFiveSectorLocalization -> ⊥
canonicalRingIsomorphismDoesNotCreateFiveSectorLocalization ()

scalarOrderAtJ0DoesNotAutomaticallyCountFiveSectors :
  ScalarLocalOrderAtJ0CountsFiveInertiaSectors -> ⊥
scalarOrderAtJ0DoesNotAutomaticallyCountFiveSectors ()

ordinaryDivisorDoesNotAutomaticallyBecomeInertiaDivisor :
  OrdinaryHauptmodulDivisorAutomaticallyLivesOnInertiaStack -> ⊥
ordinaryDivisorDoesNotAutomaticallyBecomeInertiaDivisor ()

------------------------------------------------------------------------
-- 5. Existing divisor cutset needs this refinement on the p=2 route.
------------------------------------------------------------------------

divisorCutsetBoundary :
  Divisor.HauptmodulDivisorCutsetBoundary
divisorCutsetBoundary =
  Divisor.canonicalHauptmodulDivisorCutsetBoundary

data P2FiveSectorAnalyticLocalizationAuthorityInhabited : Set where

p2FiveSectorLocalizationStillOpen :
  P2FiveSectorAnalyticLocalizationAuthorityInhabited -> ⊥
p2FiveSectorLocalizationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record P2ScalarDivisorInertiaLocalizationBoundary : Set where
  constructor p2-scalar-divisor-inertia-localization-boundary
  field
    fullToRigidifiedFiveToThreeCollapseKnown : Bool
    logCanonicalRingRigidificationCompatibilitySourced : Bool
    scalarRigidifiedDivisorSufficientForFiveSectorLocalization : Bool
    inertiaOrRepresentationRefinementRequired : Bool
    fiveSectorLocalizationAuthoritySpecified : Bool
    fiveSectorLocalizationAuthorityInhabited : Bool

canonicalP2ScalarDivisorInertiaLocalizationBoundary :
  P2ScalarDivisorInertiaLocalizationBoundary
canonicalP2ScalarDivisorInertiaLocalizationBoundary =
  p2-scalar-divisor-inertia-localization-boundary
    true true false true true false
