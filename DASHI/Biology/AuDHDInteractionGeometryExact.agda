module DASHI.Biology.AuDHDInteractionGeometryExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeurotypeProcessingGeometryExact as Geometry
import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources

------------------------------------------------------------------------
-- AuDHD INTERACTION GEOMETRY
--
-- The existing neurotype owner already keeps autism, ADHD and AuDHD as
-- separate empirical coordinates and blocks definitional collapse of AuDHD to
-- "autism + ADHD".  This module adds the next exact layer: a finite response
-- surface in which the combined coordinate is explicitly non-additive relative
-- to the two single-coordinate responses.
--
-- The Nat codes are synthetic theorem witnesses, not symptom severities,
-- population means, diagnostic scores, or effect-size estimates.
--
-- Cross-PR calibration:
--   PR #620 now owns a generic binary-interaction/nonseparability theorem using
--   rectangle and rank-one obstructions.  #618 does not import that separate
--   draft ancestry.  After convergence this module should become a thin domain
--   adapter to the generic #620 owner rather than retaining duplicate algebra.
------------------------------------------------------------------------

data AutismAxis : Set where
  autismAbsent autismPresent : AutismAxis

data ADHDAxis : Set where
  adhdAbsent adhdPresent : ADHDAxis

responseCode : AutismAxis → ADHDAxis → Nat
responseCode autismAbsent adhdAbsent = 0
responseCode autismPresent adhdAbsent = 1
responseCode autismAbsent adhdPresent = 1
responseCode autismPresent adhdPresent = 3

autismOnlyResponse : Nat
autismOnlyResponse = responseCode autismPresent adhdAbsent

adhdOnlyResponse : Nat
adhdOnlyResponse = responseCode autismAbsent adhdPresent

combinedAuDHDResponse : Nat
combinedAuDHDResponse = responseCode autismPresent adhdPresent

singleAxisSum : Nat
singleAxisSum = autismOnlyResponse + adhdOnlyResponse

autismOnlyIsOne : autismOnlyResponse ≡ 1
autismOnlyIsOne = refl

adhdOnlyIsOne : adhdOnlyResponse ≡ 1
adhdOnlyIsOne = refl

combinedIsThree : combinedAuDHDResponse ≡ 3
combinedIsThree = refl

singleAxisSumIsTwo : singleAxisSum ≡ 2
singleAxisSumIsTwo = refl

canonicalAuDHDResponseIsNonAdditive :
  combinedAuDHDResponse ≡ singleAxisSum → ⊥
canonicalAuDHDResponseIsNonAdditive ()

------------------------------------------------------------------------
-- Keep the finite interaction witness attached to the existing neurotype
-- coordinate rather than introducing a second diagnostic ontology.
------------------------------------------------------------------------

canonicalAuDHDCoordinateRetained : Geometry.NeurotypeCoordinate
canonicalAuDHDCoordinateRetained = Geometry.audhdCoordinate

canonicalAutismCoordinateRetained : Geometry.NeurotypeCoordinate
canonicalAutismCoordinateRetained = Geometry.autisticCoordinate

canonicalADHDCoordinateRetained : Geometry.NeurotypeCoordinate
canonicalADHDCoordinateRetained = Geometry.adhdCoordinate

canonicalAuDHDGeometryStillDistinctFromAutism :
  Geometry.geometry Geometry.canonicalAuDHDBridge
  ≡ Geometry.geometry Geometry.canonicalAutisticBridge → ⊥
canonicalAuDHDGeometryStillDistinctFromAutism =
  Geometry.canonicalAuDHDNotDefinitionallyAutisticGeometry

canonicalAuDHDGeometryStillDistinctFromADHD :
  Geometry.geometry Geometry.canonicalAuDHDBridge
  ≡ Geometry.geometry Geometry.canonicalADHDBridge → ⊥
canonicalAuDHDGeometryStillDistinctFromADHD =
  Geometry.canonicalAuDHDNotDefinitionallyADHDGeometry

------------------------------------------------------------------------
-- Source calibration.
------------------------------------------------------------------------

audhdEmpiricalSource : Sources.SourceReference
audhdEmpiricalSource = Sources.audhd2026

autismADHDReviewSource : Sources.SourceReference
autismADHDReviewSource = Sources.autismADHD2024

record AuDHDInteractionBoundary : Set where
  constructor audhd-interaction-boundary
  field
    audhdDefinitionallyEqualsAutismPlusADHD : Bool
    audhdDefinitionallyEqualsAutismPlusADHDIsFalse :
      audhdDefinitionallyEqualsAutismPlusADHD ≡ false
    combinedResponseMustEqualSingleAxisSum : Bool
    combinedResponseMustEqualSingleAxisSumIsFalse :
      combinedResponseMustEqualSingleAxisSum ≡ false
    finiteResponseCodesAreEmpiricalEffectSizes : Bool
    finiteResponseCodesAreEmpiricalEffectSizesIsFalse :
      finiteResponseCodesAreEmpiricalEffectSizes ≡ false
    nonAdditiveInteractionIsRepresentable : Bool
    nonAdditiveInteractionIsRepresentableIsTrue :
      nonAdditiveInteractionIsRepresentable ≡ true
    coOccurrenceRequiresItsOwnEmpiricalStudy : Bool
    coOccurrenceRequiresItsOwnEmpiricalStudyIsTrue :
      coOccurrenceRequiresItsOwnEmpiricalStudy ≡ true

canonicalAuDHDInteractionBoundary : AuDHDInteractionBoundary
canonicalAuDHDInteractionBoundary =
  audhd-interaction-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
