module DASHI.Moonshine.P11JacquetLanglandsCoordinateNonCanonicityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hervé Jacquet and Robert P. Langlands,
-- "Automorphic Forms on GL(2), Part 1", LNM 114, Springer, 1970.
-- DOI: 10.1007/BFb0058988.
--
-- Kimball Martin,
-- "The basis problem revisited", Trans. Amer. Math. Soc. 373 (2020),
-- 4523--4559. DOI: 10.1090/tran/8077.
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- J. Ramanujan Math. Soc. 17 (2002), 115--147.
--
-- DASHI CONTRIBUTION
--
-- The representation-level Jacquet--Langlands seam is already correctly
-- closed: quaternionic/Brandt and classical level-11 objects have the SAME
-- unramified local representation pi_2, while K(2)- and K_0(4)-fixed vectors
-- are distinct compact-open invariant subspaces.
--
-- This module proves a stronger coordinate-level non-canonicity theorem.
-- Even after retaining ALL of the currently source-native local information
--
--   * the same local representation pi_2;
--   * the exact common two-coordinate compact intersection;
--   * the p=11 value a_2=-2;
--   * the Satake polynomial X^2+2X+2;
--   * the cubic oldspace operator identity;
--   * the complete Satake residual map;
--   * the resulting kernel line;
--
-- there remain TWO distinct integral transverse alignments.  Their transported
-- bad-prime operators P+ and P- differ, but their Satake residual maps agree
-- pointwise and their kernel generator is the same.
--
-- Thus a Whittaker/test-vector normalization is genuinely OPTIONAL additional
-- coordinate structure.  It can choose a preferred chart if a consumer needs
-- one, but its absence does not reopen the representation-level JL theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11JacquetLanglandsRepresentationStandardAuthorityExact as JL
import DASHI.Moonshine.P11JacquetLanglandsFixedSpaceResolutionExact as Resolution
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse
import DASHI.Moonshine.P11Level44TransverseSatakeNonUniquenessExact as Satake
import DASHI.Moonshine.P11Level44BadPrimeConjugacyNoGoExact as R2NoGo
import DASHI.Moonshine.P11Level44BadPrimeOperatorSeparationExact as Bad
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal

------------------------------------------------------------------------
-- A proof-relevant collision: two distinct coordinate alignments satisfy the
-- same currently-declared local observer.
------------------------------------------------------------------------

record LocalCoordinateAlignment : Set where
  constructor local-coordinate-alignment
  field
    principalToK0 : Principal.Old3 → DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact.Bruhat3
    k0ToPrincipal : DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact.Bruhat3 → Principal.Old3
    transportedU2 : Principal.Old3 → Principal.Old3

open LocalCoordinateAlignment public

plusAlignment : LocalCoordinateAlignment
plusAlignment = local-coordinate-alignment
  Transverse.plusPrincipalToK0
  Transverse.plusK0ToPrincipal
  Satake.plusPrincipalU2

minusAlignment : LocalCoordinateAlignment
minusAlignment = local-coordinate-alignment
  Transverse.minusPrincipalToK0
  Transverse.minusK0ToPrincipal
  Satake.minusPrincipalU2

------------------------------------------------------------------------
-- The observer deliberately contains every invariant that has actually been
-- shown source-native so far.  It does NOT contain an arbitrary chart label.
------------------------------------------------------------------------

record SameDeclaredLocalData
    (A B : LocalCoordinateAlignment) : Set where
  field
    sameRepresentation :
      JL.localAtTwo JL.p11QuaternionBrandtRepresentation
      ≡ JL.localAtTwo JL.p11ClassicalNewformRepresentation

    sameCommonPlane :
      (c : Intersection.Common2) →
      principalToK0 A (Intersection.principalCommon c)
      ≡ principalToK0 B (Intersection.principalCommon c)

    sameSatakeResidual :
      (v : Principal.Old3) →
      Satake.plusSatakeQuadratic v ≡ Satake.minusSatakeQuadratic v

    sameKernelGenerator :
      transportedU2 A Satake.principalKernelGenerator
      ≡ Principal.old3 0 0 0
      × transportedU2 B Satake.principalKernelGenerator
        ≡ Principal.old3 0 0 0

open SameDeclaredLocalData public

plusMinusSameDeclaredLocalData :
  SameDeclaredLocalData plusAlignment minusAlignment
plusMinusSameDeclaredLocalData = record
  { sameRepresentation = Resolution.sameP11LocalRepresentationAtTwo
  ; sameCommonPlane = λ c →
      trans (Transverse.plusOnCommon c) (sym (Transverse.minusOnCommon c))
  ; sameSatakeResidual = Satake.satakeResidualsIdentical
  ; sameKernelGenerator =
      Satake.plusKernelGeneratorKilled , Satake.minusKernelGeneratorKilled
  }

------------------------------------------------------------------------
-- Yet the alignments are genuinely distinct on the one transverse coordinate.
------------------------------------------------------------------------

alignmentsDistinct :
  ((v : Principal.Old3) →
    principalToK0 plusAlignment v ≡ principalToK0 minusAlignment v) → ⊥
alignmentsDistinct allEqual =
  Transverse.plusAndMinusDiffer (allEqual Principal.oldBasis2)

transportedOperatorsDistinct :
  ((v : Principal.Old3) →
    transportedU2 plusAlignment v ≡ transportedU2 minusAlignment v) → ⊥
transportedOperatorsDistinct = Satake.plusMinusOperatorsDistinct

------------------------------------------------------------------------
-- A generic selector using only SameDeclaredLocalData cannot distinguish the
-- two alignments: the witness is literally inhabited for a distinct pair.
------------------------------------------------------------------------

record LocalCoordinateNonCanonicityWitness : Set where
  field
    first second : LocalCoordinateAlignment
    observationallySame : SameDeclaredLocalData first second
    coordinateDistinct :
      ((v : Principal.Old3) →
        principalToK0 first v ≡ principalToK0 second v) → ⊥
    badPrimeOperatorDistinct :
      ((v : Principal.Old3) →
        transportedU2 first v ≡ transportedU2 second v) → ⊥

canonicalLocalCoordinateNonCanonicity : LocalCoordinateNonCanonicityWitness
canonicalLocalCoordinateNonCanonicity = record
  { first = plusAlignment
  ; second = minusAlignment
  ; observationallySame = plusMinusSameDeclaredLocalData
  ; coordinateDistinct = alignmentsDistinct
  ; badPrimeOperatorDistinct = transportedOperatorsDistinct
  }

------------------------------------------------------------------------
-- The internal positive marked R2 is not one of the missing coordinate choices
-- either: the arbitrary conjugacy no-go is imported as a separate obstruction.
------------------------------------------------------------------------

internalMarkedR2CannotBeRecoveredByCoordinateChoice :
  R2NoGo.U2R2LinearConjugacy → Bad.Impossible
internalMarkedR2CannotBeRecoveredByCoordinateChoice =
  R2NoGo.u2R2LinearConjugacyImpossible

record P11JacquetLanglandsCoordinateNonCanonicityBoundary : Set where
  field
    representationLevelSameObjectRemainsClosed : Bool
    twoDistinctCoordinateAlignmentsConstructed : Bool
    bothPreserveCommonPlane : Bool
    bothHaveSameSatakeResidual : Bool
    bothHaveSameKernelGenerator : Bool
    coordinateAlignmentDeterminedByDeclaredData : Bool
    internalPositiveR2CanBeRecoveredByBasisChange : Bool
    whittakerNormalizationRequiredForJLTheorem : Bool
    whittakerNormalizationOptionalForPreferredCoordinates : Bool

canonicalP11JacquetLanglandsCoordinateNonCanonicityBoundary :
  P11JacquetLanglandsCoordinateNonCanonicityBoundary
canonicalP11JacquetLanglandsCoordinateNonCanonicityBoundary = record
  { representationLevelSameObjectRemainsClosed = true
  ; twoDistinctCoordinateAlignmentsConstructed = true
  ; bothPreserveCommonPlane = true
  ; bothHaveSameSatakeResidual = true
  ; bothHaveSameKernelGenerator = true
  ; coordinateAlignmentDeterminedByDeclaredData = false
  ; internalPositiveR2CanBeRecoveredByBasisChange = false
  ; whittakerNormalizationRequiredForJLTheorem = false
  ; whittakerNormalizationOptionalForPreferredCoordinates = true
  }
