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
-- Representation-level Jacquet--Langlands is already closed correctly: the
-- quaternionic/Brandt and classical level-11 objects have the SAME unramified
-- local representation pi_2, while K(2)- and K_0(4)-fixed vectors are distinct
-- compact-open invariant subspaces.
--
-- This module proves a stronger coordinate-level non-canonicity theorem.  Even
-- after retaining the same local representation, exact common compact plane,
-- a_2=-2 Satake polynomial, complete Satake residual map and kernel line, there
-- remain two distinct integral transverse alignments.
--
-- Therefore Whittaker/test-vector normalization is OPTIONAL additional
-- coordinate structure: it may choose a preferred chart, but its absence does
-- not reopen the representation-level JL theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (+_)

import DASHI.Moonshine.P11JacquetLanglandsRepresentationStandardAuthorityExact as JL
import DASHI.Moonshine.P11JacquetLanglandsFixedSpaceResolutionExact as Resolution
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as K0
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse
import DASHI.Moonshine.P11Level44TransverseSatakeNonUniquenessExact as Satake
import DASHI.Moonshine.P11Level44BadPrimeConjugacyNoGoExact as R2NoGo
import DASHI.Moonshine.P11Level44BadPrimeOperatorSeparationExact as Bad
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal

record LocalCoordinateAlignment : Set where
  constructor local-coordinate-alignment
  field
    principalToK0 : Principal.Old3 → K0.Bruhat3
    k0ToPrincipal : K0.Bruhat3 → Principal.Old3
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

zeroPrincipal : Principal.Old3
zeroPrincipal = Principal.old3 (+ 0) (+ 0) (+ 0)

alignmentSatakeResidual :
  LocalCoordinateAlignment → Principal.Old3 → Principal.Old3
alignmentSatakeResidual A v =
  Principal.addOld3
    (transportedU2 A (transportedU2 A v))
    (Principal.addOld3
      (Principal.scaleOld3 (+ 2) (transportedU2 A v))
      (Principal.scaleOld3 (+ 2) v))

plusAlignmentResidualIsExisting :
  (v : Principal.Old3) →
  alignmentSatakeResidual plusAlignment v ≡ Satake.plusSatakeQuadratic v
plusAlignmentResidualIsExisting v = refl

minusAlignmentResidualIsExisting :
  (v : Principal.Old3) →
  alignmentSatakeResidual minusAlignment v ≡ Satake.minusSatakeQuadratic v
minusAlignmentResidualIsExisting v = refl

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
      alignmentSatakeResidual A v ≡ alignmentSatakeResidual B v

    sameKernelGenerator :
      transportedU2 A Satake.principalKernelGenerator ≡ zeroPrincipal
      × transportedU2 B Satake.principalKernelGenerator ≡ zeroPrincipal

open SameDeclaredLocalData public

plusMinusSameDeclaredLocalData :
  SameDeclaredLocalData plusAlignment minusAlignment
plusMinusSameDeclaredLocalData = record
  { sameRepresentation = Resolution.sameP11LocalRepresentationAtTwo
  ; sameCommonPlane = λ c →
      trans (Transverse.plusOnCommon c) (sym (Transverse.minusOnCommon c))
  ; sameSatakeResidual = λ v →
      trans
        (plusAlignmentResidualIsExisting v)
        (trans
          (Satake.satakeResidualsIdentical v)
          (sym (minusAlignmentResidualIsExisting v)))
  ; sameKernelGenerator =
      Satake.plusKernelGeneratorKilled , Satake.minusKernelGeneratorKilled
  }

alignmentsDistinct :
  ((v : Principal.Old3) →
    principalToK0 plusAlignment v ≡ principalToK0 minusAlignment v) → ⊥
alignmentsDistinct allEqual =
  Transverse.plusAndMinusDiffer (allEqual Principal.oldBasis2)

transportedOperatorsDistinct :
  ((v : Principal.Old3) →
    transportedU2 plusAlignment v ≡ transportedU2 minusAlignment v) → ⊥
transportedOperatorsDistinct = Satake.plusMinusOperatorsDistinct

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
