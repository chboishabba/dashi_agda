module DASHI.Moonshine.P11JacquetLanglandsFixedSpaceResolutionExact where

------------------------------------------------------------------------
-- RESOLUTION OF THE FORMER p11 LOCAL SAME-OBJECT SEAM
--
-- The earlier frontier asked for a canonical three-dimensional map between
-- the principal full-level-2 marked fixed space and the classical K_0(4)
-- oldvector fixed space.  That target was too strong.
--
-- Standard Jacquet--Langlands supplies sameness of the AUTOMORPHIC
-- REPRESENTATION (and therefore of the local component at 2), while Martin's
-- basis-problem formulation explicitly warns that the modular-form-level JL
-- map is non-canonical.
--
-- Independently, repository finite algebra now proves that the two compact-open
-- fixed spaces are distinct 3-dimensional subspaces of one compact induced
-- model and meet in exactly a 2-coordinate plane.  Two distinct full
-- alignments already fix that common plane pointwise.
--
-- Therefore the correct theorem is:
--
--   same local representation
--   + different compact-open fixed subspaces
--   + noncanonical comparison discipline.
--
-- No distinguished K(2)-fixed <-> K_0(4)-fixed matrix remains a mathematical
-- obligation of Jacquet--Langlands.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11JacquetLanglandsRepresentationStandardAuthorityExact as JL
import DASHI.Moonshine.P11Level44CommonLocalRepresentationTargetExact as Common
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as Averaging

------------------------------------------------------------------------
-- Load-bearing representation theorem.
------------------------------------------------------------------------

sameP11LocalRepresentationAtTwo :
  JL.localAtTwo JL.p11QuaternionBrandtRepresentation
  ≡ JL.localAtTwo JL.p11ClassicalNewformRepresentation
sameP11LocalRepresentationAtTwo = JL.p11JacquetLanglandsSameLocalAtTwo

quaternionSideUnramifiedAtTwo :
  JL.UnramifiedAtTwo (JL.localAtTwo JL.p11QuaternionBrandtRepresentation)
quaternionSideUnramifiedAtTwo = JL.p11QuaternionLocalAtTwoUnramified

------------------------------------------------------------------------
-- Exact finite geometry of its two relevant compact-open fixed spaces.
------------------------------------------------------------------------

fixedSpacesHaveCommonAmbient :
  Common.commonCompactAmbientConstructed
    Common.canonicalP11Level44CommonLocalRepresentationBoundary ≡ true
fixedSpacesHaveCommonAmbient = refl

fixedSpacesAreDistinct :
  Common.principalImageEqualsK0Image
    Common.canonicalP11Level44CommonLocalRepresentationBoundary ≡ false
fixedSpacesAreDistinct = refl

fixedSpaceIntersectionHasTwoCoordinates :
  Intersection.commonIntersectionCoordinates
    Intersection.canonicalP11Level44TwoAdicFixedSpaceIntersectionBoundary ≡ 2
fixedSpaceIntersectionHasTwoCoordinates = refl

remainingTransverseCoordinates :
  Transverse.transverseCoordinates
    Transverse.canonicalP11Level44TwoAdicTransverseAlignmentBoundary ≡ 1
remainingTransverseCoordinates = refl

twoAlignmentsAlreadyFixCommonPlane :
  Transverse.alignmentsAgreeOnCommonPlane
    Transverse.canonicalP11Level44TwoAdicTransverseAlignmentBoundary ≡ true
twoAlignmentsAlreadyFixCommonPlane = refl

commonPlaneDoesNotSelectFullAlignment :
  Transverse.commonPlaneDeterminesFullAlignment
    Transverse.canonicalP11Level44TwoAdicTransverseAlignmentBoundary ≡ false
commonPlaneDoesNotSelectFullAlignment = refl

compactAveragingStillNotAnIsomorphism :
  Averaging.compactAveragingCanBeLocalIsomorphism
    Averaging.canonicalP11Level44TwoAdicAveragingNoGoBoundary ≡ false
compactAveragingStillNotAnIsomorphism = refl

------------------------------------------------------------------------
-- Corrected frontier status.
------------------------------------------------------------------------

record P11JacquetLanglandsFixedSpaceResolutionBoundary : Set where
  field
    representationLevelJLSupplied : Bool
    sameLocalRepresentationAtTwoDerived : Bool
    twoFixedSpacesPlacedInCommonAmbient : Bool
    twoFixedSpacesProvedDistinct : Bool
    exactIntersectionDimensionDerived : Bool
    canonicalFixedSpaceMapRequiredForJL : Bool
    previousThreeByThreeAlignmentTargetRetracted : Bool
    localSameObjectSeamResolvedAtCorrectLevel : Bool
    optionalExtraTestVectorNormalizationCouldStillBeStudied : Bool

canonicalP11JacquetLanglandsFixedSpaceResolutionBoundary :
  P11JacquetLanglandsFixedSpaceResolutionBoundary
canonicalP11JacquetLanglandsFixedSpaceResolutionBoundary = record
  { representationLevelJLSupplied = true
  ; sameLocalRepresentationAtTwoDerived = true
  ; twoFixedSpacesPlacedInCommonAmbient = true
  ; twoFixedSpacesProvedDistinct = true
  ; exactIntersectionDimensionDerived = true
  ; canonicalFixedSpaceMapRequiredForJL = false
  ; previousThreeByThreeAlignmentTargetRetracted = true
  ; localSameObjectSeamResolvedAtCorrectLevel = true
  ; optionalExtraTestVectorNormalizationCouldStillBeStudied = true
  }
