module DASHI.Physics.Closure.E6HyperformH3H2InvariantPotentialNoGoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2NineSheetChartExact as Nine
import DASHI.Physics.Closure.E6HyperformH3H2OrderParameterGeometryExact as Geometry

------------------------------------------------------------------------
-- NO-GO: A FULLY TRANSLATION-INVARIANT ONSITE POTENTIAL CANNOT SELECT ONE H2
--
-- The nine H2 decorations over a selected H3 are the affine plane F3^2.  Its
-- translation subgroup already acts transitively.  Therefore any single-site
-- potential invariant under all translations is constant.  Full affine-O(2,3)
-- invariance is stronger and inherits the same no-go.
--
-- Consequently a physical selection of one H2 decoration cannot come from a
-- nonconstant fully symmetric onsite V(u) alone.  Selection must use additional
-- structure: interaction/gradient terms across sites, boundary/history data,
-- coupling to another field, or spontaneous symmetry breaking of a larger
-- dynamical model.
------------------------------------------------------------------------

addCoeff : Nine.F3Coeff → Nine.F3Coeff → Nine.F3Coeff
addCoeff Nine.c0 x = x
addCoeff Nine.c1 Nine.c0 = Nine.c1
addCoeff Nine.c1 Nine.c1 = Nine.c2
addCoeff Nine.c1 Nine.c2 = Nine.c0
addCoeff Nine.c2 Nine.c0 = Nine.c2
addCoeff Nine.c2 Nine.c1 = Nine.c0
addCoeff Nine.c2 Nine.c2 = Nine.c1

negCoeff : Nine.F3Coeff → Nine.F3Coeff
negCoeff Nine.c0 = Nine.c0
negCoeff Nine.c1 = Nine.c2
negCoeff Nine.c2 = Nine.c1

subCoeff : Nine.F3Coeff → Nine.F3Coeff → Nine.F3Coeff
subCoeff x y = addCoeff x (negCoeff y)

translate : Nine.PhaseAffineCoordinate → Nine.PhaseAffineCoordinate → Nine.PhaseAffineCoordinate
translate (db , dc) (b , c) = addCoeff db b , addCoeff dc c

addSubHits : (target source : Nine.F3Coeff) →
  addCoeff (subCoeff target source) source ≡ target
addSubHits Nine.c0 Nine.c0 = refl
addSubHits Nine.c0 Nine.c1 = refl
addSubHits Nine.c0 Nine.c2 = refl
addSubHits Nine.c1 Nine.c0 = refl
addSubHits Nine.c1 Nine.c1 = refl
addSubHits Nine.c1 Nine.c2 = refl
addSubHits Nine.c2 Nine.c0 = refl
addSubHits Nine.c2 Nine.c1 = refl
addSubHits Nine.c2 Nine.c2 = refl

translationHits : (target source : Nine.PhaseAffineCoordinate) →
  translate
    (subCoeff (proj₁ target) (proj₁ source) ,
     subCoeff (proj₂ target) (proj₂ source))
    source
  ≡ target
translationHits (tb , tc) (sb , sc)
  rewrite addSubHits tb sb | addSubHits tc sc = refl

TranslationInvariant : {A : Set} → (Nine.PhaseAffineCoordinate → A) → Set
TranslationInvariant V =
  (delta x : Nine.PhaseAffineCoordinate) → V (translate delta x) ≡ V x

translationInvariantPotentialIsConstant :
  {A : Set} →
  (V : Nine.PhaseAffineCoordinate → A) →
  TranslationInvariant V →
  (x y : Nine.PhaseAffineCoordinate) → V x ≡ V y
translationInvariantPotentialIsConstant V invariant x y =
  trans
    (sym (cong V (translationHits x y)))
    (invariant
      (subCoeff (proj₁ x) (proj₁ y) , subCoeff (proj₂ x) (proj₂ y))
      y)

record H3H2InvariantPotentialBoundary : Set where
  constructor h3-h2-invariant-potential-boundary
  field
    sameAffineNineStateFibreUsed : Bool
    translationSubgroupTransitive : Bool
    translationInvariantSingleSitePotentialConstant : Bool
    fullAffineOrthogonalInvariantPotentialAlsoConstant : Bool
    invariantOnsitePotentialSelectsUniqueH2 : Bool
    interSiteInteractionCouldBreakSymmetry : Bool
    boundaryOrHistoryCouldBreakSymmetry : Bool
    coupledFieldCouldBreakSymmetry : Bool
    physicalSelectionMechanismPaid : Bool
    boundary : String
open H3H2InvariantPotentialBoundary public

canonicalInvariantPotentialBoundary : H3H2InvariantPotentialBoundary
canonicalInvariantPotentialBoundary =
  h3-h2-invariant-potential-boundary
    true true true true false
    true true true false
    "The nine H2 choices are an affine F3^2 torsor and translations act transitively. An exact generic theorem therefore proves every translation-invariant single-site potential is constant; full affine-O(2,3) invariance cannot select one H2 either. A physical section requires interactions, boundary/history data, coupling to another field, or spontaneous symmetry breaking, none of which is manufactured here."

geometryReceipt : Geometry.H3H2OrderParameterGeometryLocalReceipt
geometryReceipt = Geometry.canonicalH3H2OrderParameterGeometryLocalReceipt
