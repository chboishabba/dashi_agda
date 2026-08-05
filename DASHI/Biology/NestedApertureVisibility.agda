module DASHI.Biology.NestedApertureVisibility where

open import DASHI.Core.Prelude

import DASHI.Biology.DynamicEffectiveTopology as DynamicTopology

------------------------------------------------------------------------
-- Viewpoint-indexed visibility over one fixed aperture carrier.
--
-- Structural containment is fixed.  Effective line-of-sight changes with eye
-- position, providing a geometric consumer of the existing state-dependent
-- effective-topology theorem family.

data Aperture : Set where
  macroAperture : Aperture
  leftNestedAperture : Aperture
  rightNestedAperture : Aperture
  deepAperture : Aperture

data StructuralContainment : Aperture → Aperture → Set where
  macroContainsLeft :
    StructuralContainment macroAperture leftNestedAperture
  macroContainsRight :
    StructuralContainment macroAperture rightNestedAperture
  leftContainsDeep :
    StructuralContainment leftNestedAperture deepAperture
  rightContainsDeep :
    StructuralContainment rightNestedAperture deepAperture

data Viewpoint : Set where
  axialView : Viewpoint
  shiftedView : Viewpoint

data VisibleThrough : Viewpoint → Aperture → Aperture → Set where
  axialMacroLeft :
    VisibleThrough axialView macroAperture leftNestedAperture
  axialLeftDeep :
    VisibleThrough axialView leftNestedAperture deepAperture
  shiftedMacroRight :
    VisibleThrough shiftedView macroAperture rightNestedAperture
  shiftedRightDeep :
    VisibleThrough shiftedView rightNestedAperture deepAperture

data VisibleReach (e : Viewpoint) : Aperture → Aperture → Set where
  directVisible :
    ∀ {a b : Aperture} →
    VisibleThrough e a b →
    VisibleReach e a b

  composeVisible :
    ∀ {a b c : Aperture} →
    VisibleReach e a b →
    VisibleReach e b c →
    VisibleReach e a c

axialDeepReach :
  VisibleReach axialView macroAperture deepAperture
axialDeepReach =
  composeVisible
    (directVisible axialMacroLeft)
    (directVisible axialLeftDeep)

shiftedDeepReach :
  VisibleReach shiftedView macroAperture deepAperture
shiftedDeepReach =
  composeVisible
    (directVisible shiftedMacroRight)
    (directVisible shiftedRightDeep)

leftNestedNotVisibleFromShifted :
  VisibleThrough shiftedView macroAperture leftNestedAperture → ⊥
leftNestedNotVisibleFromShifted ()

rightNestedNotVisibleFromAxial :
  VisibleThrough axialView macroAperture rightNestedAperture → ⊥
rightNestedNotVisibleFromAxial ()

------------------------------------------------------------------------
-- Finite projective alignment and parallax.

alignmentScore : Viewpoint → Nat
alignmentScore axialView = 3
alignmentScore shiftedView = 1

axialAlignmentIsThree : alignmentScore axialView ≡ 3
axialAlignmentIsThree = refl

shiftedAlignmentIsOne : alignmentScore shiftedView ≡ 1
shiftedAlignmentIsOne = refl

data DepthLayer : Set where
  nearLayer : DepthLayer
  farLayer : DepthLayer

projectedShift : Viewpoint → DepthLayer → Nat
projectedShift axialView nearLayer = 0
projectedShift axialView farLayer = 0
projectedShift shiftedView nearLayer = 2
projectedShift shiftedView farLayer = 1

shiftedViewProducesDepthParallax :
  projectedShift shiftedView farLayer
  ≤
  projectedShift shiftedView nearLayer
shiftedViewProducesDepthParallax =
  s≤s z≤n

record ApertureVisibilityContrast : Set₁ where
  constructor apertureVisibilityContrast
  field
    fixedStructuralLeft :
      StructuralContainment macroAperture leftNestedAperture

    fixedStructuralRight :
      StructuralContainment macroAperture rightNestedAperture

    axialSelectsLeft :
      VisibleThrough axialView macroAperture leftNestedAperture

    shiftedSelectsRight :
      VisibleThrough shiftedView macroAperture rightNestedAperture

    axialRejectsRight :
      VisibleThrough axialView macroAperture rightNestedAperture → ⊥

    shiftedRejectsLeft :
      VisibleThrough shiftedView macroAperture leftNestedAperture → ⊥

    priorDynamicTopology :
      DynamicTopology.EffectiveTopologyContrast

open ApertureVisibilityContrast public

canonicalApertureVisibilityContrast : ApertureVisibilityContrast
canonicalApertureVisibilityContrast =
  apertureVisibilityContrast
    macroContainsLeft
    macroContainsRight
    axialMacroLeft
    shiftedMacroRight
    rightNestedNotVisibleFromAxial
    leftNestedNotVisibleFromShifted
    DynamicTopology.canonicalEffectiveTopologyContrast

record ApertureVisibilityBoundary : Set where
  constructor apertureVisibilityBoundary
  field
    visibilityGraphEqualsStructuralContainment : Bool
    visibilityGraphEqualsStructuralContainmentIsFalse :
      visibilityGraphEqualsStructuralContainment ≡ false

    projectiveAlignmentIsClassicalMoiréOnly : Bool
    projectiveAlignmentIsClassicalMoiréOnlyIsFalse :
      projectiveAlignmentIsClassicalMoiréOnly ≡ false

open ApertureVisibilityBoundary public

canonicalApertureVisibilityBoundary : ApertureVisibilityBoundary
canonicalApertureVisibilityBoundary =
  apertureVisibilityBoundary false refl false refl
