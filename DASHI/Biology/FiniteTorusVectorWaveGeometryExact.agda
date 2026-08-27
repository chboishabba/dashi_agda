module DASHI.Biology.FiniteTorusVectorWaveGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Anup Das, Erfan Zabeh, Bard Ermentrout, Joshua Jacobs,
-- "Planar, spiral, and concentric traveling waves distinguish behavioral
-- states in human memory", Nature Communications 17 (2026), 5143.
-- DOI: 10.1038/s41467-026-71386-z.
--
-- Lyle Muller, Alexandra N. Busch, Zachary W. Davis, John H. Reynolds,
-- "Neural traveling waves in cortex: Network mechanisms and potential roles
-- in neural computation", Neuron (2026).
-- DOI: 10.1016/j.neuron.2026.06.019.
--
-- DASHI CONTRIBUTION
--
-- Put actual finite vector-wave geometry on the existing 3 x 3 torus.  A
-- centered difference operator separates a uniform planar witness, a radial
-- source witness, a rotational/transverse witness and a mixed spiral witness
-- by exact divergence/curl signatures at the central chart point.
--
-- These finite identities model the algebra behind div/curl classification.
-- They do not claim that a 3 x 3 periodic lattice is a cortical surface, nor
-- that the named empirical classes are exhausted by these four witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; -_)
  renaming (_+_ to _+ℤ_)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

record Vec2 : Set where
  constructor vec2
  field
    xComponent : ℤ
    yComponent : ℤ

open Vec2 public

zeroℤ : ℤ
zeroℤ = + 0

oneℤ : ℤ
oneℤ = + 1

minusOneℤ : ℤ
minusOneℤ = -[1+ 0 ]

_−ℤ_ : ℤ → ℤ → ℤ
left −ℤ right = left +ℤ (- right)

addVec : Vec2 → Vec2 → Vec2
addVec (vec2 ax ay) (vec2 bx by) =
  vec2 (ax +ℤ bx) (ay +ℤ by)

residueCoordinate : Torus.Residue3 → ℤ
residueCoordinate Torus.residueMinus = minusOneℤ
residueCoordinate Torus.residueZero = zeroℤ
residueCoordinate Torus.residuePlus = oneℤ

previous3 : Torus.Residue3 → Torus.Residue3
previous3 Torus.residueMinus = Torus.residuePlus
previous3 Torus.residueZero = Torus.residueMinus
previous3 Torus.residuePlus = Torus.residueZero

previousThenNext : ∀ residue → Torus.next3 (previous3 residue) ≡ residue
previousThenNext Torus.residueMinus = refl
previousThenNext Torus.residueZero = refl
previousThenNext Torus.residuePlus = refl

nextThenPrevious : ∀ residue → previous3 (Torus.next3 residue) ≡ residue
nextThenPrevious Torus.residueMinus = refl
nextThenPrevious Torus.residueZero = refl
nextThenPrevious Torus.residuePlus = refl

translateFirstPrevious : Torus.Torus3x3 → Torus.Torus3x3
translateFirstPrevious (Torus.torusPoint first second) =
  Torus.torusPoint (previous3 first) second

translateSecondPrevious : Torus.Torus3x3 → Torus.Torus3x3
translateSecondPrevious (Torus.torusPoint first second) =
  Torus.torusPoint first (previous3 second)

VectorField : Set
VectorField = Torus.Torus3x3 → Vec2

uniformPlanarField : VectorField
uniformPlanarField point = vec2 oneℤ zeroℤ

radialSourceField : VectorField
radialSourceField point =
  vec2
    (residueCoordinate (Torus.firstCoordinate point))
    (residueCoordinate (Torus.secondCoordinate point))

rotationalField : VectorField
rotationalField point =
  vec2
    (- residueCoordinate (Torus.secondCoordinate point))
    (residueCoordinate (Torus.firstCoordinate point))

spiralField : VectorField
spiralField point = addVec (radialSourceField point) (rotationalField point)

center : Torus.Torus3x3
center = Torus.torusPoint Torus.residueZero Torus.residueZero

dxX : VectorField → Torus.Torus3x3 → ℤ
dxX field point =
  xComponent (field (Torus.translateFirst point))
  −ℤ
  xComponent (field (translateFirstPrevious point))

dyY : VectorField → Torus.Torus3x3 → ℤ
dyY field point =
  yComponent (field (Torus.translateSecond point))
  −ℤ
  yComponent (field (translateSecondPrevious point))

dxY : VectorField → Torus.Torus3x3 → ℤ
dxY field point =
  yComponent (field (Torus.translateFirst point))
  −ℤ
  yComponent (field (translateFirstPrevious point))

dyX : VectorField → Torus.Torus3x3 → ℤ
dyX field point =
  xComponent (field (Torus.translateSecond point))
  −ℤ
  xComponent (field (translateSecondPrevious point))

divergence : VectorField → Torus.Torus3x3 → ℤ
divergence field point = dxX field point +ℤ dyY field point

curl : VectorField → Torus.Torus3x3 → ℤ
curl field point = dxY field point −ℤ dyX field point

uniformPlanarCenterDivergenceZero :
  divergence uniformPlanarField center ≡ + 0
uniformPlanarCenterDivergenceZero = refl

uniformPlanarCenterCurlZero :
  curl uniformPlanarField center ≡ + 0
uniformPlanarCenterCurlZero = refl

radialSourceCenterDivergenceFour :
  divergence radialSourceField center ≡ + 4
radialSourceCenterDivergenceFour = refl

radialSourceCenterCurlZero :
  curl radialSourceField center ≡ + 0
radialSourceCenterCurlZero = refl

rotationalCenterDivergenceZero :
  divergence rotationalField center ≡ + 0
rotationalCenterDivergenceZero = refl

rotationalCenterCurlFour :
  curl rotationalField center ≡ + 4
rotationalCenterCurlFour = refl

spiralCenterDivergenceFour :
  divergence spiralField center ≡ + 4
spiralCenterDivergenceFour = refl

spiralCenterCurlFour :
  curl spiralField center ≡ + 4
spiralCenterCurlFour = refl

data FiniteGeometryClass : Set where
  planarClass : FiniteGeometryClass
  sourceSinkClass : FiniteGeometryClass
  rotationalTransverseClass : FiniteGeometryClass
  spiralMixedClass : FiniteGeometryClass

record GeometrySignature : Set where
  constructor geometrySignature
  field
    geometryClass : FiniteGeometryClass
    divergenceAtCenter : ℤ
    curlAtCenter : ℤ

open GeometrySignature public

planarSignature : GeometrySignature
planarSignature = geometrySignature planarClass (+ 0) (+ 0)

sourceSignature : GeometrySignature
sourceSignature = geometrySignature sourceSinkClass (+ 4) (+ 0)

rotationalSignature : GeometrySignature
rotationalSignature = geometrySignature rotationalTransverseClass (+ 0) (+ 4)

spiralSignature : GeometrySignature
spiralSignature = geometrySignature spiralMixedClass (+ 4) (+ 4)

record FiniteGeometryBoundary : Set where
  constructor finiteGeometryBoundary
  field
    centerSignatureIsFullHelmholtzHodgeDecomposition : Set
    centerSignatureIsNotFullHelmholtzHodgeDecomposition :
      centerSignatureIsFullHelmholtzHodgeDecomposition → Set

    finiteRotationalWitnessIsMeasuredCorticalSpiral : Set
    finiteRotationalWitnessIsNotMeasuredCorticalSpiral :
      finiteRotationalWitnessIsMeasuredCorticalSpiral → Set

canonicalFiniteGeometryBoundary : FiniteGeometryBoundary
canonicalFiniteGeometryBoundary =
  finiteGeometryBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
