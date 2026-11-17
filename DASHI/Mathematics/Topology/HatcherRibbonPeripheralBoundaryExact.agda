module DASHI.Mathematics.Topology.HatcherRibbonPeripheralBoundaryExact where

------------------------------------------------------------------------
-- HATCHER PUNCTURED TORUS VERSUS SAME F₂ PAIR-OF-PANTS ROTATION
--
-- ORIGINAL MATHEMATICS:
-- Hatcher, Algebraic Topology Example 2B.2, pp171–172:
-- local F₂ on α₁,α₂ and incoming annulus α=[α₁,α₂].
-- Classical oriented ribbon-graph / combinatorial-map boundary
-- permutation phi=vertexRotation o edgeFlip.
-- Existing Agda topology PR #1254 already owns the actual finite
-- PL pairs-of-pants / surface mesh source and its genus checks.
-- We do NOT duplicate that owner's concrete triangulations.
--
-- This file proves ONLY the four-dart finite permutation and
-- boundary-successor identities by normalisation. To conclude
-- "punctured torus" or "pair of pants", consume the classical
-- oriented ribbon-thickening theorem and χ=V−E=−1,
-- NOT a fabricated Hatcher wild embedding.
--
-- Infinite wild satellite, actual stage meridian metric,
-- geometric based collar equivalence, source physical SU3
-- and native Agda kernel status remain UNPROVED/UNCHECKED.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

data Dart : Set where
  a A b B : Dart

edgeFlip : Dart → Dart
edgeFlip a = A
edgeFlip A = a
edgeFlip b = B
edgeFlip B = b

edgeFlipInvolutive : (d : Dart) → edgeFlip (edgeFlip d) ≡ d
edgeFlipInvolutive a = refl
edgeFlipInvolutive A = refl
edgeFlipInvolutive b = refl
edgeFlipInvolutive B = refl

-- Alternating cyclic order (a B A b), yielding ONE boundary.
torusVertexRotation : Dart → Dart
torusVertexRotation a = B
torusVertexRotation B = A
torusVertexRotation A = b
torusVertexRotation b = a

torusBoundaryNext : Dart → Dart
torusBoundaryNext d = torusVertexRotation (edgeFlip d)

-- The SINGLE ribbon boundary: a -> b -> A -> B -> a.
-- Its literal source word a b a^-1 b^-1 is a commutator.
torusBoundaryAtoB : torusBoundaryNext a ≡ b
torusBoundaryAtoB = refl

torusBoundaryBtoInverseA : torusBoundaryNext b ≡ A
torusBoundaryBtoInverseA = refl

torusBoundaryInverseAtoInverseB : torusBoundaryNext A ≡ B
torusBoundaryInverseAtoInverseB = refl

torusBoundaryInverseBtoA : torusBoundaryNext B ≡ a
torusBoundaryInverseBtoA = refl

torusBoundaryDarts : List Dart
torusBoundaryDarts = a ∷ b ∷ A ∷ B ∷ []

-- Nonalternating (a A b B), SAME bouquet/group, THREE boundaries.
pantsVertexRotation : Dart → Dart
pantsVertexRotation a = A
pantsVertexRotation A = b
pantsVertexRotation b = B
pantsVertexRotation B = a

pantsBoundaryNext : Dart → Dart
pantsBoundaryNext d = pantsVertexRotation (edgeFlip d)

pantsBoundaryAtoB : pantsBoundaryNext a ≡ b
pantsBoundaryAtoB = refl

pantsBoundaryBtoA : pantsBoundaryNext b ≡ a
pantsBoundaryBtoA = refl

pantsBoundaryInverseAFixed : pantsBoundaryNext A ≡ A
pantsBoundaryInverseAFixed = refl

pantsBoundaryInverseBFixed : pantsBoundaryNext B ≡ B
pantsBoundaryInverseBFixed = refl

pantsFirstBoundaryDarts : List Dart
pantsFirstBoundaryDarts = a ∷ b ∷ []

pantsSecondBoundaryDarts : List Dart
pantsSecondBoundaryDarts = A ∷ []

pantsThirdBoundaryDarts : List Dart
pantsThirdBoundaryDarts = B ∷ []

-- Consumer must still prove actual wild relative peripheral
-- transport: neither set-theoretic F₂ generator labels nor
-- finite ribbon cycles identify Hatcher's geometric incoming
-- annulus in the chosen 3D linked horned complement.
