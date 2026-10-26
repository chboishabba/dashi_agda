module DASHI.Biology.IITPointedTernary27TriadicNonDescentExact where

------------------------------------------------------------------------
-- THREE SELECTED 27-CUBIES DO NOT DETERMINE THE TRIADIC FACE
--
-- The mature trialectic owner already supplies two structured states with the
-- same complete A/B/C + pairwise-synthesis boundary but distinct irreducible
-- triadic faces.  This module projects that stronger witness down to the user's
-- pointed-cube view:
--
--   one selected cubie in A's 27-cube,
--   one selected cubie in B's 27-cube,
--   one selected cubie in C's 27-cube.
--
-- Even those three active selections, and indeed the entire compatible
-- structured boundary from which they are read, do not determine the triadic
-- face.  Any IIT observer that retains only the selected cubies therefore has
-- a concrete non-descent obligation before it may claim to recover the higher
-- gluing/face coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITPointedTernary27FaceGluingExact as Pointed
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Trialectic
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face

------------------------------------------------------------------------
-- 1. Three active cubies extracted from the cyclic A/B/C boundary.
------------------------------------------------------------------------

record ThreeSelectedCubies : Set where
  constructor three-selected-cubies
  field
    selectedA : Pointed.PointedTernary27Cube
    selectedB : Pointed.PointedTernary27Cube
    selectedC : Pointed.PointedTernary27Cube
open ThreeSelectedCubies public

selectedCubiesObserver :
  Trialectic.StructuredTrialecticState → ThreeSelectedCubies
selectedCubiesObserver state =
  three-selected-cubies
    (Pointed.pointed-ternary27-cube
      (Trialectic.leftCell
        (Trialectic.edgeAB (Trialectic.structuredBoundary state))))
    (Pointed.pointed-ternary27-cube
      (Trialectic.rightCell
        (Trialectic.edgeAB (Trialectic.structuredBoundary state))))
    (Pointed.pointed-ternary27-cube
      (Trialectic.rightCell
        (Trialectic.edgeBC (Trialectic.structuredBoundary state))))

selectedCubiesToPointedHyperform :
  ThreeSelectedCubies → Pointed.PointedThreeCubeHyperform
selectedCubiesToPointedHyperform cubies =
  Pointed.pointed-three-cube-hyperform
    (selectedA cubies)
    (selectedB cubies)
    (selectedC cubies)

------------------------------------------------------------------------
-- 2. The canonical reciprocal and underdetermined states expose exactly the
--    same selected A/B/C cubies because they already share the whole boundary.
------------------------------------------------------------------------

sameSelectedCubies :
  selectedCubiesObserver Trialectic.structuredReciprocal
  ≡ selectedCubiesObserver Trialectic.structuredUnderdetermined
sameSelectedCubies = refl

sameSelectedPointedHyperform :
  selectedCubiesToPointedHyperform
    (selectedCubiesObserver Trialectic.structuredReciprocal)
  ≡
  selectedCubiesToPointedHyperform
    (selectedCubiesObserver Trialectic.structuredUnderdetermined)
sameSelectedPointedHyperform = refl

------------------------------------------------------------------------
-- 3. But their triadic face relations are different.
------------------------------------------------------------------------

triadicFaceConsumer :
  Trialectic.StructuredTrialecticState → Face.TriadicFaceRelation
triadicFaceConsumer = Trialectic.structuredFaceConsumer

differentTriadicFace :
  triadicFaceConsumer Trialectic.structuredReciprocal
  ≡ triadicFaceConsumer Trialectic.structuredUnderdetermined
  → ⊥
differentTriadicFace = Trialectic.differentStructuredFace

------------------------------------------------------------------------
-- 4. Therefore the selected-cubie observer cannot factor the face consumer.
------------------------------------------------------------------------

selectedCubiesDoNotDetermineTriadicFace :
  Descent.FactorsThrough selectedCubiesObserver triadicFaceConsumer → ⊥
selectedCubiesDoNotDetermineTriadicFace =
  Descent.nonDescentWitnessBlocksFactorization
    (Descent.consumerNonDescentWitness
      Trialectic.structuredReciprocal
      Trialectic.structuredUnderdetermined
      sameSelectedCubies
      differentTriadicFace)

------------------------------------------------------------------------
-- 5. Promotion boundary.
------------------------------------------------------------------------

record PointedTriadicNonDescentBoundary : Set where
  constructor pointed-triadic-non-descent-boundary
  field
    threeSelectedCubiesAreExplicit : Bool
    threeSelectedCubiesRechartToExistingThreeCubeHyperform : Bool
    sameSelectedCubiesCanCarryDifferentTriadicFaces : Bool
    selectedCubiesDetermineTriadicFace : Bool
    selectedCubiesDetermineAdmissibleFaceGluingClassByDefinition : Bool
    IITScoreFromSelectedCubiesAutomaticallyRecoversTriadicFace : Bool

open PointedTriadicNonDescentBoundary public

canonicalPointedTriadicNonDescentBoundary : PointedTriadicNonDescentBoundary
canonicalPointedTriadicNonDescentBoundary =
  pointed-triadic-non-descent-boundary
    true true true
    false false false

selectedCubiesDoNotSelfPromoteToGluingClass :
  selectedCubiesDetermineAdmissibleFaceGluingClassByDefinition
    canonicalPointedTriadicNonDescentBoundary ≡ false
selectedCubiesDoNotSelfPromoteToGluingClass = refl

selectedCubiesDoNotSelfPromoteToIITRecovery :
  IITScoreFromSelectedCubiesAutomaticallyRecoversTriadicFace
    canonicalPointedTriadicNonDescentBoundary ≡ false
selectedCubiesDoNotSelfPromoteToIITRecovery = refl
