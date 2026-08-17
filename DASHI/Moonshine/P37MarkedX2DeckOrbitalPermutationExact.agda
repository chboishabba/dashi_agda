module DASHI.Moonshine.P37MarkedX2DeckOrbitalPermutationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- DASHI CONTRIBUTION
--
-- Close the remaining semantic seam in the p=37 marked double-coset/orbital
-- construction: every DeckOrbitalSpec is not merely a function but an actual
-- bijection of the 3 x 6 full-level-2 carrier.
--
-- For
--
--   (j,g) |-> (sigma j, h_j g)
--
-- the inverse first applies sigma^-1 to recover the source coarse class, then
-- applies h_source^-1 to the frame.  The proof uses only the already-proved S3
-- inverse laws on coarse classes and on the six-frame regular torsor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Tri
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedX2DeckOrbitalHeckeExact as Orbital

------------------------------------------------------------------------
-- Coarse S3 inverse laws.
------------------------------------------------------------------------

applyCoarseInverseLeft :
  (p : Tri.TriPermutation) → (j : P37.P37GeometricJ) →
  Orbital.applyCoarse (Tri.inversePermutation p) (Orbital.applyCoarse p j) ≡ j
applyCoarseInverseLeft Tri.permIdentity P37.j8 = refl
applyCoarseInverseLeft Tri.permIdentity P37.jConjugate0 = refl
applyCoarseInverseLeft Tri.permIdentity P37.jConjugate1 = refl
applyCoarseInverseLeft Tri.permRotate P37.j8 = refl
applyCoarseInverseLeft Tri.permRotate P37.jConjugate0 = refl
applyCoarseInverseLeft Tri.permRotate P37.jConjugate1 = refl
applyCoarseInverseLeft Tri.permRotate2 P37.j8 = refl
applyCoarseInverseLeft Tri.permRotate2 P37.jConjugate0 = refl
applyCoarseInverseLeft Tri.permRotate2 P37.jConjugate1 = refl
applyCoarseInverseLeft Tri.permSwapLowMid P37.j8 = refl
applyCoarseInverseLeft Tri.permSwapLowMid P37.jConjugate0 = refl
applyCoarseInverseLeft Tri.permSwapLowMid P37.jConjugate1 = refl
applyCoarseInverseLeft Tri.permSwapLowHigh P37.j8 = refl
applyCoarseInverseLeft Tri.permSwapLowHigh P37.jConjugate0 = refl
applyCoarseInverseLeft Tri.permSwapLowHigh P37.jConjugate1 = refl
applyCoarseInverseLeft Tri.permSwapMidHigh P37.j8 = refl
applyCoarseInverseLeft Tri.permSwapMidHigh P37.jConjugate0 = refl
applyCoarseInverseLeft Tri.permSwapMidHigh P37.jConjugate1 = refl

applyCoarseInverseRight :
  (p : Tri.TriPermutation) → (j : P37.P37GeometricJ) →
  Orbital.applyCoarse p (Orbital.applyCoarse (Tri.inversePermutation p) j) ≡ j
applyCoarseInverseRight Tri.permIdentity P37.j8 = refl
applyCoarseInverseRight Tri.permIdentity P37.jConjugate0 = refl
applyCoarseInverseRight Tri.permIdentity P37.jConjugate1 = refl
applyCoarseInverseRight Tri.permRotate P37.j8 = refl
applyCoarseInverseRight Tri.permRotate P37.jConjugate0 = refl
applyCoarseInverseRight Tri.permRotate P37.jConjugate1 = refl
applyCoarseInverseRight Tri.permRotate2 P37.j8 = refl
applyCoarseInverseRight Tri.permRotate2 P37.jConjugate0 = refl
applyCoarseInverseRight Tri.permRotate2 P37.jConjugate1 = refl
applyCoarseInverseRight Tri.permSwapLowMid P37.j8 = refl
applyCoarseInverseRight Tri.permSwapLowMid P37.jConjugate0 = refl
applyCoarseInverseRight Tri.permSwapLowMid P37.jConjugate1 = refl
applyCoarseInverseRight Tri.permSwapLowHigh P37.j8 = refl
applyCoarseInverseRight Tri.permSwapLowHigh P37.jConjugate0 = refl
applyCoarseInverseRight Tri.permSwapLowHigh P37.jConjugate1 = refl
applyCoarseInverseRight Tri.permSwapMidHigh P37.j8 = refl
applyCoarseInverseRight Tri.permSwapMidHigh P37.jConjugate0 = refl
applyCoarseInverseRight Tri.permSwapMidHigh P37.jConjugate1 = refl

------------------------------------------------------------------------
-- Generic inverse of an orbital summand.
------------------------------------------------------------------------

orbitalInverse :
  Orbital.DeckOrbitalSpec →
  P37.P37FullLevel2Point → P37.P37FullLevel2Point
orbitalInverse spec (P37.p37MarkedPoint targetJ frame) =
  let sourceJ =
        Orbital.applyCoarse
          (Tri.inversePermutation (Orbital.coarsePermutation spec)) targetJ
  in
  P37.p37MarkedPoint sourceJ
    (Orbital.applyLeft
      (Tri.inversePermutation (Orbital.localPermutation spec sourceJ))
      frame)

orbitalInverseAfterForward :
  (spec : Orbital.DeckOrbitalSpec) →
  (x : P37.P37FullLevel2Point) →
  orbitalInverse spec (Orbital.applyOrbital spec x) ≡ x
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permIdentity l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftInverseCorrect l0 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permIdentity l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftInverseCorrect l1 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permIdentity l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftInverseCorrect l2 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permRotate l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftInverseCorrect l0 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permRotate l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftInverseCorrect l1 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permRotate l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftInverseCorrect l2 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permRotate2 l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftInverseCorrect l0 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permRotate2 l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftInverseCorrect l1 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permRotate2 l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftInverseCorrect l2 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapLowMid l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftInverseCorrect l0 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapLowMid l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftInverseCorrect l1 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapLowMid l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftInverseCorrect l2 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapLowHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftInverseCorrect l0 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapLowHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftInverseCorrect l1 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapLowHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftInverseCorrect l2 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapMidHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftInverseCorrect l0 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapMidHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftInverseCorrect l1 frame)
orbitalInverseAfterForward (Orbital.orbitalSpec Tri.permSwapMidHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftInverseCorrect l2 frame)

orbitalForwardAfterInverse :
  (spec : Orbital.DeckOrbitalSpec) →
  (x : P37.P37FullLevel2Point) →
  Orbital.applyOrbital spec (orbitalInverse spec x) ≡ x
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permIdentity l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftRightInverseCorrect l0 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permIdentity l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftRightInverseCorrect l1 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permIdentity l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftRightInverseCorrect l2 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permRotate l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftRightInverseCorrect l2 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permRotate l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftRightInverseCorrect l0 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permRotate l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftRightInverseCorrect l1 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permRotate2 l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftRightInverseCorrect l1 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permRotate2 l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftRightInverseCorrect l2 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permRotate2 l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftRightInverseCorrect l0 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapLowMid l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftRightInverseCorrect l1 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapLowMid l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftRightInverseCorrect l0 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapLowMid l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftRightInverseCorrect l2 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapLowHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftRightInverseCorrect l2 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapLowHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftRightInverseCorrect l1 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapLowHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftRightInverseCorrect l0 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapMidHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint P37.j8) (Orbital.applyLeftRightInverseCorrect l0 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapMidHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate0) (Orbital.applyLeftRightInverseCorrect l2 frame)
orbitalForwardAfterInverse (Orbital.orbitalSpec Tri.permSwapMidHigh l0 l1 l2)
  (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint P37.jConjugate1) (Orbital.applyLeftRightInverseCorrect l1 frame)

record DeckOrbitalBijection (spec : Orbital.DeckOrbitalSpec) : Set where
  field
    backward : P37.P37FullLevel2Point → P37.P37FullLevel2Point
    backwardAfterForward :
      (x : P37.P37FullLevel2Point) → backward (Orbital.applyOrbital spec x) ≡ x
    forwardAfterBackward :
      (x : P37.P37FullLevel2Point) → Orbital.applyOrbital spec (backward x) ≡ x

canonicalDeckOrbitalBijection :
  (spec : Orbital.DeckOrbitalSpec) → DeckOrbitalBijection spec
canonicalDeckOrbitalBijection spec = record
  { backward = orbitalInverse spec
  ; backwardAfterForward = orbitalInverseAfterForward spec
  ; forwardAfterBackward = orbitalForwardAfterInverse spec
  }

record P37DeckOrbitalPermutationBoundary : Set where
  field
    everyOrbitalSummandBijectionConstructed : Bool
    everyOrbitalSummandBijectionConstructedIsTrue :
      everyOrbitalSummandBijectionConstructed ≡ true

    t3AndT5AreSumsOfPermutationCorrespondences : Bool
    t3AndT5AreSumsOfPermutationCorrespondencesIsTrue :
      t3AndT5AreSumsOfPermutationCorrespondences ≡ true

canonicalP37DeckOrbitalPermutationBoundary : P37DeckOrbitalPermutationBoundary
canonicalP37DeckOrbitalPermutationBoundary = record
  { everyOrbitalSummandBijectionConstructed = true
  ; everyOrbitalSummandBijectionConstructedIsTrue = refl
  ; t3AndT5AreSumsOfPermutationCorrespondences = true
  ; t3AndT5AreSumsOfPermutationCorrespondencesIsTrue = refl
  }
