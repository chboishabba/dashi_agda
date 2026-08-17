module DASHI.Moonshine.P37MarkedX2DeckOrbitalHeckeExact where

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
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
--
-- DASHI CONTRIBUTION
--
-- Refine the actual p=37 marked Legendre T3/T5 correspondences to positive
-- deck-equivariant permutation orbitals on the source-native 3 x 6 level-2
-- carrier.
--
-- A summand is encoded by
--
--   (sigma ; h_j8, h_jConj0, h_jConj1) in S3 x S3^3
--
-- and acts by
--
--   (j,g) |-> (sigma(j), h_j g).
--
-- The h_j action is LEFT frame multiplication while the full-level-2 deck S3
-- acts on the RIGHT, so each summand commutes with deck change structurally.
-- Each summand is a bijection, with inverse obtained from the same existing
-- TriPermutation inverse operation.
--
-- The independently executed finite-field verifier
-- scripts/verify_p37_legendre_marked_hecke.py proves that the four T3 orbitals
-- and six T5 orbitals below reproduce, with multiplicity, the complete marked
-- Legendre F3/F5 adjacency tables.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Tri
import Base369 as Base
import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FullLevel2RigidificationExact as Level2
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedX2DeckTorsorExact as Deck37

------------------------------------------------------------------------
-- The same S3 object acts on coarse classes and by left multiplication on the
-- regular six-frame torsor.
------------------------------------------------------------------------

geometricToTri : P37.P37GeometricJ → Base.TriTruth
geometricToTri P37.j8 = Base.tri-low
geometricToTri P37.jConjugate0 = Base.tri-mid
geometricToTri P37.jConjugate1 = Base.tri-high

triToGeometric : Base.TriTruth → P37.P37GeometricJ
triToGeometric Base.tri-low = P37.j8
triToGeometric Base.tri-mid = P37.jConjugate0
triToGeometric Base.tri-high = P37.jConjugate1

geometricTriRoundTrip : (j : P37.P37GeometricJ) → triToGeometric (geometricToTri j) ≡ j
geometricTriRoundTrip P37.j8 = refl
geometricTriRoundTrip P37.jConjugate0 = refl
geometricTriRoundTrip P37.jConjugate1 = refl

triGeometricRoundTrip : (t : Base.TriTruth) → geometricToTri (triToGeometric t) ≡ t
triGeometricRoundTrip Base.tri-low = refl
triGeometricRoundTrip Base.tri-mid = refl
triGeometricRoundTrip Base.tri-high = refl

applyCoarse : Tri.TriPermutation → P37.P37GeometricJ → P37.P37GeometricJ
applyCoarse permutation j =
  triToGeometric (Tri.applyPermutation permutation (geometricToTri j))

leftR37 : P37.Frame6 → P37.Frame6
leftR37 f = Deck37.level2ToFrame (Level2.leftR (Deck37.frameToLevel2 f))

leftS37 : P37.Frame6 → P37.Frame6
leftS37 f = Deck37.level2ToFrame (Level2.leftS (Deck37.frameToLevel2 f))

applyLeft : Tri.TriPermutation → P37.Frame6 → P37.Frame6
applyLeft Tri.permIdentity f = f
applyLeft Tri.permRotate f = leftR37 f
applyLeft Tri.permRotate2 f = leftR37 (leftR37 f)
applyLeft Tri.permSwapMidHigh f = leftS37 f
applyLeft Tri.permSwapLowMid f = leftR37 (leftS37 f)
applyLeft Tri.permSwapLowHigh f = leftS37 (leftR37 f)

applyLeftInverseCorrect :
  (p : Tri.TriPermutation) → (f : P37.Frame6) →
  applyLeft (Tri.inversePermutation p) (applyLeft p f) ≡ f
applyLeftInverseCorrect Tri.permIdentity P37.frame0 = refl
applyLeftInverseCorrect Tri.permIdentity P37.frame1 = refl
applyLeftInverseCorrect Tri.permIdentity P37.frame2 = refl
applyLeftInverseCorrect Tri.permIdentity P37.frame3 = refl
applyLeftInverseCorrect Tri.permIdentity P37.frame4 = refl
applyLeftInverseCorrect Tri.permIdentity P37.frame5 = refl
applyLeftInverseCorrect Tri.permRotate P37.frame0 = refl
applyLeftInverseCorrect Tri.permRotate P37.frame1 = refl
applyLeftInverseCorrect Tri.permRotate P37.frame2 = refl
applyLeftInverseCorrect Tri.permRotate P37.frame3 = refl
applyLeftInverseCorrect Tri.permRotate P37.frame4 = refl
applyLeftInverseCorrect Tri.permRotate P37.frame5 = refl
applyLeftInverseCorrect Tri.permRotate2 P37.frame0 = refl
applyLeftInverseCorrect Tri.permRotate2 P37.frame1 = refl
applyLeftInverseCorrect Tri.permRotate2 P37.frame2 = refl
applyLeftInverseCorrect Tri.permRotate2 P37.frame3 = refl
applyLeftInverseCorrect Tri.permRotate2 P37.frame4 = refl
applyLeftInverseCorrect Tri.permRotate2 P37.frame5 = refl
applyLeftInverseCorrect Tri.permSwapLowMid P37.frame0 = refl
applyLeftInverseCorrect Tri.permSwapLowMid P37.frame1 = refl
applyLeftInverseCorrect Tri.permSwapLowMid P37.frame2 = refl
applyLeftInverseCorrect Tri.permSwapLowMid P37.frame3 = refl
applyLeftInverseCorrect Tri.permSwapLowMid P37.frame4 = refl
applyLeftInverseCorrect Tri.permSwapLowMid P37.frame5 = refl
applyLeftInverseCorrect Tri.permSwapLowHigh P37.frame0 = refl
applyLeftInverseCorrect Tri.permSwapLowHigh P37.frame1 = refl
applyLeftInverseCorrect Tri.permSwapLowHigh P37.frame2 = refl
applyLeftInverseCorrect Tri.permSwapLowHigh P37.frame3 = refl
applyLeftInverseCorrect Tri.permSwapLowHigh P37.frame4 = refl
applyLeftInverseCorrect Tri.permSwapLowHigh P37.frame5 = refl
applyLeftInverseCorrect Tri.permSwapMidHigh P37.frame0 = refl
applyLeftInverseCorrect Tri.permSwapMidHigh P37.frame1 = refl
applyLeftInverseCorrect Tri.permSwapMidHigh P37.frame2 = refl
applyLeftInverseCorrect Tri.permSwapMidHigh P37.frame3 = refl
applyLeftInverseCorrect Tri.permSwapMidHigh P37.frame4 = refl
applyLeftInverseCorrect Tri.permSwapMidHigh P37.frame5 = refl

applyLeftRightInverseCorrect :
  (p : Tri.TriPermutation) → (f : P37.Frame6) →
  applyLeft p (applyLeft (Tri.inversePermutation p) f) ≡ f
applyLeftRightInverseCorrect Tri.permIdentity P37.frame0 = refl
applyLeftRightInverseCorrect Tri.permIdentity P37.frame1 = refl
applyLeftRightInverseCorrect Tri.permIdentity P37.frame2 = refl
applyLeftRightInverseCorrect Tri.permIdentity P37.frame3 = refl
applyLeftRightInverseCorrect Tri.permIdentity P37.frame4 = refl
applyLeftRightInverseCorrect Tri.permIdentity P37.frame5 = refl
applyLeftRightInverseCorrect Tri.permRotate P37.frame0 = refl
applyLeftRightInverseCorrect Tri.permRotate P37.frame1 = refl
applyLeftRightInverseCorrect Tri.permRotate P37.frame2 = refl
applyLeftRightInverseCorrect Tri.permRotate P37.frame3 = refl
applyLeftRightInverseCorrect Tri.permRotate P37.frame4 = refl
applyLeftRightInverseCorrect Tri.permRotate P37.frame5 = refl
applyLeftRightInverseCorrect Tri.permRotate2 P37.frame0 = refl
applyLeftRightInverseCorrect Tri.permRotate2 P37.frame1 = refl
applyLeftRightInverseCorrect Tri.permRotate2 P37.frame2 = refl
applyLeftRightInverseCorrect Tri.permRotate2 P37.frame3 = refl
applyLeftRightInverseCorrect Tri.permRotate2 P37.frame4 = refl
applyLeftRightInverseCorrect Tri.permRotate2 P37.frame5 = refl
applyLeftRightInverseCorrect Tri.permSwapLowMid P37.frame0 = refl
applyLeftRightInverseCorrect Tri.permSwapLowMid P37.frame1 = refl
applyLeftRightInverseCorrect Tri.permSwapLowMid P37.frame2 = refl
applyLeftRightInverseCorrect Tri.permSwapLowMid P37.frame3 = refl
applyLeftRightInverseCorrect Tri.permSwapLowMid P37.frame4 = refl
applyLeftRightInverseCorrect Tri.permSwapLowMid P37.frame5 = refl
applyLeftRightInverseCorrect Tri.permSwapLowHigh P37.frame0 = refl
applyLeftRightInverseCorrect Tri.permSwapLowHigh P37.frame1 = refl
applyLeftRightInverseCorrect Tri.permSwapLowHigh P37.frame2 = refl
applyLeftRightInverseCorrect Tri.permSwapLowHigh P37.frame3 = refl
applyLeftRightInverseCorrect Tri.permSwapLowHigh P37.frame4 = refl
applyLeftRightInverseCorrect Tri.permSwapLowHigh P37.frame5 = refl
applyLeftRightInverseCorrect Tri.permSwapMidHigh P37.frame0 = refl
applyLeftRightInverseCorrect Tri.permSwapMidHigh P37.frame1 = refl
applyLeftRightInverseCorrect Tri.permSwapMidHigh P37.frame2 = refl
applyLeftRightInverseCorrect Tri.permSwapMidHigh P37.frame3 = refl
applyLeftRightInverseCorrect Tri.permSwapMidHigh P37.frame4 = refl
applyLeftRightInverseCorrect Tri.permSwapMidHigh P37.frame5 = refl

------------------------------------------------------------------------
-- Left multiplication commutes with right deck change.
------------------------------------------------------------------------

leftCommutesRightR :
  (p : Tri.TriPermutation) → (f : P37.Frame6) →
  applyLeft p (Deck37.rightR37 f) ≡ Deck37.rightR37 (applyLeft p f)
leftCommutesRightR Tri.permIdentity P37.frame0 = refl
leftCommutesRightR Tri.permIdentity P37.frame1 = refl
leftCommutesRightR Tri.permIdentity P37.frame2 = refl
leftCommutesRightR Tri.permIdentity P37.frame3 = refl
leftCommutesRightR Tri.permIdentity P37.frame4 = refl
leftCommutesRightR Tri.permIdentity P37.frame5 = refl
leftCommutesRightR Tri.permRotate P37.frame0 = refl
leftCommutesRightR Tri.permRotate P37.frame1 = refl
leftCommutesRightR Tri.permRotate P37.frame2 = refl
leftCommutesRightR Tri.permRotate P37.frame3 = refl
leftCommutesRightR Tri.permRotate P37.frame4 = refl
leftCommutesRightR Tri.permRotate P37.frame5 = refl
leftCommutesRightR Tri.permRotate2 P37.frame0 = refl
leftCommutesRightR Tri.permRotate2 P37.frame1 = refl
leftCommutesRightR Tri.permRotate2 P37.frame2 = refl
leftCommutesRightR Tri.permRotate2 P37.frame3 = refl
leftCommutesRightR Tri.permRotate2 P37.frame4 = refl
leftCommutesRightR Tri.permRotate2 P37.frame5 = refl
leftCommutesRightR Tri.permSwapLowMid P37.frame0 = refl
leftCommutesRightR Tri.permSwapLowMid P37.frame1 = refl
leftCommutesRightR Tri.permSwapLowMid P37.frame2 = refl
leftCommutesRightR Tri.permSwapLowMid P37.frame3 = refl
leftCommutesRightR Tri.permSwapLowMid P37.frame4 = refl
leftCommutesRightR Tri.permSwapLowMid P37.frame5 = refl
leftCommutesRightR Tri.permSwapLowHigh P37.frame0 = refl
leftCommutesRightR Tri.permSwapLowHigh P37.frame1 = refl
leftCommutesRightR Tri.permSwapLowHigh P37.frame2 = refl
leftCommutesRightR Tri.permSwapLowHigh P37.frame3 = refl
leftCommutesRightR Tri.permSwapLowHigh P37.frame4 = refl
leftCommutesRightR Tri.permSwapLowHigh P37.frame5 = refl
leftCommutesRightR Tri.permSwapMidHigh P37.frame0 = refl
leftCommutesRightR Tri.permSwapMidHigh P37.frame1 = refl
leftCommutesRightR Tri.permSwapMidHigh P37.frame2 = refl
leftCommutesRightR Tri.permSwapMidHigh P37.frame3 = refl
leftCommutesRightR Tri.permSwapMidHigh P37.frame4 = refl
leftCommutesRightR Tri.permSwapMidHigh P37.frame5 = refl

leftCommutesRightS :
  (p : Tri.TriPermutation) → (f : P37.Frame6) →
  applyLeft p (Deck37.rightS37 f) ≡ Deck37.rightS37 (applyLeft p f)
leftCommutesRightS Tri.permIdentity P37.frame0 = refl
leftCommutesRightS Tri.permIdentity P37.frame1 = refl
leftCommutesRightS Tri.permIdentity P37.frame2 = refl
leftCommutesRightS Tri.permIdentity P37.frame3 = refl
leftCommutesRightS Tri.permIdentity P37.frame4 = refl
leftCommutesRightS Tri.permIdentity P37.frame5 = refl
leftCommutesRightS Tri.permRotate P37.frame0 = refl
leftCommutesRightS Tri.permRotate P37.frame1 = refl
leftCommutesRightS Tri.permRotate P37.frame2 = refl
leftCommutesRightS Tri.permRotate P37.frame3 = refl
leftCommutesRightS Tri.permRotate P37.frame4 = refl
leftCommutesRightS Tri.permRotate P37.frame5 = refl
leftCommutesRightS Tri.permRotate2 P37.frame0 = refl
leftCommutesRightS Tri.permRotate2 P37.frame1 = refl
leftCommutesRightS Tri.permRotate2 P37.frame2 = refl
leftCommutesRightS Tri.permRotate2 P37.frame3 = refl
leftCommutesRightS Tri.permRotate2 P37.frame4 = refl
leftCommutesRightS Tri.permRotate2 P37.frame5 = refl
leftCommutesRightS Tri.permSwapLowMid P37.frame0 = refl
leftCommutesRightS Tri.permSwapLowMid P37.frame1 = refl
leftCommutesRightS Tri.permSwapLowMid P37.frame2 = refl
leftCommutesRightS Tri.permSwapLowMid P37.frame3 = refl
leftCommutesRightS Tri.permSwapLowMid P37.frame4 = refl
leftCommutesRightS Tri.permSwapLowMid P37.frame5 = refl
leftCommutesRightS Tri.permSwapLowHigh P37.frame0 = refl
leftCommutesRightS Tri.permSwapLowHigh P37.frame1 = refl
leftCommutesRightS Tri.permSwapLowHigh P37.frame2 = refl
leftCommutesRightS Tri.permSwapLowHigh P37.frame3 = refl
leftCommutesRightS Tri.permSwapLowHigh P37.frame4 = refl
leftCommutesRightS Tri.permSwapLowHigh P37.frame5 = refl
leftCommutesRightS Tri.permSwapMidHigh P37.frame0 = refl
leftCommutesRightS Tri.permSwapMidHigh P37.frame1 = refl
leftCommutesRightS Tri.permSwapMidHigh P37.frame2 = refl
leftCommutesRightS Tri.permSwapMidHigh P37.frame3 = refl
leftCommutesRightS Tri.permSwapMidHigh P37.frame4 = refl
leftCommutesRightS Tri.permSwapMidHigh P37.frame5 = refl

------------------------------------------------------------------------
-- Orbital permutation specification.
------------------------------------------------------------------------

record DeckOrbitalSpec : Set where
  constructor orbitalSpec
  field
    coarsePermutation : Tri.TriPermutation
    atJ8 : Tri.TriPermutation
    atJConjugate0 : Tri.TriPermutation
    atJConjugate1 : Tri.TriPermutation

open DeckOrbitalSpec public

localPermutation : DeckOrbitalSpec → P37.P37GeometricJ → Tri.TriPermutation
localPermutation spec P37.j8 = atJ8 spec
localPermutation spec P37.jConjugate0 = atJConjugate0 spec
localPermutation spec P37.jConjugate1 = atJConjugate1 spec

applyOrbital : DeckOrbitalSpec → P37.P37FullLevel2Point → P37.P37FullLevel2Point
applyOrbital spec (P37.p37MarkedPoint j frame) =
  P37.p37MarkedPoint
    (applyCoarse (coarsePermutation spec) j)
    (applyLeft (localPermutation spec j) frame)

applyOrbitalCommutesDeckR :
  (spec : DeckOrbitalSpec) → (x : P37.P37FullLevel2Point) →
  applyOrbital spec (Deck37.rightRPoint x)
  ≡ Deck37.rightRPoint (applyOrbital spec x)
applyOrbitalCommutesDeckR spec (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint (applyCoarse (coarsePermutation spec) P37.j8))
    (leftCommutesRightR (atJ8 spec) frame)
applyOrbitalCommutesDeckR spec (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint (applyCoarse (coarsePermutation spec) P37.jConjugate0))
    (leftCommutesRightR (atJConjugate0 spec) frame)
applyOrbitalCommutesDeckR spec (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint (applyCoarse (coarsePermutation spec) P37.jConjugate1))
    (leftCommutesRightR (atJConjugate1 spec) frame)

applyOrbitalCommutesDeckS :
  (spec : DeckOrbitalSpec) → (x : P37.P37FullLevel2Point) →
  applyOrbital spec (Deck37.rightSPoint x)
  ≡ Deck37.rightSPoint (applyOrbital spec x)
applyOrbitalCommutesDeckS spec (P37.p37MarkedPoint P37.j8 frame) =
  cong (P37.p37MarkedPoint (applyCoarse (coarsePermutation spec) P37.j8))
    (leftCommutesRightS (atJ8 spec) frame)
applyOrbitalCommutesDeckS spec (P37.p37MarkedPoint P37.jConjugate0 frame) =
  cong (P37.p37MarkedPoint (applyCoarse (coarsePermutation spec) P37.jConjugate0))
    (leftCommutesRightS (atJConjugate0 spec) frame)
applyOrbitalCommutesDeckS spec (P37.p37MarkedPoint P37.jConjugate1 frame) =
  cong (P37.p37MarkedPoint (applyCoarse (coarsePermutation spec) P37.jConjugate1))
    (leftCommutesRightS (atJConjugate1 spec) frame)

------------------------------------------------------------------------
-- Exact four T3 and six T5 orbital summands found by the independent finite
-- reduction.  These are source-native positive permutation targets.
------------------------------------------------------------------------

t3o0 t3o1 t3o2 t3o3 : DeckOrbitalSpec
t3o0 = orbitalSpec Tri.permSwapMidHigh Tri.permSwapLowMid Tri.permIdentity Tri.permIdentity
t3o1 = orbitalSpec Tri.permSwapMidHigh Tri.permSwapLowMid Tri.permSwapMidHigh Tri.permSwapMidHigh
t3o2 = orbitalSpec Tri.permRotate Tri.permSwapMidHigh Tri.permSwapLowHigh Tri.permRotate
t3o3 = orbitalSpec Tri.permRotate2 Tri.permRotate2 Tri.permSwapMidHigh Tri.permSwapLowHigh

t5o0 t5o1 t5o2 t5o3 t5o4 t5o5 : DeckOrbitalSpec
t5o0 = orbitalSpec Tri.permSwapMidHigh Tri.permRotate Tri.permSwapMidHigh Tri.permSwapLowMid
t5o1 = orbitalSpec Tri.permSwapMidHigh Tri.permRotate2 Tri.permSwapLowMid Tri.permSwapMidHigh
t5o2 = orbitalSpec Tri.permSwapLowMid Tri.permIdentity Tri.permIdentity Tri.permSwapLowHigh
t5o3 = orbitalSpec Tri.permRotate Tri.permSwapLowHigh Tri.permSwapLowMid Tri.permRotate2
t5o4 = orbitalSpec Tri.permRotate2 Tri.permRotate Tri.permSwapLowHigh Tri.permSwapLowMid
t5o5 = orbitalSpec Tri.permSwapLowHigh Tri.permSwapLowMid Tri.permSwapLowHigh Tri.permSwapLowMid

t3Orbital : Fin 4 → DeckOrbitalSpec
t3Orbital zero = t3o0
t3Orbital (suc zero) = t3o1
t3Orbital (suc (suc zero)) = t3o2
t3Orbital (suc (suc (suc zero))) = t3o3

t5Orbital : Fin 6 → DeckOrbitalSpec
t5Orbital zero = t5o0
t5Orbital (suc zero) = t5o1
t5Orbital (suc (suc zero)) = t5o2
t5Orbital (suc (suc (suc zero))) = t5o3
t5Orbital (suc (suc (suc (suc zero)))) = t5o4
t5Orbital (suc (suc (suc (suc (suc zero))))) = t5o5

orbitalT3Neighbour : P37.P37FullLevel2Point → Fin 4 → P37.P37FullLevel2Point
orbitalT3Neighbour x edge = applyOrbital (t3Orbital edge) x

orbitalT5Neighbour : P37.P37FullLevel2Point → Fin 6 → P37.P37FullLevel2Point
orbitalT5Neighbour x edge = applyOrbital (t5Orbital edge) x

OrbitalT3 : Positive.PositiveFiniteNeighbourSystem P37.P37FullLevel2Point
OrbitalT3 = record
  { Positive.arity = 4
  ; Positive.neighbour = orbitalT3Neighbour
  }

OrbitalT5 : Positive.PositiveFiniteNeighbourSystem P37.P37FullLevel2Point
OrbitalT5 = record
  { Positive.arity = 6
  ; Positive.neighbour = orbitalT5Neighbour
  }

orbitalT3DeckREquivariant :
  (x : P37.P37FullLevel2Point) → (edge : Fin 4) →
  orbitalT3Neighbour (Deck37.rightRPoint x) edge
  ≡ Deck37.rightRPoint (orbitalT3Neighbour x edge)
orbitalT3DeckREquivariant x edge = applyOrbitalCommutesDeckR (t3Orbital edge) x

orbitalT3DeckSEquivariant :
  (x : P37.P37FullLevel2Point) → (edge : Fin 4) →
  orbitalT3Neighbour (Deck37.rightSPoint x) edge
  ≡ Deck37.rightSPoint (orbitalT3Neighbour x edge)
orbitalT3DeckSEquivariant x edge = applyOrbitalCommutesDeckS (t3Orbital edge) x

orbitalT5DeckREquivariant :
  (x : P37.P37FullLevel2Point) → (edge : Fin 6) →
  orbitalT5Neighbour (Deck37.rightRPoint x) edge
  ≡ Deck37.rightRPoint (orbitalT5Neighbour x edge)
orbitalT5DeckREquivariant x edge = applyOrbitalCommutesDeckR (t5Orbital edge) x

orbitalT5DeckSEquivariant :
  (x : P37.P37FullLevel2Point) → (edge : Fin 6) →
  orbitalT5Neighbour (Deck37.rightSPoint x) edge
  ≡ Deck37.rightSPoint (orbitalT5Neighbour x edge)
orbitalT5DeckSEquivariant x edge = applyOrbitalCommutesDeckS (t5Orbital edge) x

record P37MarkedX2DeckOrbitalBoundary : Set where
  field
    t3FourPermutationOrbitalsConstructed : Bool
    t3FourPermutationOrbitalsConstructedIsTrue :
      t3FourPermutationOrbitalsConstructed ≡ true

    t5SixPermutationOrbitalsConstructed : Bool
    t5SixPermutationOrbitalsConstructedIsTrue :
      t5SixPermutationOrbitalsConstructed ≡ true

    everyOrbitalDeckS3Equivariant : Bool
    everyOrbitalDeckS3EquivariantIsTrue : everyOrbitalDeckS3Equivariant ≡ true

    orbitalTablesIndependentlyMatchLegendreAdjacency : Bool
    orbitalTablesIndependentlyMatchLegendreAdjacencyIsTrue :
      orbitalTablesIndependentlyMatchLegendreAdjacency ≡ true

canonicalP37MarkedX2DeckOrbitalBoundary : P37MarkedX2DeckOrbitalBoundary
canonicalP37MarkedX2DeckOrbitalBoundary = record
  { t3FourPermutationOrbitalsConstructed = true
  ; t3FourPermutationOrbitalsConstructedIsTrue = refl
  ; t5SixPermutationOrbitalsConstructed = true
  ; t5SixPermutationOrbitalsConstructedIsTrue = refl
  ; everyOrbitalDeckS3Equivariant = true
  ; everyOrbitalDeckS3EquivariantIsTrue = refl
  ; orbitalTablesIndependentlyMatchLegendreAdjacency = true
  ; orbitalTablesIndependentlyMatchLegendreAdjacencyIsTrue = refl
  }
