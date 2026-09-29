module DASHI.Moonshine.OggSSPP2F4CurveKleinActionGroupoidExact where

------------------------------------------------------------------------
-- INDEPENDENT ARITHMETIC CURVE-POINT KLEIN ACTION GROUPOID
--
-- On the nine ACTUAL F4 rational points of E:y²+y=x³, the commuting
-- Frobenius and coordinate-negation involutions give the elementary
-- two-generator Klein group C2 x C2.
--
-- This owner inhabits the existing generic group-action / orbit-presentation
-- contract, with all 4x4x9 composition cases checked definitionally.
-- The component space has four orbits of sizes 1,2,2,4.  This concrete
-- arithmetic groupoid FAILS the ten-component Monster p=2 recognition gate.
--
-- A separate Gamma_0(4), inertia, or local-stack source is still missing.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Generic
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveFrobeniusNegationOrbitExact as Klein

KleinGroup : Set
KleinGroup = Bool × Bool

xor₂ : Bool → Bool → Bool
xor₂ false b = b
xor₂ true false = true
xor₂ true true = false

combineKlein : KleinGroup → KleinGroup → KleinGroup
combineKlein (a , b) (c , d) =
  xor₂ a c , xor₂ b d

actKlein : KleinGroup → Curve.RationalF4Point → Curve.RationalF4Point
actKlein (frob , negation) point =
  Klein.kleinAct frob negation point

kleinIdentityActs :
  (point : Curve.RationalF4Point) →
  actKlein (false , false) point ≡ point
kleinIdentityActs point = refl

kleinCombineActs :
  (g h : KleinGroup) (point : Curve.RationalF4Point) →
  actKlein (combineKlein g h) point
    ≡ actKlein g (actKlein h point)
kleinCombineActs (false , false) (false , false) Curve.infinity = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , false) (false , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , false) (false , true) Curve.infinity = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , false) (false , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , false) (true , false) Curve.infinity = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , false) (true , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , false) (true , true) Curve.infinity = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , false) (true , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , true) (false , false) Curve.infinity = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , true) (false , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , true) (false , true) Curve.infinity = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , true) (false , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , true) (true , false) Curve.infinity = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , true) (true , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (false , true) (true , true) Curve.infinity = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (false , true) (true , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , false) (false , false) Curve.infinity = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , false) (false , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , false) (false , true) Curve.infinity = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , false) (false , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , false) (true , false) Curve.infinity = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , false) (true , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , false) (true , true) Curve.infinity = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , false) (true , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , true) (false , false) Curve.infinity = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , true) (false , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , true) (false , true) Curve.infinity = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , true) (false , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , true) (true , false) Curve.infinity = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , true) (true , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinCombineActs (true , true) (true , true) Curve.infinity = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.p00) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.p01) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.p1Zeta) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.pZetaZeta) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinCombineActs (true , true) (true , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

kleinInverseActs :
  (g : KleinGroup) (point : Curve.RationalF4Point) →
  actKlein g (actKlein g point) ≡ point
kleinInverseActs (false , false) Curve.infinity = refl
kleinInverseActs (false , false) (Curve.affine Curve.p00) = refl
kleinInverseActs (false , false) (Curve.affine Curve.p01) = refl
kleinInverseActs (false , false) (Curve.affine Curve.p1Zeta) = refl
kleinInverseActs (false , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinInverseActs (false , false) (Curve.affine Curve.pZetaZeta) = refl
kleinInverseActs (false , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinInverseActs (false , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinInverseActs (false , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinInverseActs (false , true) Curve.infinity = refl
kleinInverseActs (false , true) (Curve.affine Curve.p00) = refl
kleinInverseActs (false , true) (Curve.affine Curve.p01) = refl
kleinInverseActs (false , true) (Curve.affine Curve.p1Zeta) = refl
kleinInverseActs (false , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinInverseActs (false , true) (Curve.affine Curve.pZetaZeta) = refl
kleinInverseActs (false , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinInverseActs (false , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinInverseActs (false , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinInverseActs (true , false) Curve.infinity = refl
kleinInverseActs (true , false) (Curve.affine Curve.p00) = refl
kleinInverseActs (true , false) (Curve.affine Curve.p01) = refl
kleinInverseActs (true , false) (Curve.affine Curve.p1Zeta) = refl
kleinInverseActs (true , false) (Curve.affine Curve.p1ZetaSquared) = refl
kleinInverseActs (true , false) (Curve.affine Curve.pZetaZeta) = refl
kleinInverseActs (true , false) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinInverseActs (true , false) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinInverseActs (true , false) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
kleinInverseActs (true , true) Curve.infinity = refl
kleinInverseActs (true , true) (Curve.affine Curve.p00) = refl
kleinInverseActs (true , true) (Curve.affine Curve.p01) = refl
kleinInverseActs (true , true) (Curve.affine Curve.p1Zeta) = refl
kleinInverseActs (true , true) (Curve.affine Curve.p1ZetaSquared) = refl
kleinInverseActs (true , true) (Curve.affine Curve.pZetaZeta) = refl
kleinInverseActs (true , true) (Curve.affine Curve.pZetaZetaSquared) = refl
kleinInverseActs (true , true) (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinInverseActs (true , true) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

arithmeticKleinAction :
  Symmetry.InvertibleSymmetryAction
    Curve.RationalF4Point KleinGroup
arithmeticKleinAction =
  Symmetry.invertibleSymmetryAction
    (false , false)
    combineKlein
    (λ g → g)
    actKlein
    kleinIdentityActs
    kleinCombineActs
    kleinInverseActs
    kleinInverseActs

arithmeticKleinOrbitPresentation :
  Generic.OrbitPresentation arithmeticKleinAction
arithmeticKleinOrbitPresentation =
  Generic.orbitPresentation
    Klein.CurveKleinOrbit
    Klein.kleinOrbit
    Klein.kleinRepresentative
    (λ g p →
      Klein.kleinActPreservesOrbit (proj₁ g) (proj₂ g) p)
    Klein.kleinRepresentativeHasItsLabel
    Klein.kleinReachFlags
    Klein.kleinReachEveryPoint

-- These are action-stabilizer profile counts of C2 x C2:
-- singleton has stabilizer 4; the two pairs have stabilizer 2;
-- the four-point orbit has trivial stabilizer.
jointOrbitSize : Klein.CurveKleinOrbit → Nat
jointOrbitSize Klein.infinitySingleton = 1
jointOrbitSize Klein.zeroXPair = 2
jointOrbitSize Klein.unitXPair = 2
jointOrbitSize Klein.primitiveXFour = 4

expectedStabilizerSize : Klein.CurveKleinOrbit → Nat
expectedStabilizerSize Klein.infinitySingleton = 4
expectedStabilizerSize Klein.zeroXPair = 2
expectedStabilizerSize Klein.unitXPair = 2
expectedStabilizerSize Klein.primitiveXFour = 1

orbitStabilizerCountFour :
  (orbit : Klein.CurveKleinOrbit) →
  jointOrbitSize orbit * expectedStabilizerSize orbit ≡ 4
orbitStabilizerCountFour Klein.infinitySingleton = refl
orbitStabilizerCountFour Klein.zeroXPair = refl
orbitStabilizerCountFour Klein.unitXPair = refl
orbitStabilizerCountFour Klein.primitiveXFour = refl

------------------------------------------------------------------------
-- Action-derived stabilizer classifier (not merely chosen multiplicities).
------------------------------------------------------------------------

not₂ : Bool → Bool
not₂ false = true
not₂ true = false

and₂ : Bool → Bool → Bool
and₂ false b = false
and₂ true b = b

same₂ : Bool → Bool → Bool
same₂ false false = true
same₂ true true = true
same₂ _ _ = false

stabilizerTruth : Klein.CurveKleinOrbit → KleinGroup → Bool
stabilizerTruth Klein.infinitySingleton g = true
stabilizerTruth Klein.zeroXPair (frob , negation) = not₂ negation
stabilizerTruth Klein.unitXPair (frob , negation) = same₂ frob negation
stabilizerTruth Klein.primitiveXFour (frob , negation) =
  and₂ (not₂ frob) (not₂ negation)

stabilizerTruthSound :
  (orbit : Klein.CurveKleinOrbit) (g : KleinGroup) →
  stabilizerTruth orbit g ≡ true →
  actKlein g (Klein.kleinRepresentative orbit)
    ≡ Klein.kleinRepresentative orbit
stabilizerTruthSound Klein.infinitySingleton (false , false) h = refl
stabilizerTruthSound Klein.infinitySingleton (false , true) h = refl
stabilizerTruthSound Klein.infinitySingleton (true , false) h = refl
stabilizerTruthSound Klein.infinitySingleton (true , true) h = refl
stabilizerTruthSound Klein.zeroXPair (false , false) h = refl
stabilizerTruthSound Klein.zeroXPair (false , true) ()
stabilizerTruthSound Klein.zeroXPair (true , false) h = refl
stabilizerTruthSound Klein.zeroXPair (true , true) ()
stabilizerTruthSound Klein.unitXPair (false , false) h = refl
stabilizerTruthSound Klein.unitXPair (false , true) ()
stabilizerTruthSound Klein.unitXPair (true , false) ()
stabilizerTruthSound Klein.unitXPair (true , true) h = refl
stabilizerTruthSound Klein.primitiveXFour (false , false) h = refl
stabilizerTruthSound Klein.primitiveXFour (false , true) ()
stabilizerTruthSound Klein.primitiveXFour (true , false) ()
stabilizerTruthSound Klein.primitiveXFour (true , true) ()

stabilizerTruthComplete :
  (orbit : Klein.CurveKleinOrbit) (g : KleinGroup) →
  actKlein g (Klein.kleinRepresentative orbit)
    ≡ Klein.kleinRepresentative orbit →
  stabilizerTruth orbit g ≡ true
stabilizerTruthComplete Klein.infinitySingleton (false , false) h = refl
stabilizerTruthComplete Klein.infinitySingleton (false , true) h = refl
stabilizerTruthComplete Klein.infinitySingleton (true , false) h = refl
stabilizerTruthComplete Klein.infinitySingleton (true , true) h = refl
stabilizerTruthComplete Klein.zeroXPair (false , false) h = refl
stabilizerTruthComplete Klein.zeroXPair (false , true) ()
stabilizerTruthComplete Klein.zeroXPair (true , false) h = refl
stabilizerTruthComplete Klein.zeroXPair (true , true) ()
stabilizerTruthComplete Klein.unitXPair (false , false) h = refl
stabilizerTruthComplete Klein.unitXPair (false , true) ()
stabilizerTruthComplete Klein.unitXPair (true , false) ()
stabilizerTruthComplete Klein.unitXPair (true , true) h = refl
stabilizerTruthComplete Klein.primitiveXFour (false , false) h = refl
stabilizerTruthComplete Klein.primitiveXFour (false , true) ()
stabilizerTruthComplete Klein.primitiveXFour (true , false) ()
stabilizerTruthComplete Klein.primitiveXFour (true , true) ()

boolCount : Bool → Nat
boolCount false = 0
boolCount true = 1

computedStabilizerCount : Klein.CurveKleinOrbit → Nat
computedStabilizerCount orbit =
  boolCount (stabilizerTruth orbit (false , false))
  + boolCount (stabilizerTruth orbit (false , true))
  + boolCount (stabilizerTruth orbit (true , false))
  + boolCount (stabilizerTruth orbit (true , true))

stabilizerCountIsExpected :
  (orbit : Klein.CurveKleinOrbit) →
  computedStabilizerCount orbit ≡ expectedStabilizerSize orbit
stabilizerCountIsExpected Klein.infinitySingleton = refl
stabilizerCountIsExpected Klein.zeroXPair = refl
stabilizerCountIsExpected Klein.unitXPair = refl
stabilizerCountIsExpected Klein.primitiveXFour = refl

record F4CurveKleinActionGroupoidBoundary : Set where
  constructor f4-curve-klein-action-groupoid-boundary
  field
    literalNinePointArithmeticCarrier : Bool
    genuineInvertibleKleinActionOwned : Bool
    actionCompositionAndInverseExact : Bool
    orbitPresentationInhabited : Bool
    actualOrbitTransportersInhabited : Bool
    orbitCountsOneTwoTwoFour : Bool
    orbitStabilizerCardinalityAuditOwned : Bool
    stabilizerPredicateExactSoundComplete : Bool
    stabilizerCosetResidualPresentationBuilt : Bool
    actualMonsterP2ArithmeticRecognitionBuilt : Bool

canonicalF4CurveKleinActionGroupoidBoundary :
  F4CurveKleinActionGroupoidBoundary
canonicalF4CurveKleinActionGroupoidBoundary =
  f4-curve-klein-action-groupoid-boundary
    true true true true true true true true false false
