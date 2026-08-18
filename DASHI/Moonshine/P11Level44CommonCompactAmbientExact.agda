module DASHI.Moonshine.P11Level44CommonCompactAmbientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- Journal of the Ramanujan Mathematical Society 17 (2002), 115--147.
--
-- Jean-Pierre Serre,
-- "Trees", Springer. DOI: 10.1007/978-3-642-61856-7.
--
-- Kimball Martin,
-- "The basis problem revisited", Trans. Amer. Math. Soc. 373 (2020),
-- 4523--4559. DOI: 10.1090/tran/8077.
--
-- EXECUTABLE FINITE CHECK
-- scripts/verify_p11_two_adic_local_averaging.py enumerates
--
--   B(Z/4) \ GL_2(Z/4)
--
-- as six compact cells.  In one deterministic ordering the right-orbit
-- partitions are
--
--   K(2):    {0,2}, {1,3}, {4,5}
--   K_0(4):  {0,1,2,3}, {4}, {5}.
--
-- DASHI CONTRIBUTION
--
-- Replace the misleading search for a canonical isomorphism between the two
-- three-dimensional fixed spaces by the source-faithful common-ambient object:
-- both are subspaces of functions on the SAME six compact cells.
--
-- Principal full-level-2 coordinates embed as
--
--   (x,y,z) |-> (x,y,x,y,z,z),
--
-- while Gamma_0(4) / Bruhat coordinates embed as
--
--   (w,l,r) |-> (w,w,w,w,l,r).
--
-- Their intersection is exactly two-dimensional:
--
--   (a,a,b) on the principal side
--       =
--   (a,b,b) on the Gamma_0(4) side.
--
-- This explains the rank-two compact averaging theorem structurally.  It does
-- NOT yet identify the noncompact GL_2(Q_2) action / Satake datum; all
-- unramified principal-series compact restrictions have the same basic K-side
-- shape, so the p11 local representation still requires its noncompact action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Old
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as Avg

------------------------------------------------------------------------
-- Six-cell common compact carrier.
------------------------------------------------------------------------

record Compact6 : Set where
  constructor compact6
  field
    c0 c1 c2 c3 c4 c5 : ℤ

open Compact6 public

compact6Ext :
  (u v : Compact6) →
  c0 u ≡ c0 v → c1 u ≡ c1 v → c2 u ≡ c2 v →
  c3 u ≡ c3 v → c4 u ≡ c4 v → c5 u ≡ c5 v →
  u ≡ v
compact6Ext
  (compact6 a0 a1 a2 a3 a4 a5)
  (compact6 b0 b1 b2 b3 b4 b5)
  refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- Principal K(2)-fixed embedding: constant on the three two-point orbits.
------------------------------------------------------------------------

principalCompactEmbed : Old.Old3 → Compact6
principalCompactEmbed v = compact6
  (Old.x1 v) (Old.x2 v) (Old.x1 v) (Old.x2 v) (Old.x4 v) (Old.x4 v)

principalCompactEmbedInjective :
  (u v : Old.Old3) →
  principalCompactEmbed u ≡ principalCompactEmbed v →
  u ≡ v
principalCompactEmbedInjective
  (Old.old3 x y z) (Old.old3 a b c) equality
  with cong c0 equality | cong c1 equality | cong c4 equality
... | refl | refl | refl = refl

------------------------------------------------------------------------
-- Gamma_0(4)-fixed / Bruhat embedding: constant on the 4+1+1 partition.
------------------------------------------------------------------------

gammaCompactEmbed : Avg.Bruhat3 → Compact6
gammaCompactEmbed v = compact6
  (Avg.wide v) (Avg.wide v) (Avg.wide v) (Avg.wide v)
  (Avg.left v) (Avg.right v)

gammaCompactEmbedInjective :
  (u v : Avg.Bruhat3) →
  gammaCompactEmbed u ≡ gammaCompactEmbed v →
  u ≡ v
gammaCompactEmbedInjective
  (Avg.bruhat3 w l r) (Avg.bruhat3 a b c) equality
  with cong c0 equality | cong c4 equality | cong c5 equality
... | refl | refl | refl = refl

------------------------------------------------------------------------
-- Exact common intersection: two free coordinates a,b.
------------------------------------------------------------------------

record Intersection2 : Set where
  constructor intersection2
  field
    sharedWide sharedTerminal : ℤ

open Intersection2 public

intersectionPrincipal : Intersection2 → Old.Old3
intersectionPrincipal q = Old.old3
  (sharedWide q) (sharedWide q) (sharedTerminal q)

intersectionGamma : Intersection2 → Avg.Bruhat3
intersectionGamma q = Avg.bruhat3
  (sharedWide q) (sharedTerminal q) (sharedTerminal q)

intersectionEmbeddingsAgree :
  (q : Intersection2) →
  principalCompactEmbed (intersectionPrincipal q)
  ≡ gammaCompactEmbed (intersectionGamma q)
intersectionEmbeddingsAgree (intersection2 a b) = refl

------------------------------------------------------------------------
-- Any actual equality of the two ambient embeddings forces exactly the two
-- intersection equations x1=x2 and left=right, plus the common coordinates.
------------------------------------------------------------------------

sameAmbientForcesPrincipalFirstTwoEqual :
  (p : Old.Old3) → (g : Avg.Bruhat3) →
  principalCompactEmbed p ≡ gammaCompactEmbed g →
  Old.x1 p ≡ Old.x2 p
sameAmbientForcesPrincipalFirstTwoEqual p g equality =
  trans
    (cong c0 equality)
    (sym (cong c1 equality))

sameAmbientForcesGammaTerminalEqual :
  (p : Old.Old3) → (g : Avg.Bruhat3) →
  principalCompactEmbed p ≡ gammaCompactEmbed g →
  Avg.left g ≡ Avg.right g
sameAmbientForcesGammaTerminalEqual p g equality =
  trans
    (sym (cong c4 equality))
    (cong c5 equality)

sameAmbientIdentifiesWide :
  (p : Old.Old3) → (g : Avg.Bruhat3) →
  principalCompactEmbed p ≡ gammaCompactEmbed g →
  Old.x1 p ≡ Avg.wide g
sameAmbientIdentifiesWide p g equality = cong c0 equality

sameAmbientIdentifiesTerminal :
  (p : Old.Old3) → (g : Avg.Bruhat3) →
  principalCompactEmbed p ≡ gammaCompactEmbed g →
  Old.x4 p ≡ Avg.left g
sameAmbientIdentifiesTerminal p g equality = cong c4 equality

------------------------------------------------------------------------
-- Reconstruct the unique two-coordinate intersection witness from any ambient
-- equality.  This is the exact intersection theorem, not only a dimension
-- comment.
------------------------------------------------------------------------

record AmbientIntersectionWitness (p : Old.Old3) (g : Avg.Bruhat3) : Set where
  field
    coordinates : Intersection2
    principalExact : intersectionPrincipal coordinates ≡ p
    gammaExact : intersectionGamma coordinates ≡ g

open AmbientIntersectionWitness public

sameAmbientHasIntersectionWitness :
  (p : Old.Old3) → (g : Avg.Bruhat3) →
  principalCompactEmbed p ≡ gammaCompactEmbed g →
  AmbientIntersectionWitness p g
sameAmbientHasIntersectionWitness
  p@(Old.old3 x y z) g@(Avg.bruhat3 w l r) equality
  with cong c0 equality | cong c1 equality | cong c4 equality | cong c5 equality
... | x=w | y=w | z=l | z=r = record
  { coordinates = intersection2 x z
  ; principalExact =
      let y=x : y ≡ x
          y=x = trans y=w (sym x=w)
      in
      cong (λ q → Old.old3 x q z) (sym y=x)
  ; gammaExact =
      let w=x : w ≡ x
          w=x = sym x=w
          l=z : l ≡ z
          l=z = sym z=l
          r=z : r ≡ z
          r=z = sym z=r
      in
      trans
        (cong (λ q → Avg.bruhat3 q z z) (sym w=x))
        (trans
          (cong (λ q → Avg.bruhat3 w q z) (sym l=z))
          (cong (Avg.bruhat3 w l) (sym r=z)))
  }

------------------------------------------------------------------------
-- The denominator-cleared compact average lands exactly in the Gamma-side
-- intersection condition left=right, explaining its rank-two image.
------------------------------------------------------------------------

clearedAverageTerminalCoordinatesEqual :
  (v : Old.Old3) →
  Avg.left (Avg.clearedCompactAverage v)
  ≡ Avg.right (Avg.clearedCompactAverage v)
clearedAverageTerminalCoordinatesEqual v = refl

record P11Level44CommonCompactAmbientBoundary : Set where
  field
    sixCellAmbientConstructed : Bool
    principalThreeOrbitEmbeddingConstructed : Bool
    gammaFourOneOneEmbeddingConstructed : Bool
    bothEmbeddingsInjective : Bool
    exactTwoCoordinateIntersectionConstructed : Bool
    compactAveragingImageLiesInIntersectionCondition : Bool
    canonicalIsomorphismBetweenFixedSpacesRequired : Bool
    commonAmbientEqualsFullLocalRepresentation : Bool
    noncompactSatakeActionStillRequired : Bool

canonicalP11Level44CommonCompactAmbientBoundary :
  P11Level44CommonCompactAmbientBoundary
canonicalP11Level44CommonCompactAmbientBoundary = record
  { sixCellAmbientConstructed = true
  ; principalThreeOrbitEmbeddingConstructed = true
  ; gammaFourOneOneEmbeddingConstructed = true
  ; bothEmbeddingsInjective = true
  ; exactTwoCoordinateIntersectionConstructed = true
  ; compactAveragingImageLiesInIntersectionCondition = true
  ; canonicalIsomorphismBetweenFixedSpacesRequired = false
  ; commonAmbientEqualsFullLocalRepresentation = false
  ; noncompactSatakeActionStillRequired = true
  }
