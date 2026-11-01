module DASHI.Moonshine.OggSSPP2F4CurveShearReflectionExact where

------------------------------------------------------------------------
-- p=2 / F4: an ACTUAL curve-coordinate S3 action.
--
-- On E : y²+y=x³ over F4 with zeta³=1, define
--   rho(x,y) = (zeta*x,y),     F(x,y) = (x²,y²).
--
-- This file works on the ALREADY CONSTRUCTED exact nine-point rational
-- curve carrier, NOT an ad-hoc nine-label surrogate. We prove exhaustively
--
--   rho³ = id, F² = id, F rho F = rho⁻¹,
--
-- and compute the fixed points, C3 orbits and joint S3 orbits.
--
-- The resulting action has 3 singleton S3 orbits and one six-element orbit.
-- This is a genuine FINITE CURVE POINT SET action, not yet a theorem that
-- rho and Frobenius are endomorphisms of the ACTUAL elliptic AddCommGroup.
-- In particular it does not identify the S3 action with a VOA action,
-- a Monster residual valuation, or Gamma0(4) level structure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

open Curve using (RationalF4Point; AffineF4Point)

-- Multiplication of the first coordinate by the literal F4 cube root.
rhoAffine : AffineF4Point → AffineF4Point
rhoAffine Curve.p00 = Curve.p00
rhoAffine Curve.p01 = Curve.p01
rhoAffine Curve.p1Zeta = Curve.pZetaZeta
rhoAffine Curve.p1ZetaSquared = Curve.pZetaZetaSquared
rhoAffine Curve.pZetaZeta = Curve.pZetaSquaredZeta
rhoAffine Curve.pZetaZetaSquared = Curve.pZetaSquaredZetaSquared
rhoAffine Curve.pZetaSquaredZeta = Curve.p1Zeta
rhoAffine Curve.pZetaSquaredZetaSquared = Curve.p1ZetaSquared

rho : RationalF4Point → RationalF4Point
rho Curve.infinity = Curve.infinity
rho (Curve.affine p) = Curve.affine (rhoAffine p)

rhoTwice : RationalF4Point → RationalF4Point
rhoTwice p = rho (rho p)

rhoThree :
  (p : RationalF4Point) →
  rho (rhoTwice p) ≡ p
rhoThree Curve.infinity = refl
rhoThree (Curve.affine Curve.p00) = refl
rhoThree (Curve.affine Curve.p01) = refl
rhoThree (Curve.affine Curve.p1Zeta) = refl
rhoThree (Curve.affine Curve.p1ZetaSquared) = refl
rhoThree (Curve.affine Curve.pZetaZeta) = refl
rhoThree (Curve.affine Curve.pZetaZetaSquared) = refl
rhoThree (Curve.affine Curve.pZetaSquaredZeta) = refl
rhoThree (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- These clauses check that the permutation is really the coordinate map
-- (x,y) ↦ (zeta*x,y) on ALL eight affine rational points.
rhoAffineCoordinates :
  (p : AffineF4Point) →
  Curve.affineCoordinates (rhoAffine p)
  ≡
  ((Curve.zeta₄ Curve.*₄
    (proj₁ (Curve.affineCoordinates p))) ,
  (proj₂ (Curve.affineCoordinates p)))
rhoAffineCoordinates Curve.p00 = refl
rhoAffineCoordinates Curve.p01 = refl
rhoAffineCoordinates Curve.p1Zeta = refl
rhoAffineCoordinates Curve.p1ZetaSquared = refl
rhoAffineCoordinates Curve.pZetaZeta = refl
rhoAffineCoordinates Curve.pZetaZetaSquared = refl
rhoAffineCoordinates Curve.pZetaSquaredZeta = refl
rhoAffineCoordinates Curve.pZetaSquaredZetaSquared = refl

frobenius : RationalF4Point → RationalF4Point
frobenius = Curve.frobeniusRational

frobeniusInvolution :
  (p : RationalF4Point) →
  frobenius (frobenius p) ≡ p
frobeniusInvolution = Curve.frobeniusRationalInvolutive

-- Characteristic-two descent conjugates the cube-root shear to its inverse.
frobeniusConjugatesRho :
  (p : RationalF4Point) →
  frobenius (rho (frobenius p)) ≡ rhoTwice p
frobeniusConjugatesRho Curve.infinity = refl
frobeniusConjugatesRho (Curve.affine Curve.p00) = refl
frobeniusConjugatesRho (Curve.affine Curve.p01) = refl
frobeniusConjugatesRho (Curve.affine Curve.p1Zeta) = refl
frobeniusConjugatesRho (Curve.affine Curve.p1ZetaSquared) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaZeta) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaZetaSquared) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaSquaredZeta) = refl
frobeniusConjugatesRho (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- Exact C3 orbit types: three fixed points and two triples.
data RhoOrbit : Set where
  infinityFixed : RhoOrbit
  zeroZeroFixed : RhoOrbit
  zeroOneFixed : RhoOrbit
  zetaYTriple : RhoOrbit
  zetaSquaredYTriple : RhoOrbit

rhoOrbit : RationalF4Point → RhoOrbit
rhoOrbit Curve.infinity = infinityFixed
rhoOrbit (Curve.affine Curve.p00) = zeroZeroFixed
rhoOrbit (Curve.affine Curve.p01) = zeroOneFixed
rhoOrbit (Curve.affine Curve.p1Zeta) = zetaYTriple
rhoOrbit (Curve.affine Curve.p1ZetaSquared) = zetaSquaredYTriple
rhoOrbit (Curve.affine Curve.pZetaZeta) = zetaYTriple
rhoOrbit (Curve.affine Curve.pZetaZetaSquared) = zetaSquaredYTriple
rhoOrbit (Curve.affine Curve.pZetaSquaredZeta) = zetaYTriple
rhoOrbit (Curve.affine Curve.pZetaSquaredZetaSquared) = zetaSquaredYTriple

rhoOrbitInvariant :
  (p : RationalF4Point) →
  rhoOrbit (rho p) ≡ rhoOrbit p
rhoOrbitInvariant Curve.infinity = refl
rhoOrbitInvariant (Curve.affine Curve.p00) = refl
rhoOrbitInvariant (Curve.affine Curve.p01) = refl
rhoOrbitInvariant (Curve.affine Curve.p1Zeta) = refl
rhoOrbitInvariant (Curve.affine Curve.p1ZetaSquared) = refl
rhoOrbitInvariant (Curve.affine Curve.pZetaZeta) = refl
rhoOrbitInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
rhoOrbitInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
rhoOrbitInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

rhoOrbitCount : Nat
rhoOrbitCount = 5

rhoOrbitPartition : 3 + 2 * 3 ≡ Curve.rationalCount
rhoOrbitPartition = refl

-- Adding Frobenius merges the two rho-triples and fixes all three
-- x=0 / infinity elements individually.
data ShearReflectionOrbit : Set where
  infinityFixed : ShearReflectionOrbit
  zeroZeroFixed : ShearReflectionOrbit
  zeroOneFixed : ShearReflectionOrbit
  sixNonzeroX : ShearReflectionOrbit

jointOrbit : RationalF4Point → ShearReflectionOrbit
jointOrbit Curve.infinity = infinityFixed
jointOrbit (Curve.affine Curve.p00) = zeroZeroFixed
jointOrbit (Curve.affine Curve.p01) = zeroOneFixed
jointOrbit (Curve.affine Curve.p1Zeta) = sixNonzeroX
jointOrbit (Curve.affine Curve.p1ZetaSquared) = sixNonzeroX
jointOrbit (Curve.affine Curve.pZetaZeta) = sixNonzeroX
jointOrbit (Curve.affine Curve.pZetaZetaSquared) = sixNonzeroX
jointOrbit (Curve.affine Curve.pZetaSquaredZeta) = sixNonzeroX
jointOrbit (Curve.affine Curve.pZetaSquaredZetaSquared) = sixNonzeroX

jointOrbitRhoInvariant :
  (p : RationalF4Point) →
  jointOrbit (rho p) ≡ jointOrbit p
jointOrbitRhoInvariant Curve.infinity = refl
jointOrbitRhoInvariant (Curve.affine Curve.p00) = refl
jointOrbitRhoInvariant (Curve.affine Curve.p01) = refl
jointOrbitRhoInvariant (Curve.affine Curve.p1Zeta) = refl
jointOrbitRhoInvariant (Curve.affine Curve.p1ZetaSquared) = refl
jointOrbitRhoInvariant (Curve.affine Curve.pZetaZeta) = refl
jointOrbitRhoInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
jointOrbitRhoInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
jointOrbitRhoInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

jointOrbitFrobeniusInvariant :
  (p : RationalF4Point) →
  jointOrbit (frobenius p) ≡ jointOrbit p
jointOrbitFrobeniusInvariant Curve.infinity = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.p00) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.p01) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.p1Zeta) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.p1ZetaSquared) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.pZetaZeta) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
jointOrbitFrobeniusInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

jointOrbitCount : Nat
jointOrbitCount = 4

jointOrbitPartition : 1 + 1 + 1 + 6 ≡ Curve.rationalCount
jointOrbitPartition = refl

------------------------------------------------------------------------
-- The C3 and S3 orbit labels are backed by LITERAL REACHABILITY terms,
-- not merely invariant quotient maps.
------------------------------------------------------------------------

data RhoStep : Set where
  stepZero : RhoStep
  stepOne : RhoStep
  stepTwo : RhoStep

rhoStep : RhoStep → RationalF4Point → RationalF4Point
rhoStep stepZero p = p
rhoStep stepOne p = rho p
rhoStep stepTwo p = rhoTwice p

applyFrobenius : Bool → RationalF4Point → RationalF4Point
applyFrobenius false p = p
applyFrobenius true p = frobenius p

jointAct : Bool → RhoStep → RationalF4Point → RationalF4Point
jointAct f k p = rhoStep k (applyFrobenius f p)

jointRepresentative : ShearReflectionOrbit → RationalF4Point
jointRepresentative infinityFixed = Curve.infinity
jointRepresentative zeroZeroFixed = Curve.affine Curve.p00
jointRepresentative zeroOneFixed = Curve.affine Curve.p01
jointRepresentative sixNonzeroX = Curve.affine Curve.p1Zeta

jointRepresentativeHasLabel :
  (orbit : ShearReflectionOrbit) →
  jointOrbit (jointRepresentative orbit) ≡ orbit
jointRepresentativeHasLabel infinityFixed = refl
jointRepresentativeHasLabel zeroZeroFixed = refl
jointRepresentativeHasLabel zeroOneFixed = refl
jointRepresentativeHasLabel sixNonzeroX = refl

jointReachFlags : RationalF4Point → Bool × RhoStep
jointReachFlags Curve.infinity = false , stepZero
jointReachFlags (Curve.affine Curve.p00) = false , stepZero
jointReachFlags (Curve.affine Curve.p01) = false , stepZero
jointReachFlags (Curve.affine Curve.p1Zeta) = false , stepZero
jointReachFlags (Curve.affine Curve.p1ZetaSquared) = true , stepZero
jointReachFlags (Curve.affine Curve.pZetaZeta) = false , stepOne
jointReachFlags (Curve.affine Curve.pZetaZetaSquared) = true , stepOne
jointReachFlags (Curve.affine Curve.pZetaSquaredZeta) = false , stepTwo
jointReachFlags (Curve.affine Curve.pZetaSquaredZetaSquared) = true , stepTwo

jointReachEveryPoint :
  (p : RationalF4Point) →
  jointAct
    (proj₁ (jointReachFlags p))
    (proj₂ (jointReachFlags p))
    (jointRepresentative (jointOrbit p))
  ≡ p
jointReachEveryPoint Curve.infinity = refl
jointReachEveryPoint (Curve.affine Curve.p00) = refl
jointReachEveryPoint (Curve.affine Curve.p01) = refl
jointReachEveryPoint (Curve.affine Curve.p1Zeta) = refl
jointReachEveryPoint (Curve.affine Curve.p1ZetaSquared) = refl
jointReachEveryPoint (Curve.affine Curve.pZetaZeta) = refl
jointReachEveryPoint (Curve.affine Curve.pZetaZetaSquared) = refl
jointReachEveryPoint (Curve.affine Curve.pZetaSquaredZeta) = refl
jointReachEveryPoint (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- A logically meaningful no-free-action obstruction: one witness exists.
-- Unlike an empty "NoGo" datatype, this accepts the actual free-action
-- proposition as input and derives contradiction using the fixed infinity.
rhoCannotActFreely :
  ((p : RationalF4Point) → rho p ≡ p → ⊥) → ⊥
rhoCannotActFreely h = h Curve.infinity refl

-- The three fixed elements are literal witnesses, not a numerical claim.
rhoFixesInfinity : rho Curve.infinity ≡ Curve.infinity
rhoFixesInfinity = refl
rhoFixesZeroZero : rho (Curve.affine Curve.p00) ≡ Curve.affine Curve.p00
rhoFixesZeroZero = refl
rhoFixesZeroOne : rho (Curve.affine Curve.p01) ≡ Curve.affine Curve.p01
rhoFixesZeroOne = refl

-- Strict separation of the curve S3 set action from the unrelated
-- free output-phase C3 action on the 27-code carrier.
data CurveShearIsFreeOnAllNine : Set where
rhoHasFixedPointAndIsNotFree : CurveShearIsFreeOnAllNine → ⊥
rhoHasFixedPointAndIsNotFree ()

record Boundary : Set where
  constructor boundary
  field
    actualCurveCoordinateShear : Bool
    shearOrderThree : Bool
    frobeniusOrderTwo : Bool
    frobeniusConjugatesShearToInverse : Bool
    shearThreeFixedTwoTripleProfile : Bool
    jointThreeSingletonOneSixOrbitProfile : Bool
    jointOrbitsHaveExplicitReachabilityWitnesses : Bool
    ellipticAdditionPreservationProved : Bool
    literalVOAActionIdentified : Bool
    gamma0FourLevelStructureProved : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true true false false false
