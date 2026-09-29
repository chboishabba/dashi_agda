module DASHI.Moonshine.OggSSPP2F4CurveEigenbasisSheet9Exact where

------------------------------------------------------------------------
-- F4 CURVE <-> CENTERED C3^2 EIGENBASIS SHEET
--
-- The earlier origin-centred chart was chosen to expose Frobenius pairs.
-- It is a pointed C2-set bidi, but it is NOT the additive P,Q eigenbasis
-- chart: two mixed-sign states are exchanged.
--
-- This module installs the corrected finite chart suggested by the genuine
-- elliptic generators
--
--   P=(0,0), Q=(1,zeta),
--
-- with the intended coordinates
--
--   O              -> ( 0, 0)
--   P              -> (+1, 0)
--  -P              -> (-1, 0)
--   Q              -> ( 0,+1)
--  -Q              -> ( 0,-1)
--   P+Q            -> (+1,+1)
--  -(P+Q)          -> (-1,-1)
--   P-Q            -> (+1,-1)
--  -P+Q            -> (-1,+1).
--
-- On this exact chart:
--
--   elliptic coordinate negation -> (a,b) |-> (-a,-b)
--   Frobenius                    -> (a,b) |-> (a,-b)
--   rho(x,y)=(zeta*x,y)          -> (a,b) |-> (a+b,b).
--
-- The action intertwiners below are exhaustive finite proofs on the ACTUAL
-- F4 curve-point carrier.  The remaining missing theorem is that this chart
-- also intertwines the genuine elliptic addition. That theorem is being
-- discharged independently in Lean using Mathlib's actual point group.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveFrobeniusNegationOrbitExact as Klein
import DASHI.Moonshine.OggSSPP2F4CurveShearReflectionExact as CurveS3
import DASHI.Moonshine.OggSSPP2CenteredTernaryGroupExact as Group
import DASHI.Moonshine.OggSSPP2F4CurveOriginCenteredSheet9Exact as Old

open Codec using ([]ᵥ; _∷ᵥ_)

curveToBasisSheet : Curve.RationalF4Point → Codec.Sheet9
curveToBasisSheet Curve.infinity =
  Codec.sheet Trit.zer Trit.zer
curveToBasisSheet (Curve.affine Curve.p00) =
  Codec.sheet Trit.pos Trit.zer
curveToBasisSheet (Curve.affine Curve.p01) =
  Codec.sheet Trit.neg Trit.zer
curveToBasisSheet (Curve.affine Curve.p1Zeta) =
  Codec.sheet Trit.zer Trit.pos
curveToBasisSheet (Curve.affine Curve.p1ZetaSquared) =
  Codec.sheet Trit.zer Trit.neg
curveToBasisSheet (Curve.affine Curve.pZetaZeta) =
  Codec.sheet Trit.pos Trit.pos
curveToBasisSheet (Curve.affine Curve.pZetaZetaSquared) =
  Codec.sheet Trit.neg Trit.neg
curveToBasisSheet (Curve.affine Curve.pZetaSquaredZetaSquared) =
  Codec.sheet Trit.pos Trit.neg
curveToBasisSheet (Curve.affine Curve.pZetaSquaredZeta) =
  Codec.sheet Trit.neg Trit.pos

basisSheetToCurve : Codec.Sheet9 → Curve.RationalF4Point
basisSheetToCurve (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) =
  Curve.infinity
basisSheetToCurve (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) =
  Curve.affine Curve.p00
basisSheetToCurve (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) =
  Curve.affine Curve.p01
basisSheetToCurve (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) =
  Curve.affine Curve.p1Zeta
basisSheetToCurve (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) =
  Curve.affine Curve.p1ZetaSquared
basisSheetToCurve (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaZeta
basisSheetToCurve (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaZetaSquared
basisSheetToCurve (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaSquaredZetaSquared
basisSheetToCurve (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaSquaredZeta

curveBasisRoundTrip :
  (p : Curve.RationalF4Point) →
  basisSheetToCurve (curveToBasisSheet p) ≡ p
curveBasisRoundTrip Curve.infinity = refl
curveBasisRoundTrip (Curve.affine Curve.p00) = refl
curveBasisRoundTrip (Curve.affine Curve.p01) = refl
curveBasisRoundTrip (Curve.affine Curve.p1Zeta) = refl
curveBasisRoundTrip (Curve.affine Curve.p1ZetaSquared) = refl
curveBasisRoundTrip (Curve.affine Curve.pZetaZeta) = refl
curveBasisRoundTrip (Curve.affine Curve.pZetaZetaSquared) = refl
curveBasisRoundTrip (Curve.affine Curve.pZetaSquaredZeta) = refl
curveBasisRoundTrip (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

basisCurveRoundTrip :
  (s : Codec.Sheet9) →
  curveToBasisSheet (basisSheetToCurve s) ≡ s
basisCurveRoundTrip (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisCurveRoundTrip (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl

basisIdentityAtCenteredZero :
  curveToBasisSheet Curve.infinity ≡ Group.centerSheetZero
basisIdentityAtCenteredZero = refl

------------------------------------------------------------------------
-- Additive inverse / elliptic negation.
------------------------------------------------------------------------

basisNegationIntertwining :
  (p : Curve.RationalF4Point) →
  curveToBasisSheet (Klein.negateRational p)
  ≡ Group.centerSheetNeg (curveToBasisSheet p)
basisNegationIntertwining Curve.infinity = refl
basisNegationIntertwining (Curve.affine Curve.p00) = refl
basisNegationIntertwining (Curve.affine Curve.p01) = refl
basisNegationIntertwining (Curve.affine Curve.p1Zeta) = refl
basisNegationIntertwining (Curve.affine Curve.p1ZetaSquared) = refl
basisNegationIntertwining (Curve.affine Curve.pZetaZeta) = refl
basisNegationIntertwining (Curve.affine Curve.pZetaZetaSquared) = refl
basisNegationIntertwining (Curve.affine Curve.pZetaSquaredZeta) = refl
basisNegationIntertwining (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

------------------------------------------------------------------------
-- Frobenius matrix diag(1,-1).
------------------------------------------------------------------------

basisFrobenius : Codec.Sheet9 → Codec.Sheet9
basisFrobenius (a ∷ᵥ b ∷ᵥ []ᵥ) =
  Codec.sheet a (Trit.inv b)

basisFrobeniusIntertwining :
  (p : Curve.RationalF4Point) →
  curveToBasisSheet (Curve.frobeniusRational p)
  ≡ basisFrobenius (curveToBasisSheet p)
basisFrobeniusIntertwining Curve.infinity = refl
basisFrobeniusIntertwining (Curve.affine Curve.p00) = refl
basisFrobeniusIntertwining (Curve.affine Curve.p01) = refl
basisFrobeniusIntertwining (Curve.affine Curve.p1Zeta) = refl
basisFrobeniusIntertwining (Curve.affine Curve.p1ZetaSquared) = refl
basisFrobeniusIntertwining (Curve.affine Curve.pZetaZeta) = refl
basisFrobeniusIntertwining (Curve.affine Curve.pZetaZetaSquared) = refl
basisFrobeniusIntertwining (Curve.affine Curve.pZetaSquaredZeta) = refl
basisFrobeniusIntertwining (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

basisFrobeniusInvolutive :
  (s : Codec.Sheet9) →
  basisFrobenius (basisFrobenius s) ≡ s
basisFrobeniusInvolutive (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite Trit.inv-invol b = refl

------------------------------------------------------------------------
-- rho matrix [[1,1],[0,1]]: (a,b) |-> (a+b,b).
------------------------------------------------------------------------

basisShear : Codec.Sheet9 → Codec.Sheet9
basisShear (a ∷ᵥ b ∷ᵥ []ᵥ) =
  Codec.sheet (Group.centerAdd a b) b

basisShearIntertwining :
  (p : Curve.RationalF4Point) →
  curveToBasisSheet (CurveS3.rho p)
  ≡ basisShear (curveToBasisSheet p)
basisShearIntertwining Curve.infinity = refl
basisShearIntertwining (Curve.affine Curve.p00) = refl
basisShearIntertwining (Curve.affine Curve.p01) = refl
basisShearIntertwining (Curve.affine Curve.p1Zeta) = refl
basisShearIntertwining (Curve.affine Curve.p1ZetaSquared) = refl
basisShearIntertwining (Curve.affine Curve.pZetaZeta) = refl
basisShearIntertwining (Curve.affine Curve.pZetaZetaSquared) = refl
basisShearIntertwining (Curve.affine Curve.pZetaSquaredZeta) = refl
basisShearIntertwining (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

basisShearTwice : Codec.Sheet9 → Codec.Sheet9
basisShearTwice s = basisShear (basisShear s)

basisShearThree :
  (s : Codec.Sheet9) →
  basisShear (basisShearTwice s) ≡ s
basisShearThree (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisShearThree (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl

basisFrobeniusConjugatesShear :
  (s : Codec.Sheet9) →
  basisFrobenius (basisShear (basisFrobenius s))
  ≡ basisShearTwice s
basisFrobeniusConjugatesShear
  (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
basisFrobeniusConjugatesShear
  (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl

------------------------------------------------------------------------
-- The two matrices are actual endomorphisms of the CENTERED C3^2 law.
------------------------------------------------------------------------

basisFrobeniusPreservesAddition :
  (s t : Codec.Sheet9) →
  basisFrobenius (Group.centerSheetAdd s t)
  ≡ Group.centerSheetAdd (basisFrobenius s) (basisFrobenius t)
basisFrobeniusPreservesAddition
  (a ∷ᵥ b ∷ᵥ []ᵥ)
  (c ∷ᵥ d ∷ᵥ []ᵥ)
  rewrite Group.centerInvAdd b d = refl

basisShearPreservesAddition :
  (s t : Codec.Sheet9) →
  basisShear (Group.centerSheetAdd s t)
  ≡ Group.centerSheetAdd (basisShear s) (basisShear t)
basisShearPreservesAddition
  (a ∷ᵥ b ∷ᵥ []ᵥ)
  (c ∷ᵥ d ∷ᵥ []ᵥ)
  rewrite sym (Group.centerAdd-medial a b c d) = refl

basisFrobeniusPreservesZero :
  basisFrobenius Group.centerSheetZero ≡ Group.centerSheetZero
basisFrobeniusPreservesZero = refl

basisShearPreservesZero :
  basisShear Group.centerSheetZero ≡ Group.centerSheetZero
basisShearPreservesZero = refl

------------------------------------------------------------------------
-- The OLD pointed Frobenius chart is not this additive eigenbasis chart.
------------------------------------------------------------------------

oldAndBasisDifferAtMixedSign :
  Old.centeredCurveToSheet
    (Curve.affine Curve.pZetaZetaSquared)
  ≡
  curveToBasisSheet
    (Curve.affine Curve.pZetaZetaSquared)
  → ⊥
oldAndBasisDifferAtMixedSign ()

oldAndBasisDifferAtOtherMixedSign :
  Old.centeredCurveToSheet
    (Curve.affine Curve.pZetaSquaredZeta)
  ≡
  curveToBasisSheet
    (Curve.affine Curve.pZetaSquaredZeta)
  → ⊥
oldAndBasisDifferAtOtherMixedSign ()

record Boundary : Set where
  constructor boundary
  field
    exactNinePointBidi : Bool
    ellipticIdentityAtCenteredZero : Bool
    coordinateNegationIsGroupInverseShape : Bool
    frobeniusDiagonalReflection : Bool
    zetaShearMatrixShape : Bool
    s3PresentationPaidOnActualCurveSet : Bool
    centeredGroupEndomorphismMatricesPaid : Bool
    oldPointedChartDistinguishedFromEigenbasis : Bool
    ellipticAdditionIntertwinerPaid : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true true true false
