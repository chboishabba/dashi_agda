module DASHI.Physics.CondensedMatter.HexagonalSqrt3R30ReciprocalFoldingExact where

------------------------------------------------------------------------
-- EXACT HEXAGONAL sqrt(3) x sqrt(3) R30 SUPERLATTICE CERTIFICATE
--
-- Conventional primitive hexagonal basis:
--   a1, a2 with equal norm and mutual angle 60 degrees.
--
-- Selected real-space supercell:
--   A1 =  a1 + a2
--   A2 = -a1 + 2 a2
--
-- Integer column matrix:
--
--        [ 1  -1 ]
--   M =  [ 1   2 ]
--
-- det M = 3.
--
-- The reciprocal numerator matrix
--
--        [ 2  -1 ]
--   N =  [ 1   1 ]
--
-- satisfies M^T N = 3 I.  Thus (1/3)N is the reciprocal-basis
-- transformation.  All identities below are exact integer identities.
--
-- The sqrt(3) and R30 labels are represented by algebraic metric certificates
-- in the hexagonal Gram form, not by machine floating point or a transcendental
-- trigonometric approximation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; -[1+_]; -_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

------------------------------------------------------------------------
-- Integer vector/matrix core.
------------------------------------------------------------------------

record Z2 : Set where
  constructor z2
  field
    x : ℤ
    y : ℤ

open Z2 public

zeroℤ : ℤ
zeroℤ = + 0

oneℤ : ℤ
oneℤ = + 1

twoℤ : ℤ
twoℤ = + 2

threeℤ : ℤ
threeℤ = + 3

sixℤ : ℤ
sixℤ = + 6

minusOneℤ : ℤ
minusOneℤ = -[1+ 0 ]

_−ℤ_ : ℤ → ℤ → ℤ
left −ℤ right = left +ℤ (- right)

primitiveA1 primitiveA2 : Z2
primitiveA1 = z2 oneℤ zeroℤ
primitiveA2 = z2 zeroℤ oneℤ

superA1 superA2 : Z2
superA1 = z2 oneℤ oneℤ
superA2 = z2 minusOneℤ twoℤ

reciprocalNumeratorB1 reciprocalNumeratorB2 : Z2
reciprocalNumeratorB1 = z2 twoℤ oneℤ
reciprocalNumeratorB2 = z2 minusOneℤ oneℤ

det2 : Z2 → Z2 → ℤ
det2 left right =
  (x left *ℤ y right) −ℤ (y left *ℤ x right)

supercellDeterminantIsThree :
  det2 superA1 superA2 ≡ threeℤ
supercellDeterminantIsThree = refl

primitiveToSuperA1PositiveOrientation :
  det2 primitiveA1 superA1 ≡ oneℤ
primitiveToSuperA1PositiveOrientation = refl

------------------------------------------------------------------------
-- Hexagonal metric.
--
-- We scale the primitive squared norm to 2 so the Gram matrix is integral:
--
--       [ 2  1 ]
--   G = [ 1  2 ].
--
-- This is the exact equal-length / 60-degree hexagonal metric.
------------------------------------------------------------------------

hexDot : Z2 → Z2 → ℤ
hexDot left right =
  ((twoℤ *ℤ x left) *ℤ x right)
  +ℤ ((x left *ℤ y right)
  +ℤ ((y left *ℤ x right)
  +ℤ ((twoℤ *ℤ y left) *ℤ y right)))

hexNormSq : Z2 → ℤ
hexNormSq value = hexDot value value

primitiveA1NormSqIsTwo :
  hexNormSq primitiveA1 ≡ twoℤ
primitiveA1NormSqIsTwo = refl

primitiveA2NormSqIsTwo :
  hexNormSq primitiveA2 ≡ twoℤ
primitiveA2NormSqIsTwo = refl

primitiveDotIsOne :
  hexDot primitiveA1 primitiveA2 ≡ oneℤ
primitiveDotIsOne = refl

superA1NormSqIsSix :
  hexNormSq superA1 ≡ sixℤ
superA1NormSqIsSix = refl

superA2NormSqIsSix :
  hexNormSq superA2 ≡ sixℤ
superA2NormSqIsSix = refl

superDotIsThree :
  hexDot superA1 superA2 ≡ threeℤ
superDotIsThree = refl

-- Equal supercell norms and 2<A1,A2> = ||A1||^2 encode cos(60)=1/2.
supercellSixtyDegreeMetricCertificate :
  (twoℤ *ℤ hexDot superA1 superA2)
  ≡ hexNormSq superA1
supercellSixtyDegreeMetricCertificate = refl

-- ||A1||^2 = 3 ||a1||^2 encodes the sqrt(3) real-space scale.
supercellSqrt3ScaleCertificate :
  hexNormSq superA1 ≡ threeℤ *ℤ hexNormSq primitiveA1
supercellSqrt3ScaleCertificate = refl

-- <a1,A1> = 3 in this normalization.  Together with
-- ||a1||^2 = 2 and ||A1||^2 = 6,
--
--   4 <a1,A1>^2 = 3 ||a1||^2 ||A1||^2,
--
-- i.e. cos^2(theta)=3/4.  The positive dot and positive determinant above
-- select the +30-degree branch in the conventional oriented hexagonal basis.
primitiveA1DotSuperA1IsThree :
  hexDot primitiveA1 superA1 ≡ threeℤ
primitiveA1DotSuperA1IsThree = refl

r30MetricSquareCertificate :
  (+ 4) *ℤ
    (hexDot primitiveA1 superA1 *ℤ hexDot primitiveA1 superA1)
  ≡
  threeℤ *ℤ
    (hexNormSq primitiveA1 *ℤ hexNormSq superA1)
r30MetricSquareCertificate = refl

------------------------------------------------------------------------
-- Exact reciprocal transform certificate.
--
-- M has columns superA1/superA2.
-- N has columns reciprocalNumeratorB1/reciprocalNumeratorB2.
--
-- M^T N = 3 I means that B_i = N_i / 3 are dual to the supercell basis
-- when the original reciprocal basis is dual to a_i.
------------------------------------------------------------------------

dotCoordinates : Z2 → Z2 → ℤ
dotCoordinates left right =
  (x left *ℤ x right) +ℤ (y left *ℤ y right)

mtN11IsThree :
  dotCoordinates superA1 reciprocalNumeratorB1 ≡ threeℤ
mtN11IsThree = refl

mtN12IsZero :
  dotCoordinates superA1 reciprocalNumeratorB2 ≡ zeroℤ
mtN12IsZero = refl

mtN21IsZero :
  dotCoordinates superA2 reciprocalNumeratorB1 ≡ zeroℤ
mtN21IsZero = refl

mtN22IsThree :
  dotCoordinates superA2 reciprocalNumeratorB2 ≡ threeℤ
mtN22IsThree = refl

record ReciprocalTransformCertificate : Set where
  constructor reciprocal-transform-certificate
  field
    m11 m12 m21 m22 : ℤ
    n11 n12 n21 n22 : ℤ
    mtN11 : (m11 *ℤ n11) +ℤ (m21 *ℤ n21) ≡ threeℤ
    mtN12 : (m11 *ℤ n12) +ℤ (m21 *ℤ n22) ≡ zeroℤ
    mtN21 : (m12 *ℤ n11) +ℤ (m22 *ℤ n21) ≡ zeroℤ
    mtN22 : (m12 *ℤ n12) +ℤ (m22 *ℤ n22) ≡ threeℤ

canonicalReciprocalTransformCertificate : ReciprocalTransformCertificate
canonicalReciprocalTransformCertificate =
  reciprocal-transform-certificate
    oneℤ minusOneℤ oneℤ twoℤ
    twoℤ minusOneℤ oneℤ oneℤ
    refl refl refl refl

------------------------------------------------------------------------
-- Exact C3 folding class on the 3 x 3 primitive-coordinate torus.
--
-- q(x,y)=x-y mod 3.  Both supercell translations preserve q:
--   A1 = (+1,+1)
--   A2 = (-1,+2) = (-1,-1) mod 3.
--
-- Hence the nine primitive residue positions split into three folding
-- classes, the finite shadow of Z^2 / M Z^2 ~= C3.
------------------------------------------------------------------------

previous3 : Torus.Residue3 → Torus.Residue3
previous3 Torus.residueMinus = Torus.residuePlus
previous3 Torus.residueZero = Torus.residueMinus
previous3 Torus.residuePlus = Torus.residueZero

difference3 : Torus.Residue3 → Torus.Residue3 → Torus.Residue3
difference3 Torus.residueMinus Torus.residueMinus = Torus.residueZero
difference3 Torus.residueMinus Torus.residueZero = Torus.residueMinus
difference3 Torus.residueMinus Torus.residuePlus = Torus.residuePlus
difference3 Torus.residueZero Torus.residueMinus = Torus.residuePlus
difference3 Torus.residueZero Torus.residueZero = Torus.residueZero
difference3 Torus.residueZero Torus.residuePlus = Torus.residueMinus
difference3 Torus.residuePlus Torus.residueMinus = Torus.residueMinus
difference3 Torus.residuePlus Torus.residueZero = Torus.residuePlus
difference3 Torus.residuePlus Torus.residuePlus = Torus.residueZero

foldClass : Torus.Torus3x3 → Torus.Residue3
foldClass point =
  difference3
    (Torus.firstCoordinate point)
    (Torus.secondCoordinate point)

translateSuperA1 : Torus.Torus3x3 → Torus.Torus3x3
translateSuperA1 point =
  Torus.translateFirst (Torus.translateSecond point)

translateSuperA2 : Torus.Torus3x3 → Torus.Torus3x3
translateSuperA2 (Torus.torusPoint first second) =
  Torus.torusPoint (previous3 first) (previous3 second)

foldClassInvariantUnderSuperA1 :
  (point : Torus.Torus3x3) →
  foldClass (translateSuperA1 point) ≡ foldClass point
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
foldClassInvariantUnderSuperA1
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl

foldClassInvariantUnderSuperA2 :
  (point : Torus.Torus3x3) →
  foldClass (translateSuperA2 point) ≡ foldClass point
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
foldClassInvariantUnderSuperA2
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl

foldRepresentativeMinus foldRepresentativeZero foldRepresentativePlus :
  Torus.Torus3x3
foldRepresentativeMinus =
  Torus.torusPoint Torus.residueMinus Torus.residueZero
foldRepresentativeZero =
  Torus.torusPoint Torus.residueZero Torus.residueZero
foldRepresentativePlus =
  Torus.torusPoint Torus.residuePlus Torus.residueZero

foldRepresentativeMinusClass :
  foldClass foldRepresentativeMinus ≡ Torus.residueMinus
foldRepresentativeMinusClass = refl

foldRepresentativeZeroClass :
  foldClass foldRepresentativeZero ≡ Torus.residueZero
foldRepresentativeZeroClass = refl

foldRepresentativePlusClass :
  foldClass foldRepresentativePlus ≡ Torus.residuePlus
foldRepresentativePlusClass = refl

minusNotZero : Torus.residueMinus ≡ Torus.residueZero → ⊥
minusNotZero ()

minusNotPlus : Torus.residueMinus ≡ Torus.residuePlus → ⊥
minusNotPlus ()

zeroNotPlus : Torus.residueZero ≡ Torus.residuePlus → ⊥
zeroNotPlus ()

record Sqrt3R30ExactBoundary : Set where
  constructor sqrt3-r30-exact-boundary
  field
    determinantThreeProved : Bool
    sqrt3MetricScaleProved : Bool
    r30AlgebraicMetricCertificateProved : Bool
    reciprocalMatrixIdentityProved : Bool
    finiteThreeClassFoldingInvariantProved : Bool
    finiteTorusIsEntireInfiniteCrystal : Bool
    arpesSpectralIntensityDerivedFromGeometry : Bool
    materialHamiltonianDerivedFromSupercellAlgebra : Bool

canonicalSqrt3R30ExactBoundary : Sqrt3R30ExactBoundary
canonicalSqrt3R30ExactBoundary =
  sqrt3-r30-exact-boundary
    true true true true true
    false false false
