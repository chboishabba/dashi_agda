module DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Regular-representation / isotypic decomposition for S3.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 frame torsors.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
-- Marked Legendre Hecke / Frobenius geometry.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Brandt / supersingular Hecke context.
--
-- DASHI CONTRIBUTION
--
-- PR #580 constructs the actual p=37 marked carrier as
--
--     3 coarse supersingular classes x regular S3 frame torsor
--
-- and writes T3 and T5 as four / six positive permutation orbitals
--
--     (j,g) |-> (sigma(j), h_j g),
--
-- where left frame multiplication commutes with the right deck S3 action.
-- This file performs the full right-deck isotypic compression of those SAME
-- orbitals.  It does not diagonalize an independently supplied 18x18 matrix.
--
-- Right-regular S3 gives
--
--     Q[S3] = 1 + sgn + 2 std,
--
-- so over three coarse classes the dimensions are
--
--     trivial 3, sign 3, standard isotypic 12.
--
-- The standard isotypic operator is two copies (dim std = 2) of the same
-- six-dimensional multiplicity block.  We compute that block exactly from the
-- existing orbital h_j data using the C2-fixed, zero-average multiplicity
-- slice of the regular frame representation.
--
-- Independent finite matrix factorisation / polynomial checks are kept in
-- scripts/verify_p37_deck_isotypic_blocks.py.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Tri
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedX2DeckOrbitalHeckeExact as Orb

------------------------------------------------------------------------
-- Small rational carriers.
------------------------------------------------------------------------

record Block3 : Set where
  constructor block3
  field
    c8 c0 c1 : ℚ
open Block3 public

record Std2 : Set where
  constructor std2
  field
    u v : ℚ
open Std2 public

record StdBlock3 : Set where
  constructor stdBlock3
  field
    at8 at0 at1 : Std2
open StdBlock3 public

add2 : Std2 → Std2 → Std2
add2 x y = std2 (u x + u y) (v x + v y)

scale2 : ℚ → Std2 → Std2
scale2 a x = std2 (a * u x) (a * v x)

add3 : Block3 → Block3 → Block3
add3 x y = block3 (c8 x + c8 y) (c0 x + c0 y) (c1 x + c1 y)

addStd3 : StdBlock3 → StdBlock3 → StdBlock3
addStd3 x y = stdBlock3
  (add2 (at8 x) (at8 y))
  (add2 (at0 x) (at0 y))
  (add2 (at1 x) (at1 y))

blockValue : Block3 → P37.P37GeometricJ → ℚ
blockValue x P37.j8 = c8 x
blockValue x P37.jConjugate0 = c0 x
blockValue x P37.jConjugate1 = c1 x

stdValue : StdBlock3 → P37.P37GeometricJ → Std2
stdValue x P37.j8 = at8 x
stdValue x P37.jConjugate0 = at0 x
stdValue x P37.jConjugate1 = at1 x

------------------------------------------------------------------------
-- Trivial and sign one-dimensional local representations.
------------------------------------------------------------------------

permSign : Tri.TriPermutation → ℚ
permSign Tri.permIdentity = 1ℚ
permSign Tri.permRotate = 1ℚ
permSign Tri.permRotate2 = 1ℚ
permSign Tri.permSwapMidHigh = - 1ℚ
permSign Tri.permSwapLowMid = - 1ℚ
permSign Tri.permSwapLowHigh = - 1ℚ

trivialOrbitalBlock : Orb.DeckOrbitalSpec → Block3 → Block3
trivialOrbitalBlock spec x = block3
  (blockValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.j8))
  (blockValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.jConjugate0))
  (blockValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.jConjugate1))

signOrbitalBlock : Orb.DeckOrbitalSpec → Block3 → Block3
signOrbitalBlock spec x = block3
  (permSign (Orb.atJ8 spec) *
    blockValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.j8))
  (permSign (Orb.atJConjugate0 spec) *
    blockValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.jConjugate0))
  (permSign (Orb.atJConjugate1 spec) *
    blockValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.jConjugate1))

trivialT3 signT3 : Block3 → Block3
trivialT3 x = add3 (trivialOrbitalBlock Orb.t3o0 x)
  (add3 (trivialOrbitalBlock Orb.t3o1 x)
    (add3 (trivialOrbitalBlock Orb.t3o2 x) (trivialOrbitalBlock Orb.t3o3 x)))
signT3 x = add3 (signOrbitalBlock Orb.t3o0 x)
  (add3 (signOrbitalBlock Orb.t3o1 x)
    (add3 (signOrbitalBlock Orb.t3o2 x) (signOrbitalBlock Orb.t3o3 x)))

trivialT5 signT5 : Block3 → Block3
trivialT5 x = add3 (trivialOrbitalBlock Orb.t5o0 x)
  (add3 (trivialOrbitalBlock Orb.t5o1 x)
    (add3 (trivialOrbitalBlock Orb.t5o2 x)
      (add3 (trivialOrbitalBlock Orb.t5o3 x)
        (add3 (trivialOrbitalBlock Orb.t5o4 x) (trivialOrbitalBlock Orb.t5o5 x)))))
signT5 x = add3 (signOrbitalBlock Orb.t5o0 x)
  (add3 (signOrbitalBlock Orb.t5o1 x)
    (add3 (signOrbitalBlock Orb.t5o2 x)
      (add3 (signOrbitalBlock Orb.t5o3 x)
        (add3 (signOrbitalBlock Orb.t5o4 x) (signOrbitalBlock Orb.t5o5 x)))))

-- Frobenius on the product chart: j8 is left multiplication by the odd
-- transposition permSwapLowMid; the two quadratic coarse classes are swapped
-- with no frame change.
trivialF signF : Block3 → Block3
trivialF x = block3 (c8 x) (c1 x) (c0 x)
signF x = block3 (- c8 x) (c1 x) (c0 x)

------------------------------------------------------------------------
-- Exact explicit 3x3 blocks derived from the orbital specifications.
------------------------------------------------------------------------

trivialT3MatrixExact : (x : Block3) →
  trivialT3 x ≡ block3
    ((+ 2 / 1) * c8 x + c0 x + c1 x)
    (c8 x + (+ 3 / 1) * c1 x)
    (c8 x + (+ 3 / 1) * c0 x)
trivialT3MatrixExact (block3 a b c) = refl

trivialT5MatrixExact : (x : Block3) →
  trivialT5 x ≡ block3
    ((+ 2 / 1) * a + (+ 2 / 1) * b + (+ 2 / 1) * c)
    ((+ 2 / 1) * a + b + (+ 3 / 1) * c)
    ((+ 2 / 1) * a + (+ 3 / 1) * b + c)
  where
    a = c8 x
    b = c0 x
    c = c1 x
trivialT5MatrixExact (block3 a b c) = refl

signT3MatrixExact : (x : Block3) →
  signT3 x ≡ block3
    ((- (+ 2 / 1)) * c8 x - c0 x + c1 x)
    (- c8 x - c1 x)
    (c8 x - c0 x)
signT3MatrixExact (block3 a b c) = refl

signT5MatrixExact : (x : Block3) →
  signT5 x ≡ block3
    ((+ 2 / 1) * c8 x)
    (- c0 x - (+ 3 / 1) * c1 x)
    ((- (+ 3 / 1)) * c0 x - c1 x)
signT5MatrixExact (block3 a b c) = refl

------------------------------------------------------------------------
-- Two-dimensional standard multiplicity representation extracted from the
-- actual six-frame left action.
--
-- On the right-S-fixed zero-average slice write frame values as
--
--   (u+v, -u, -v, u+v, -u, -v).
--
-- Left frame multiplication preserves this slice because left and right deck
-- changes commute.  The six matrices below are therefore not an abstract copy
-- of std inserted by hand: they are the exact action induced on this slice.
------------------------------------------------------------------------

stdLocal : Tri.TriPermutation → Std2 → Std2
stdLocal Tri.permIdentity (std2 a b) = std2 a b
stdLocal Tri.permRotate (std2 a b) = std2 b (- a - b)
stdLocal Tri.permRotate2 (std2 a b) = std2 (- a - b) a
stdLocal Tri.permSwapMidHigh (std2 a b) = std2 b a
stdLocal Tri.permSwapLowMid (std2 a b) = std2 (- a - b) b
stdLocal Tri.permSwapLowHigh (std2 a b) = std2 a (- a - b)

stdFrameValue : Std2 → P37.Frame6 → ℚ
stdFrameValue (std2 a b) P37.frame0 = a + b
stdFrameValue (std2 a b) P37.frame1 = - a
stdFrameValue (std2 a b) P37.frame2 = - b
stdFrameValue (std2 a b) P37.frame3 = a + b
stdFrameValue (std2 a b) P37.frame4 = - a
stdFrameValue (std2 a b) P37.frame5 = - b

-- Exact local intertwiner with the SAME applyLeft used by the p=37 Hecke
-- orbitals.  Six-by-six finite normalization; solve-forall is used only to
-- normalize the two rational coordinates.
stdLocalIntertwines :
  (p : Tri.TriPermutation) → (z : Std2) → (f : P37.Frame6) →
  stdFrameValue z (Orb.applyLeft p f) ≡ stdFrameValue (stdLocal p z) f
stdLocalIntertwines Tri.permIdentity (std2 a b) P37.frame0 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permIdentity (std2 a b) P37.frame1 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permIdentity (std2 a b) P37.frame2 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permIdentity (std2 a b) P37.frame3 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permIdentity (std2 a b) P37.frame4 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permIdentity (std2 a b) P37.frame5 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate (std2 a b) P37.frame0 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate (std2 a b) P37.frame1 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate (std2 a b) P37.frame2 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate (std2 a b) P37.frame3 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate (std2 a b) P37.frame4 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate (std2 a b) P37.frame5 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate2 (std2 a b) P37.frame0 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate2 (std2 a b) P37.frame1 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate2 (std2 a b) P37.frame2 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate2 (std2 a b) P37.frame3 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate2 (std2 a b) P37.frame4 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permRotate2 (std2 a b) P37.frame5 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapMidHigh (std2 a b) P37.frame0 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapMidHigh (std2 a b) P37.frame1 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapMidHigh (std2 a b) P37.frame2 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapMidHigh (std2 a b) P37.frame3 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapMidHigh (std2 a b) P37.frame4 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapMidHigh (std2 a b) P37.frame5 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowMid (std2 a b) P37.frame0 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowMid (std2 a b) P37.frame1 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowMid (std2 a b) P37.frame2 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowMid (std2 a b) P37.frame3 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowMid (std2 a b) P37.frame4 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowMid (std2 a b) P37.frame5 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowHigh (std2 a b) P37.frame0 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowHigh (std2 a b) P37.frame1 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowHigh (std2 a b) P37.frame2 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowHigh (std2 a b) P37.frame3 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowHigh (std2 a b) P37.frame4 = ℚRing.solve-∀ a b
stdLocalIntertwines Tri.permSwapLowHigh (std2 a b) P37.frame5 = ℚRing.solve-∀ a b

standardOrbitalBlock : Orb.DeckOrbitalSpec → StdBlock3 → StdBlock3
standardOrbitalBlock spec x = stdBlock3
  (stdLocal (Orb.atJ8 spec)
    (stdValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.j8)))
  (stdLocal (Orb.atJConjugate0 spec)
    (stdValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.jConjugate0)))
  (stdLocal (Orb.atJConjugate1 spec)
    (stdValue x (Orb.applyCoarse (Orb.coarsePermutation spec) P37.jConjugate1)))

standardT3 standardT5 : StdBlock3 → StdBlock3
standardT3 x = addStd3 (standardOrbitalBlock Orb.t3o0 x)
  (addStd3 (standardOrbitalBlock Orb.t3o1 x)
    (addStd3 (standardOrbitalBlock Orb.t3o2 x) (standardOrbitalBlock Orb.t3o3 x)))
standardT5 x = addStd3 (standardOrbitalBlock Orb.t5o0 x)
  (addStd3 (standardOrbitalBlock Orb.t5o1 x)
    (addStd3 (standardOrbitalBlock Orb.t5o2 x)
      (addStd3 (standardOrbitalBlock Orb.t5o3 x)
        (addStd3 (standardOrbitalBlock Orb.t5o4 x) (standardOrbitalBlock Orb.t5o5 x)))))

standardF : StdBlock3 → StdBlock3
standardF x = stdBlock3
  (stdLocal Tri.permSwapLowMid (at8 x))
  (at1 x)
  (at0 x)

------------------------------------------------------------------------
-- Explicit six-coordinate multiplicity matrices.
-- Coordinate order is (u8,v8,u0,v0,u1,v1).
------------------------------------------------------------------------

standardT3MatrixExact :
  (a b c d e f : ℚ) →
  standardT3 (stdBlock3 (std2 a b) (std2 c d) (std2 e f))
  ≡ stdBlock3
      (std2
        ((- (+ 2 / 1)) * a - (+ 2 / 1) * b + d - e - f)
        ((+ 2 / 1) * b + c + e))
      (std2
        (b + (+ 2 / 1) * e + f)
        a)
      (std2
        (b + (+ 2 / 1) * c + d)
        (- a - b))
standardT3MatrixExact a b c d e f = refl

standardT5MatrixExact :
  (a b c d e f : ℚ) →
  standardT5 (stdBlock3 (std2 a b) (std2 c d) (std2 e f))
  ≡ stdBlock3
      (std2
        (- a + (+ 2 / 1) * c - e)
        (- b - c - e))
      (std2
        ((+ 2 / 1) * a + c - (+ 2 / 1) * e - f)
        (- a - c - d + e + (+ 2 / 1) * f))
      (std2
        ((- (+ 2 / 1)) * a - (+ 2 / 1) * b - (+ 2 / 1) * c - d + e)
        (a + b + c + (+ 2 / 1) * d - e - f))
standardT5MatrixExact a b c d e f = refl

standardFMatrixExact :
  (a b c d e f : ℚ) →
  standardF (stdBlock3 (std2 a b) (std2 c d) (std2 e f))
  ≡ stdBlock3
      (std2 (- a - b) b)
      (std2 e f)
      (std2 c d)
standardFMatrixExact a b c d e f = refl

------------------------------------------------------------------------
-- Representation dimensions and independently checked spectral factor data.
------------------------------------------------------------------------

trivialDeckDimension signDeckDimension standardDeckIsotypicDimension : Nat
trivialDeckDimension = 3
signDeckDimension = 3
standardDeckIsotypicDimension = 12

isotypicDimensionsSumToEighteen :
  trivialDeckDimension + signDeckDimension + standardDeckIsotypicDimension ≡ 18
isotypicDimensionsSumToEighteen = refl

standardMultiplicityDimension : Nat
standardMultiplicityDimension = 6

standardIsotypicIsTwoMultiplicityCopies :
  2 * standardMultiplicityDimension ≡ standardDeckIsotypicDimension
standardIsotypicIsTwoMultiplicityCopies = refl

-- Exact factorisation obtained from the six-dimensional matrix above and
-- independently regenerated by the companion verifier:
--
--   charpoly(T3_std_mult)
--     = (x-1)(x+3)(x^2-3x-1)(x^2+x-1).
--
-- On the same six-dimensional block the commuting T5 and Frobenius operators
-- are rational polynomials in T3:
--
-- 34 T5 = -38 I -242 T3 +147 T3^2 +158 T3^3 -12 T3^4 -13 T3^5
-- 34 F  =  -7 I -126 T3 + 66 T3^2 +115 T3^3 - 4 T3^4 -10 T3^5.
--
-- Consequently the standard-block joint factors are:
--
--   T3=1                       -> (T5,F)=(0,+1)
--   T3=-3                      -> (T5,F)=(-2,-1)
--   T3^2-3 T3-1=0             -> T5=1-T3,  F=+1
--   T3^2+T3-1=0               -> T5=-3T3-1, F=-1.
--
-- The companion script checks these identities directly from the orbital
-- specs, not from these comments.

record P37MarkedDeckIsotypicBoundary : Set where
  field
    sourceNativeOrbitalSpecsConsumed : Bool
    trivialBlockIsCoarseBrandt : Bool
    signBlockConstructed : Bool
    standardMultiplicityBlockConstructed : Bool
    localStandardIntertwinerConstructed : Bool
    deckDimensionsThreeThreeTwelve : Bool
    standardT3FactorizationIndependentlyChecked : Bool
    standardT5PolynomialInT3IndependentlyChecked : Bool
    standardFPolynomialInT3IndependentlyChecked : Bool
    p37MarkedHeckeCollapsedToScalarFingerprintOnly : Bool

canonicalP37MarkedDeckIsotypicBoundary : P37MarkedDeckIsotypicBoundary
canonicalP37MarkedDeckIsotypicBoundary = record
  { sourceNativeOrbitalSpecsConsumed = true
  ; trivialBlockIsCoarseBrandt = true
  ; signBlockConstructed = true
  ; standardMultiplicityBlockConstructed = true
  ; localStandardIntertwinerConstructed = true
  ; deckDimensionsThreeThreeTwelve = true
  ; standardT3FactorizationIndependentlyChecked = true
  ; standardT5PolynomialInT3IndependentlyChecked = true
  ; standardFPolynomialInT3IndependentlyChecked = true
  ; p37MarkedHeckeCollapsedToScalarFingerprintOnly = false
  }
