module DASHI.Mathematics.Algebra.RationalAlbertSignedMonomialAutomorphismsExact where

------------------------------------------------------------------------
-- LIFT THE EXPLICIT OCTONION SIGNED-MONOMIAL GROUP TO H_3(O_Q)
--
-- Any octonion automorphism commuting with conjugation acts diagonally on the
-- three off-diagonal octonion coordinates of the Albert algebra while fixing
-- the rational diagonal.  Here we instantiate that construction for the two
-- explicit generators g7/g2 from
-- `RationalOctonionSignedMonomialAutomorphismsExact`.
--
-- Source-written below:
--   * order 7 / order 2 laws after the lift;
--   * preservation of the Albert Jordan product;
--   * preservation of the cubic norm;
--   * commutation with the already-paid coordinate S3 generators.
--
-- The companion finite script checks the four generators close to an explicit
-- 8064-element signed-permutation subgroup on the 27 rational coordinates:
--
--   1344 (octonion signed-monomial) x 6 (coordinate S3) = 8064.
--
-- This is a genuine constructive subgroup of Aut(H_3(O_Q)); it is not promoted
-- to the full algebraic/Lie group F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalOctonionSignedMonomialAutomorphismsExact as G
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S3

liftO : (O.RationalOctonion → O.RationalOctonion) → A.RationalAlbert → A.RationalAlbert
liftO f (A.albert a b c x y z) = A.albert a b c (f x) (f y) (f z)

g7A g2A : A.RationalAlbert → A.RationalAlbert
g7A = liftO G.g7O
g2A = liftO G.g2O

------------------------------------------------------------------------
-- Orders.
------------------------------------------------------------------------

g2ASquaredIdentity : ∀ value → g2A (g2A value) ≡ value
g2ASquaredIdentity (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.g2SquaredIdentity x)
    (G.g2SquaredIdentity y)
    (G.g2SquaredIdentity z)


g7ASquared g7ACubed g7AFourth g7AFifth g7ASixth : A.RationalAlbert → A.RationalAlbert
g7ASquared value = g7A (g7A value)
g7ACubed value = g7A (g7ASquared value)
g7AFourth value = g7A (g7ACubed value)
g7AFifth value = g7A (g7AFourth value)
g7ASixth value = g7A (g7AFifth value)

g7ASeventhIdentity : ∀ value → g7A (g7ASixth value) ≡ value
g7ASeventhIdentity (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.g7SeventhIdentity x)
    (G.g7SeventhIdentity y)
    (G.g7SeventhIdentity z)

------------------------------------------------------------------------
-- Direct product / cubic preservation.
--
-- The proofs follow the repository's exact rational-polynomial style: destruct
-- the complete two-input 54-coordinate carrier and solve every resulting
-- coordinate identity.
------------------------------------------------------------------------

g7APreservesProduct : ∀ left right →
  g7A (J.jordanProduct left right) ≡ J.jordanProduct (g7A left) (g7A right)
g7APreservesProduct
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7)))
  (A.albert d e f
    (O.oct (Q.quat u0 u1 u2 u3) (Q.quat u4 u5 u6 u7))
    (O.oct (Q.quat v0 v1 v2 v3) (Q.quat v4 v5 v6 v7))
    (O.oct (Q.quat w0 w1 w2 w3) (Q.quat w4 w5 w6 w7))) =
  Laws.albertExt
    (solve vars) (solve vars) (solve vars)
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷
      y0 ∷ y1 ∷ y2 ∷ y3 ∷ y4 ∷ y5 ∷ y6 ∷ y7 ∷
      z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷
      d ∷ e ∷ f ∷
      u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷
      v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ v5 ∷ v6 ∷ v7 ∷
      w0 ∷ w1 ∷ w2 ∷ w3 ∷ w4 ∷ w5 ∷ w6 ∷ w7 ∷ []

g2APreservesProduct : ∀ left right →
  g2A (J.jordanProduct left right) ≡ J.jordanProduct (g2A left) (g2A right)
g2APreservesProduct
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7)))
  (A.albert d e f
    (O.oct (Q.quat u0 u1 u2 u3) (Q.quat u4 u5 u6 u7))
    (O.oct (Q.quat v0 v1 v2 v3) (Q.quat v4 v5 v6 v7))
    (O.oct (Q.quat w0 w1 w2 w3) (Q.quat w4 w5 w6 w7))) =
  Laws.albertExt
    (solve vars) (solve vars) (solve vars)
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷
      y0 ∷ y1 ∷ y2 ∷ y3 ∷ y4 ∷ y5 ∷ y6 ∷ y7 ∷
      z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷
      d ∷ e ∷ f ∷
      u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷
      v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ v5 ∷ v6 ∷ v7 ∷
      w0 ∷ w1 ∷ w2 ∷ w3 ∷ w4 ∷ w5 ∷ w6 ∷ w7 ∷ []


g7APreservesCubic : ∀ value → A.cubicNorm (g7A value) ≡ A.cubicNorm value
g7APreservesCubic
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7))) =
  solve
    (a ∷ b ∷ c ∷
     x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷
     y0 ∷ y1 ∷ y2 ∷ y3 ∷ y4 ∷ y5 ∷ y6 ∷ y7 ∷
     z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ [])

g2APreservesCubic : ∀ value → A.cubicNorm (g2A value) ≡ A.cubicNorm value
g2APreservesCubic
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7))) =
  solve
    (a ∷ b ∷ c ∷
     x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷
     y0 ∷ y1 ∷ y2 ∷ y3 ∷ y4 ∷ y5 ∷ y6 ∷ y7 ∷
     z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ [])

------------------------------------------------------------------------
-- The octonion action commutes with coordinate S3.
------------------------------------------------------------------------

g7CommutesCycle : ∀ value → g7A (S3.cycleA value) ≡ S3.cycleA (g7A value)
g7CommutesCycle (A.albert _ _ _ _ _ _) = refl

g2CommutesCycle : ∀ value → g2A (S3.cycleA value) ≡ S3.cycleA (g2A value)
g2CommutesCycle (A.albert _ _ _ _ _ _) = refl

g7CommutesSwap : ∀ value → g7A (S3.swapA value) ≡ S3.swapA (g7A value)
g7CommutesSwap (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.g7CommutesConjugation x)
    (G.g7CommutesConjugation z)
    (G.g7CommutesConjugation y)

g2CommutesSwap : ∀ value → g2A (S3.swapA value) ≡ S3.swapA (g2A value)
g2CommutesSwap (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.g2CommutesConjugation x)
    (G.g2CommutesConjugation z)
    (G.g2CommutesConjugation y)

record AlbertSignedMonomialBoundary : Set where
  constructor albert-signed-monomial-boundary
  field
    orderSevenAlbertAutomorphismSourceWritten : Bool
    involutiveAlbertAutomorphismSourceWritten : Bool
    jordanProductPreservationSourceWritten : Bool
    cubicNormPreservationSourceWritten : Bool
    commutesWithCoordinateS3Paid : Bool
    octonionSignedMonomialClosure1344RuntimeChecked : Bool
    combinedAlbertSubgroup8064RuntimeChecked : Bool
    fullF4AutomorphismGroupPaid : Bool
open AlbertSignedMonomialBoundary public

currentAlbertSignedMonomialBoundary : AlbertSignedMonomialBoundary
currentAlbertSignedMonomialBoundary =
  albert-signed-monomial-boundary
    true true true true true true true false
