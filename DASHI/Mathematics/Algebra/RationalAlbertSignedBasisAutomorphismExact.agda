module DASHI.Mathematics.Algebra.RationalAlbertSignedBasisAutomorphismExact where

------------------------------------------------------------------------
-- LIFT THE EXPLICIT OCTONION SIGNED-BASIS AUTOMORPHISMS TO H_3(O_Q)
--
-- The rational octonion owner supplies two concrete automorphisms `autoA` and
-- `autoB` generating the locally enumerated 1344-element signed-basis subgroup.
-- Applying either automorphism simultaneously to the three off-diagonal
-- octonions, while fixing the diagonal rationals, gives an Albert
-- automorphism.  This file source-writes the product/cubic preservation laws on
-- the actual rational Albert carrier.
--
-- These diagonal-octonion automorphisms commute with the already-owned S3
-- coordinate permutations.  Locally the resulting finite subgroup therefore
-- has order 1344*6 = 8064.  This is still far smaller than full F4 and is kept
-- attribution-safe.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalOctonionSignedBasisAutomorphismExact as G
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S3

------------------------------------------------------------------------
-- The two lifted automorphisms.
------------------------------------------------------------------------

liftAutoA : A.RationalAlbert → A.RationalAlbert
liftAutoA (A.albert a b c x y z) =
  A.albert a b c (G.autoA x) (G.autoA y) (G.autoA z)

liftAutoB : A.RationalAlbert → A.RationalAlbert
liftAutoB (A.albert a b c x y z) =
  A.albert a b c (G.autoB x) (G.autoB y) (G.autoB z)

liftAutoASquaredIdentity : ∀ value → liftAutoA (liftAutoA value) ≡ value
liftAutoASquaredIdentity (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.autoASquaredIdentity x)
    (G.autoASquaredIdentity y)
    (G.autoASquaredIdentity z)

liftAutoBCubedIdentity : ∀ value →
  liftAutoB (liftAutoB (liftAutoB value)) ≡ value
liftAutoBCubedIdentity (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.autoBCubedIdentity x)
    (G.autoBCubedIdentity y)
    (G.autoBCubedIdentity z)

------------------------------------------------------------------------
-- Product preservation on the literal 27-coordinate Jordan carrier.
------------------------------------------------------------------------

liftAutoAPreservesProduct : ∀ left right →
  liftAutoA (J.jordanProduct left right)
  ≡ J.jordanProduct (liftAutoA left) (liftAutoA right)
liftAutoAPreservesProduct
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

liftAutoBPreservesProduct : ∀ left right →
  liftAutoB (J.jordanProduct left right)
  ≡ J.jordanProduct (liftAutoB left) (liftAutoB right)
liftAutoBPreservesProduct
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

------------------------------------------------------------------------
-- Cubic norm preservation.
------------------------------------------------------------------------

liftAutoAPreservesCubic : ∀ value → A.cubicNorm (liftAutoA value) ≡ A.cubicNorm value
liftAutoAPreservesCubic
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7))) =
  solve vars
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷
      y0 ∷ y1 ∷ y2 ∷ y3 ∷ y4 ∷ y5 ∷ y6 ∷ y7 ∷
      z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ []

liftAutoBPreservesCubic : ∀ value → A.cubicNorm (liftAutoB value) ≡ A.cubicNorm value
liftAutoBPreservesCubic
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7))) =
  solve vars
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷
      y0 ∷ y1 ∷ y2 ∷ y3 ∷ y4 ∷ y5 ∷ y6 ∷ y7 ∷
      z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ []

------------------------------------------------------------------------
-- The diagonal octonion action commutes with the coordinate S3.
------------------------------------------------------------------------

liftAutoACycleCommute : ∀ value →
  liftAutoA (S3.cycleA value) ≡ S3.cycleA (liftAutoA value)
liftAutoACycleCommute (A.albert _ _ _ _ _ _) = refl

liftAutoBCycleCommute : ∀ value →
  liftAutoB (S3.cycleA value) ≡ S3.cycleA (liftAutoB value)
liftAutoBCycleCommute (A.albert _ _ _ _ _ _) = refl

liftAutoASwapCommute : ∀ value →
  liftAutoA (S3.swapA value) ≡ S3.swapA (liftAutoA value)
liftAutoASwapCommute (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.autoACommutesConjugation x)
    (G.autoACommutesConjugation z)
    (G.autoACommutesConjugation y)

liftAutoBSwapCommute : ∀ value →
  liftAutoB (S3.swapA value) ≡ S3.swapA (liftAutoB value)
liftAutoBSwapCommute (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (G.autoBCommutesConjugation x)
    (G.autoBCommutesConjugation z)
    (G.autoBCommutesConjugation y)

------------------------------------------------------------------------
-- Attribution-safe subgroup boundary.
------------------------------------------------------------------------

record AlbertSignedBasisAutomorphismBoundary : Set where
  constructor albert-signed-basis-automorphism-boundary
  field
    liftedOctonionGeneratorsPaid : Bool
    liftedProductPreservationSourceWritten : Bool
    liftedCubicPreservationSourceWritten : Bool
    commutationWithCoordinateS3Paid : Bool
    localOctonionSignedBasisClosureOrder : Nat
    localCombinedAlbertFiniteSubgroupOrder : Nat
    fullF4AutomorphismGroupPaid : Bool
open AlbertSignedBasisAutomorphismBoundary public

canonicalBoundary : AlbertSignedBasisAutomorphismBoundary
canonicalBoundary =
  albert-signed-basis-automorphism-boundary
    true true true true 1344 8064 false
