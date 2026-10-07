module DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismLawsExact where

------------------------------------------------------------------------
-- PRODUCT / CUBIC PRESERVATION FOR THE EXPLICIT ALBERT S3
--
-- Direct coordinate polynomial proofs, following the same proof style as the
-- rational octonion and Albert Jordan-law owners.  These are source-written
-- kernel obligations; no promotion to full F4 is made.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S3

cyclePreservesProduct : S3.CyclePreservesProduct
cyclePreservesProduct
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

swapPreservesProduct : S3.SwapPreservesProduct
swapPreservesProduct
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

cyclePreservesCubic : S3.CyclePreservesCubic
cyclePreservesCubic
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

swapPreservesCubic : S3.SwapPreservesCubic
swapPreservesCubic
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

record Boundary : Set where
  constructor boundary
  field
    cycleProductPreservationSourceWritten : Bool
    swapProductPreservationSourceWritten : Bool
    cycleCubicPreservationSourceWritten : Bool
    swapCubicPreservationSourceWritten : Bool
    fullF4Paid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true false
