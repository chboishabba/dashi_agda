module DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact where

------------------------------------------------------------------------
-- COORDINATE LAW PROOFS FOR THE RATIONAL ALBERT PRODUCT
--
-- This follows the same exact-polynomial proof style as the repository's
-- rational quaternion/octonion owners: destruct all rational coordinates and
-- discharge each resulting coordinate identity with the rational ring solver.
--
-- The product itself is the explicit Hermitian symmetrisation written in
-- RationalAlbertJordanProductExact.  The proofs below therefore do not appeal
-- to associative matrix algebra (which would be invalid over octonions).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J

------------------------------------------------------------------------
-- Extensionality for the six Hermitian coordinate blocks.
------------------------------------------------------------------------

albertExt :
  ∀ {left right : A.RationalAlbert} →
  A.diagonal0 left ≡ A.diagonal0 right →
  A.diagonal1 left ≡ A.diagonal1 right →
  A.diagonal2 left ≡ A.diagonal2 right →
  A.off12 left ≡ A.off12 right →
  A.off20 left ≡ A.off20 right →
  A.off01 left ≡ A.off01 right →
  left ≡ right
albertExt {A.albert _ _ _ _ _ _} {A.albert _ _ _ _ _ _}
  refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- Commutativity.
------------------------------------------------------------------------

jordanCommutative : ∀ left right →
  J.jordanProduct left right ≡ J.jordanProduct right left
jordanCommutative
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7)))
  (A.albert d e f
    (O.oct (Q.quat u0 u1 u2 u3) (Q.quat u4 u5 u6 u7))
    (O.oct (Q.quat v0 v1 v2 v3) (Q.quat v4 v5 v6 v7))
    (O.oct (Q.quat w0 w1 w2 w3) (Q.quat w4 w5 w6 w7))) =
  albertExt
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
-- Distinguished unit.
------------------------------------------------------------------------

jordanRightUnit : ∀ value →
  J.jordanProduct value A.unitAlbert ≡ value
jordanRightUnit
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7))) =
  albertExt
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
      z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ []

jordanLeftUnit : ∀ value →
  J.jordanProduct A.unitAlbert value ≡ value
jordanLeftUnit value =
  trans (jordanCommutative A.unitAlbert value) (jordanRightUnit value)

------------------------------------------------------------------------
-- Exceptional Jordan identity.
--
-- The theorem is source-written as the direct 54-variable polynomial
-- exhaustion.  It remains kernel-pending until Agda is run on this branch.
------------------------------------------------------------------------

jordanIdentity : J.JordanIdentity
jordanIdentity
  (A.albert a b c
    (O.oct (Q.quat x0 x1 x2 x3) (Q.quat x4 x5 x6 x7))
    (O.oct (Q.quat y0 y1 y2 y3) (Q.quat y4 y5 y6 y7))
    (O.oct (Q.quat z0 z1 z2 z3) (Q.quat z4 z5 z6 z7)))
  (A.albert d e f
    (O.oct (Q.quat u0 u1 u2 u3) (Q.quat u4 u5 u6 u7))
    (O.oct (Q.quat v0 v1 v2 v3) (Q.quat v4 v5 v6 v7))
    (O.oct (Q.quat w0 w1 w2 w3) (Q.quat w4 w5 w6 w7))) =
  albertExt
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

record AlbertJordanLawBoundary : Set where
  constructor albert-jordan-law-boundary
  field
    productCommutativitySourceWritten : Bool
    unitLawsSourceWritten : Bool
    jordanIdentitySourceWritten : Bool
    agdaKernelReceiptObserved : Bool
    f4AutomorphismActionPaid : Bool
open AlbertJordanLawBoundary public

currentAlbertJordanLawBoundary : AlbertJordanLawBoundary
currentAlbertJordanLawBoundary =
  albert-jordan-law-boundary true true true false false
