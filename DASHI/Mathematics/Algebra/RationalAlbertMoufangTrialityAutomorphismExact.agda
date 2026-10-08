module DASHI.Mathematics.Algebra.RationalAlbertMoufangTrialityAutomorphismExact where

------------------------------------------------------------------------
-- ONE EXPLICIT SPIN(8)-TRIALITY-TYPE ALBERT AUTOMORPHISM
--
-- Let u = e1 be the repository's unit imaginary rational octonion.  Alternativity
-- gives the Moufang identity
--
--     (u x) (y u) = u (x y) u.
--
-- Hence the three orthogonal maps
--
--     L_u(x)=u x,   R_u(y)=y u,   M_u(z)=(u z)u
--
-- form an explicit triality triple.  Acting by these three maps on the three
-- off-diagonal coordinates of H_3(O_Q), while fixing the diagonal scalars,
-- preserves the Albert cubic and Jordan product.  This is a genuine non-diagonal
-- triality-type transformation and is stronger than the common diagonal G2
-- action constructed in the signed-basis owner.
--
-- Full Spin(8) triality and full F4 generation are not inferred from one triple.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws

leftU rightU middleU : O.RationalOctonion → O.RationalOctonion
leftU x = O._*o_ O.e1 x
rightU x = O._*o_ x O.e1
middleU x = O._*o_ (O._*o_ O.e1 x) O.e1

/-- Coordinate form of the Moufang triality identity for the selected unit. -/
selectedMoufangTriality : ∀ x y →
  O._*o_ (leftU x) (rightU y) ≡ middleU (O._*o_ x y)
selectedMoufangTriality
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7))
  (O.oct (Q.quat b0 b1 b2 b3) (Q.quat b4 b5 b6 b7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷
      b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ []

trialityA : A.RationalAlbert → A.RationalAlbert
trialityA (A.albert a b c x y z) =
  A.albert a b c (leftU x) (rightU y) (middleU z)

trialityPreservesProduct : ∀ left right →
  trialityA (J.jordanProduct left right) ≡
  J.jordanProduct (trialityA left) (trialityA right)
trialityPreservesProduct
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

trialityPreservesCubic : ∀ value →
  A.cubicNorm (trialityA value) ≡ A.cubicNorm value
trialityPreservesCubic
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

record TrialityBoundary : Set where
  constructor triality-boundary
  field
    selectedMoufangTriplePaid : Bool
    AlbertProductPreservationPaid : Bool
    AlbertCubicPreservationPaid : Bool
    fullSpin8TrialityPaid : Bool
    fullF4Paid : Bool
open TrialityBoundary public

canonicalBoundary : TrialityBoundary
canonicalBoundary = triality-boundary true true true false false
