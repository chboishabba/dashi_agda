module DASHI.Mathematics.Algebra.RationalOctonionLinearityExact where

------------------------------------------------------------------------
-- LINEARITY OF CONJUGATION AND THE EXPLICIT SIGNED-BASIS AUTOMORPHISMS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalOctonionSignedBasisAutomorphismExact as G

conjugateAdditive : ∀ left right →
  O.octonionConjugate (O._+o_ left right)
  ≡ O._+o_ (O.octonionConjugate left) (O.octonionConjugate right)
conjugateAdditive
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

conjugateScale : ∀ scalar value →
  O.octonionConjugate (A.scaleO scalar value)
  ≡ A.scaleO scalar (O.octonionConjugate value)
conjugateScale scalar
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = scalar ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ []

autoAAdditive : ∀ left right →
  G.autoA (O._+o_ left right) ≡ O._+o_ (G.autoA left) (G.autoA right)
autoAAdditive
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

autoBAdditive : ∀ left right →
  G.autoB (O._+o_ left right) ≡ O._+o_ (G.autoB left) (G.autoB right)
autoBAdditive
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

autoAScale : ∀ scalar value →
  G.autoA (A.scaleO scalar value) ≡ A.scaleO scalar (G.autoA value)
autoAScale scalar
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = scalar ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ []

autoBScale : ∀ scalar value →
  G.autoB (A.scaleO scalar value) ≡ A.scaleO scalar (G.autoB value)
autoBScale scalar
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = scalar ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ []
