module DASHI.Mathematics.Algebra.RationalOctonionSignedMonomialAutomorphismsExact where

------------------------------------------------------------------------
-- EXPLICIT SIGNED-MONOMIAL AUTOMORPHISMS OF THE RATIONAL OCTONIONS
--
-- The repository octonion basis is 1,e1,...,e7 in the coordinate order of
-- two rational quaternions.  Exhaustive local enumeration of all 7!*2^7
-- signed imaginary-basis permutations preserving the literal Cayley-Dickson
-- multiplication table finds exactly 1344 automorphisms.
--
-- Two explicit generators suffice:
--
-- g7: e1->e2, e2->-e4, e3->-e6, e4->e3,
--     e5->e1, e6->e7, e7->e5
--
-- g2: e1->-e1, e2->e2, e3->-e3, e4->e5,
--     e5->e4, e6->e7, e7->e6.
--
-- Companion runtime:
--   scripts/check_rational_octonion_signed_monomial_automorphisms.py
-- checks total=1344, order(g7)=7, order(g2)=2 and <g7,g2>=all 1344.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

g7O : O.RationalOctonion → O.RationalOctonion
g7O (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.oct
    (Q.quat a0 b1 a1 b0)
    (Q.quat (- a2) b3 (- a3) b2)

g2O : O.RationalOctonion → O.RationalOctonion
g2O (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.oct
    (Q.quat a0 (- a1) a2 (- a3))
    (Q.quat b1 b0 b3 b2)

g7PreservesProduct : ∀ left right →
  g7O (O._*o_ left right) ≡ O._*o_ (g7O left) (g7O right)
g7PreservesProduct
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (O.oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ []

g2PreservesProduct : ∀ left right →
  g2O (O._*o_ left right) ≡ O._*o_ (g2O left) (g2O right)
g2PreservesProduct
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (O.oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ []

g7CommutesConjugation : ∀ value →
  g7O (O.octonionConjugate value) ≡ O.octonionConjugate (g7O value)
g7CommutesConjugation
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []

g2CommutesConjugation : ∀ value →
  g2O (O.octonionConjugate value) ≡ O.octonionConjugate (g2O value)
g2CommutesConjugation
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []

g7PreservesNorm : ∀ value → O.octonionNormSq (g7O value) ≡ O.octonionNormSq value
g7PreservesNorm
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])

g2PreservesNorm : ∀ value → O.octonionNormSq (g2O value) ≡ O.octonionNormSq value
g2PreservesNorm
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])

g2SquaredIdentity : ∀ value → g2O (g2O value) ≡ value
g2SquaredIdentity
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []

g7Squared g7Cubed g7Fourth g7Fifth g7Sixth : O.RationalOctonion → O.RationalOctonion
g7Squared value = g7O (g7O value)
g7Cubed value = g7O (g7Squared value)
g7Fourth value = g7O (g7Cubed value)
g7Fifth value = g7O (g7Fourth value)
g7Sixth value = g7O (g7Fifth value)

g7SeventhIdentity : ∀ value → g7O (g7Sixth value) ≡ value
g7SeventhIdentity
    (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []

signedMonomialAutomorphismCount : Nat
signedMonomialAutomorphismCount = 1344

record SignedMonomialAutomorphismBoundary : Set where
  constructor signed-monomial-automorphism-boundary
  field
    explicitOrderSevenGeneratorPaid : Bool
    explicitInvolutionGeneratorPaid : Bool
    bothGeneratorsMultiplicativePaid : Bool
    bothGeneratorsConjugationCompatiblePaid : Bool
    bothGeneratorsNormPreservingPaid : Bool
    exhaustiveSignedBasisSearchCount : Bool
    generatedClosureEqualsExhaustiveSetRuntimeChecked : Bool
    fullContinuousG2Identified : Bool
open SignedMonomialAutomorphismBoundary public

currentSignedMonomialAutomorphismBoundary : SignedMonomialAutomorphismBoundary
currentSignedMonomialAutomorphismBoundary =
  signed-monomial-automorphism-boundary
    true true true true true true true false
