module DASHI.Mathematics.Algebra.RationalOctonionSignedBasisAutomorphismExact where

------------------------------------------------------------------------
-- EXPLICIT RATIONAL OCTONION AUTOMORPHISMS
--
-- The repository's Cayley--Dickson octonions admit many signed permutations
-- of the seven imaginary basis vectors.  A local exhaustive basis-table probe
-- found exactly 1344 such signed basis permutations preserving multiplication.
-- Two small transformations generate that finite signed-basis automorphism
-- group.  This file source-writes those two generators as actual rational
-- octonion maps and proves finite order, multiplication / conjugation / norm
-- preservation by exact coordinate identities.
--
-- The finite closure order 1344 remains a local combinatorial diagnostic here;
-- this file does not identify the full algebraic automorphism group G2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

autoA : O.RationalOctonion → O.RationalOctonion
autoA (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.oct (Q.quat a0 (- a1) a2 (- a3)) (Q.quat a5 a4 a7 a6)

autoB : O.RationalOctonion → O.RationalOctonion
autoB (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.oct (Q.quat a0 a5 a1 a4) (Q.quat a7 a2 a6 a3)

------------------------------------------------------------------------
-- Explicit invertibility: A is an involution and B has order three.
------------------------------------------------------------------------

autoASquaredIdentity : ∀ value → autoA (autoA value) ≡ value
autoASquaredIdentity
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ []

autoBCubedIdentity : ∀ value → autoB (autoB (autoB value)) ≡ value
autoBCubedIdentity
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) = refl

autoAPreservesProduct : ∀ left right →
  autoA (O._*o_ left right) ≡ O._*o_ (autoA left) (autoA right)
autoAPreservesProduct
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7))
  (O.oct (Q.quat b0 b1 b2 b3) (Q.quat b4 b5 b6 b7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷
      b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ []

autoBPreservesProduct : ∀ left right →
  autoB (O._*o_ left right) ≡ O._*o_ (autoB left) (autoB right)
autoBPreservesProduct
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7))
  (O.oct (Q.quat b0 b1 b2 b3) (Q.quat b4 b5 b6 b7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷
      b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ []

autoACommutesConjugation : ∀ value →
  autoA (O.octonionConjugate value) ≡ O.octonionConjugate (autoA value)
autoACommutesConjugation
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ []

autoBCommutesConjugation : ∀ value →
  autoB (O.octonionConjugate value) ≡ O.octonionConjugate (autoB value)
autoBCommutesConjugation
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars = a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ []

autoAPreservesNorm : ∀ value → O.octonionNormSq (autoA value) ≡ O.octonionNormSq value
autoAPreservesNorm
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ [])

autoBPreservesNorm : ∀ value → O.octonionNormSq (autoB value) ≡ O.octonionNormSq value
autoBPreservesNorm
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ [])

record SignedBasisAutomorphismBoundary : Set where
  constructor signed-basis-automorphism-boundary
  field
    generatorAOrderTwoPaid : Bool
    generatorBOrderThreePaid : Bool
    generatorAProductPreserving : Bool
    generatorBProductPreserving : Bool
    generatorAConjugationPreserving : Bool
    generatorBConjugationPreserving : Bool
    generatorANormPreserving : Bool
    generatorBNormPreserving : Bool
    localSignedBasisClosureOrder : Nat
    fullG2RecognitionPaid : Bool
open SignedBasisAutomorphismBoundary public

canonicalBoundary : SignedBasisAutomorphismBoundary
canonicalBoundary =
  signed-basis-automorphism-boundary
    true true true true true true true true 1344 false
