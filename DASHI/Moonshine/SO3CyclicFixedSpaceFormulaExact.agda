module DASHI.Moonshine.SO3CyclicFixedSpaceFormulaExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Record the closed fixed-space count for restricting the integer-spin SO(3)
-- weight carrier V_j to an axial cyclic subgroup C_n:
--
--   dim(V_j^{C_n}) = 2 * floor(j / n) + 1.
--
-- This is the count of weights m in {-j,...,+j} divisible by n.  We use the
-- formula as a generic fingerprint producer and compare C2/C3 against a first
-- richer C2/C3/C5 probe.  C5 is used only as an information probe here; this
-- module does not claim that C5 is the correct Ogg-reduction subgroup.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat.Base using (_/_)

import DASHI.Moonshine.SO3CyclicFixedSpaceScanExact as Scan

cyclicFixedDimension : Nat → Nat → Nat
cyclicFixedDimension order j = 2 * (j / order) + 1

c2FormulaMatchesJ4 : cyclicFixedDimension 2 4 ≡ Scan.fixedC2 4
c2FormulaMatchesJ4 = refl

c2FormulaMatchesJ5 : cyclicFixedDimension 2 5 ≡ Scan.fixedC2 5
c2FormulaMatchesJ5 = refl

c3FormulaMatchesJ4 : cyclicFixedDimension 3 4 ≡ Scan.fixedC3 4
c3FormulaMatchesJ4 = refl

c3FormulaMatchesJ5 : cyclicFixedDimension 3 5 ≡ Scan.fixedC3 5
c3FormulaMatchesJ5 = refl

fixedFingerprint : List Nat → Nat → List Nat
fixedFingerprint orders j = map (λ order → cyclicFixedDimension order j) orders

orders23 : List Nat
orders23 = 2 ∷ 3 ∷ []

orders235 : List Nat
orders235 = 2 ∷ 3 ∷ 5 ∷ []

j4Fingerprint23 : fixedFingerprint orders23 4 ≡ 5 ∷ 3 ∷ []
j4Fingerprint23 = refl

j5Fingerprint23 : fixedFingerprint orders23 5 ≡ 5 ∷ 3 ∷ []
j5Fingerprint23 = refl

j4J5CollisionPersistsFor23 :
  fixedFingerprint orders23 4 ≡ fixedFingerprint orders23 5
j4J5CollisionPersistsFor23 = refl

j4Fingerprint235 : fixedFingerprint orders235 4 ≡ 5 ∷ 3 ∷ 1 ∷ []
j4Fingerprint235 = refl

j5Fingerprint235 : fixedFingerprint orders235 5 ≡ 5 ∷ 3 ∷ 3 ∷ []
j5Fingerprint235 = refl

------------------------------------------------------------------------
-- The extra order-five fixed-space probe retains information discarded by
-- the order-two/order-three pair.  We intentionally state the distinction as
-- two exact values rather than promote a preferred-subgroup conclusion.
------------------------------------------------------------------------

j4C5FixedIsOne : cyclicFixedDimension 5 4 ≡ 1
j4C5FixedIsOne = refl

j5C5FixedIsThree : cyclicFixedDimension 5 5 ≡ 3
j5C5FixedIsThree = refl
