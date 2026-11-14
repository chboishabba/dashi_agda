module DASHI.Mathematics.Symmetry.DiamondNVFourAxisPermutationExact where

-- Classical diamond <111> unoriented NV-axis labels. Uses the four
-- actual labels already defined in PR #1238, but does not import an
-- unmerged PR or identify these labels with D4h's four basal axes.
-- The four labels are an even-sign representative of four lines
-- through the origin, not four oriented vectors with independent sign.

open import Agda.Builtin.Equality using (_≡_; refl)

data Axis : Set where
  aaa abb bab bba : Axis

-- Cyclic coordinate permutation (x,y,z) -> (y,z,x)
cycle : Axis → Axis
cycle aaa = aaa
cycle abb = bba
cycle bba = bab
cycle bab = abb

cycleThree : (a : Axis) → cycle (cycle (cycle a)) ≡ a
cycleThree aaa = refl
cycleThree abb = refl
cycleThree bab = refl
cycleThree bba = refl

-- A cubic quarter-turn (x,y,z)->(-y,x,z) acts on unoriented
-- axes by canonicalising to the even-negative representative.
quarterZ : Axis → Axis
quarterZ aaa = abb
quarterZ abb = bba
quarterZ bba = bab
quarterZ bab = aaa

quarterZFour : (a : Axis) →
  quarterZ (quarterZ (quarterZ (quarterZ a))) ≡ a
quarterZFour aaa = refl
quarterZFour abb = refl
quarterZFour bab = refl
quarterZFour bba = refl

-- These are induced finite permutations of *axes* only.
-- A physical NV centre breaks local symmetry and requires a
-- defect-site stabilizer; this module proves no C3 spin-energy symmetry.
