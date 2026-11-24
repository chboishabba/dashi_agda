{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayG1CompactSimpleFiniteScopeValidatorExact where

------------------------------------------------------------------------
-- SOURCE / STATUS
--
-- Finite G1.01 scope hygiene for the compact-simple index surface in
-- DASHI/Physics/YangMills/CompactSimpleQuantitativeCoverage.agda:20-45.
-- Roadmap context:
-- Docs/roadmaps/YMClayUnifiedUnpostulate43AndSameOSMaxCut20261114.md:157-158
-- Docs/physics/YMClay23PhysicalProducersCurrentMaxCut20261109.md:50-58
-- This validates only the existing finite index domain; it does not construct
-- group-by-group physical Yang-Mills measures or discharge Clay G1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (tt)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact

natLeBool : Nat → Nat → Bool
natLeBool zero _ = true
natLeBool (suc _) zero = false
natLeBool (suc left) (suc right) = natLeBool left right

natLeBoolComplete : ∀ left right → left ≤ right → natLeBool left right ≡ true
natLeBoolComplete zero right left≤right = refl
natLeBoolComplete (suc left) zero ()
natLeBoolComplete (suc left) (suc right) (s≤s left≤right) =
  natLeBoolComplete left right left≤right

natLeBoolSound : ∀ left right → natLeBool left right ≡ true → left ≤ right
natLeBoolSound zero right valid = z≤n
natLeBoolSound (suc left) zero ()
natLeBoolSound (suc left) (suc right) valid =
  s≤s (natLeBoolSound left right valid)

validCompactSimpleIndex? : Compact.CompactSimpleLieGroup → Bool
validCompactSimpleIndex? (Compact.SU n) = natLeBool 2 n
validCompactSimpleIndex? (Compact.SOodd n) = natLeBool 1 n
validCompactSimpleIndex? (Compact.SOeven n) = natLeBool 3 n
validCompactSimpleIndex? (Compact.Sp n) = natLeBool 1 n
validCompactSimpleIndex? Compact.G2 = true
validCompactSimpleIndex? Compact.F4 = true
validCompactSimpleIndex? Compact.E6 = true
validCompactSimpleIndex? Compact.E7 = true
validCompactSimpleIndex? Compact.E8 = true

validCompactSimpleIndexComplete :
  ∀ group → Compact.ValidCompactSimpleIndex group →
  validCompactSimpleIndex? group ≡ true
validCompactSimpleIndexComplete (Compact.SU n) valid =
  natLeBoolComplete 2 n valid
validCompactSimpleIndexComplete (Compact.SOodd n) valid =
  natLeBoolComplete 1 n valid
validCompactSimpleIndexComplete (Compact.SOeven n) valid =
  natLeBoolComplete 3 n valid
validCompactSimpleIndexComplete (Compact.Sp n) valid =
  natLeBoolComplete 1 n valid
validCompactSimpleIndexComplete Compact.G2 valid = refl
validCompactSimpleIndexComplete Compact.F4 valid = refl
validCompactSimpleIndexComplete Compact.E6 valid = refl
validCompactSimpleIndexComplete Compact.E7 valid = refl
validCompactSimpleIndexComplete Compact.E8 valid = refl

validCompactSimpleIndexSound :
  ∀ group → validCompactSimpleIndex? group ≡ true →
  Compact.ValidCompactSimpleIndex group
validCompactSimpleIndexSound (Compact.SU n) valid =
  natLeBoolSound 2 n valid
validCompactSimpleIndexSound (Compact.SOodd n) valid =
  natLeBoolSound 1 n valid
validCompactSimpleIndexSound (Compact.SOeven n) valid =
  natLeBoolSound 3 n valid
validCompactSimpleIndexSound (Compact.Sp n) valid =
  natLeBoolSound 1 n valid
validCompactSimpleIndexSound Compact.G2 valid = tt
validCompactSimpleIndexSound Compact.F4 valid = tt
validCompactSimpleIndexSound Compact.E6 valid = tt
validCompactSimpleIndexSound Compact.E7 valid = tt
validCompactSimpleIndexSound Compact.E8 valid = tt

g1FiniteScopeValidatorLevel : ProofLevel
g1FiniteScopeValidatorLevel = machineChecked
