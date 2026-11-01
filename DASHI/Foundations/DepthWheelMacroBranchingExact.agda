module DASHI.Foundations.DepthWheelMacroBranchingExact where

------------------------------------------------------------------------
-- ONE-WHEEL BRANCH MULTIPLICITY
--
-- Exact finite separation requested by the depth-wheel analysis:
--   6 = 2*3 and 9 = 3*3 are local state x phase carrier sizes;
--   8 = 2^3 and 27 = 3^3 are branches generated over one complete wheel.
-- These are differently typed constructions, not interchangeable numerology.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_*_)

localStatePhaseCardinality : Nat → Nat
localStatePhaseCardinality stateCardinality = stateCardinality * 3

oneWheelBranchMultiplicity : Nat → Nat
oneWheelBranchMultiplicity branchingPerPhase =
  branchingPerPhase * branchingPerPhase * branchingPerPhase

polarLocalPhaseIs6 : localStatePhaseCardinality 2 ≡ 6
polarLocalPhaseIs6 = refl

ternaryLocalPhaseIs9 : localStatePhaseCardinality 3 ≡ 9
ternaryLocalPhaseIs9 = refl

polarOneWheelIs8 : oneWheelBranchMultiplicity 2 ≡ 8
polarOneWheelIs8 = refl

ternaryOneWheelIs27 : oneWheelBranchMultiplicity 3 ≡ 27
ternaryOneWheelIs27 = refl

record MacroBranchingProfile : Set where
  constructor macroBranchingProfile
  field
    perPhaseBranching : Nat
    localPhaseCarrier : Nat
    macroBranches : Nat
    localExact : localPhaseCarrier ≡ perPhaseBranching * 3
    macroExact :
      macroBranches ≡ perPhaseBranching * perPhaseBranching * perPhaseBranching

polarMacroBranchingProfile : MacroBranchingProfile
polarMacroBranchingProfile = macroBranchingProfile 2 6 8 refl refl

ternaryMacroBranchingProfile : MacroBranchingProfile
ternaryMacroBranchingProfile = macroBranchingProfile 3 9 27 refl refl
