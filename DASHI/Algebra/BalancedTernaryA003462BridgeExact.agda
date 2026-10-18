module DASHI.Algebra.BalancedTernaryA003462BridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using ([]; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Wikimedia.IbrahimA003462BalancedTernaryResidualCodecSnowballExact as A003462

------------------------------------------------------------------------
-- Reconcile the new integer owner with the repository's earlier A003462
-- frontier.  That earlier owner correctly left reconstruction / uniqueness
-- unpaid; this bridge reuses its finite magnitude coordinate rather than
-- introducing another bound sequence.

maxMagnitude : Nat → Nat
maxMagnitude = A003462.balancedTernaryMaxMagnitude

oneTritMagnitude : maxMagnitude 1 ≡ 1
oneTritMagnitude = A003462.oneTritMax

twoTritMagnitude : maxMagnitude 2 ≡ 4
twoTritMagnitude = A003462.twoTritMax

threeTritMagnitude : maxMagnitude 3 ≡ 13
threeTritMagnitude = A003462.threeTritMax

threePositiveTritEvaluationMatchesA003462Magnitude :
  BT.positiveWeight
    (BT.eval (Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ []))
  ≡ maxMagnitude 3
threePositiveTritEvaluationMatchesA003462Magnitude = refl

record BalancedTernaryA003462Boundary : Set where
  constructor balancedTernaryA003462Boundary
  field
    existingMagnitudeSequenceReused : Bool
    threeTritExtremumWelded : Bool
    generalReconstructionBijectionPaidHere : Bool
    generalUniquenessPaidHere : Bool

canonicalBalancedTernaryA003462Boundary : BalancedTernaryA003462Boundary
canonicalBalancedTernaryA003462Boundary =
  balancedTernaryA003462Boundary true true false false
