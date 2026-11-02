module DASHI.Mathematics.Complexity.Karp21MichaelLevinGoalExecutionWitnessExact where

------------------------------------------------------------------------
-- MICHAEL LEVIN BIOELECTRIC PROGRAMME: same-goal/different-policy
-- pattern, INSTANTIATED on the actual Karp 1972 signed Max-Cut verifier.
--
-- Reuse the pre-existing DASHI.Biology.Levin.CompetentGoalExecution
-- GoalExecutionSystem and its exact witness constructors. Do not
-- fabricate a new goal system or infer a biological NP solver.
--
-- For every nonempty signed WeightedCutGraph, a binary label vector is
-- a candidate state. Both genuine policies:
--    do nothing / flip every label
-- achieve the same cut score and the same threshold verdict.
-- The policies are distinct on the Policy=Bool carrier, but yield the
-- SAME goal. When a cut has an actual acceptance witness, this
-- constructs the pre-existing GoalUnderdeterminesTrajectoryWitness
-- AND CompetentExecutionWitness records with no Boolean status flags.
--
-- This is a strict finite counterexample to:
--   task success -> unique physical mechanism / computation.
-- It neither constructs a biological physical realisation nor proves
-- a polynomial-cost MAX CUT solution; the initial witness is supplied.
--
-- Historical attribution: Richard Karp (1972), Michael Levin's
-- programme (prior DASHI/Biology/Levin/CompetentGoalExecution owner).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Integer.Base as Int
import Data.Vec.Base as Vec

import DASHI.Biology.Levin.CompetentGoalExecution as Levin
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Lap

-- Policy bits describe actual two distinct lower-level operations:
-- identity and whole-cut complement. Neither consults the threshold.
applyPolicy : ∀ {n} → Bool → Vec.Vec Bool n → Vec.Vec Bool n
applyPolicy false bits = bits
applyPolicy true bits = Lap.flipLabels bits

samePolicy : Bool → Bool → Bool
samePolicy false false = true
samePolicy true true = true
samePolicy false true = false
samePolicy true false = false

module ActualKarpGoalSystem
  {n : Nat}
  (graph : Cut.WeightedCutGraph (suc n))
  where

  -- "Goal" is exact threshold acceptance for this FIXED source graph.
  -- The abstract Levin policy is explicitly instantiated to Bool.
  sameGoalExecution : Levin.GoalExecutionSystem
  sameGoalExecution = record
    { Levin.State = Vec.Vec Bool (suc n)
    ; Levin.Goal = ⊤
    ; Levin.Command = ⊤
    ; Levin.Policy = Bool
    ; Levin.interpret = λ _ → tt
    ; Levin.accept = λ _ _ → true
    ; Levin.discover = λ _ _ → false
    ; Levin.execute = applyPolicy
    ; Levin.satisfies =
        λ bits _ → Cut.verifyWeightedMaxCut graph bits
    ; Levin.samePolicy = samePolicy
    }

  -- Every signed edge crossing survives the true global C2 action.
  flipVerifierInvariant :
    (bits : Vec.Vec Bool (suc n)) →
    Cut.verifyWeightedMaxCut graph (applyPolicy true bits) ≡
    Cut.verifyWeightedMaxCut graph bits
  flipVerifierInvariant bits =
    cong (Int._≤ᵇ_ (Cut.threshold graph))
      (Lap.signedMaxCutGlobalFlipInvariant (Cut.edges graph) bits)

  -- A successful witnessed cut has two DIFFERENT policies, both
  -- successful, giving a real inhabitant of Levin's source theorem.
  goalUnderdeterminesKarpPolicy :
    (bits : Vec.Vec Bool (suc n)) →
    Cut.verifyWeightedMaxCut graph bits ≡ true →
    Levin.GoalUnderdeterminesTrajectoryWitness sameGoalExecution
  goalUnderdeterminesKarpPolicy bits accepted = record
    { Levin.initial = bits
    ; Levin.command = tt
    ; Levin.policy₁ = false
    ; Levin.policy₂ = true
    ; Levin.distinctPolicies = refl
    ; Levin.policy₁Succeeds = accepted
    ; Levin.policy₂Succeeds = trans
        (flipVerifierInvariant bits) accepted
    }

  -- The higher-level command itself does not enumerate or provide the
  -- accepted witness: success depends on the supplied initial state.
  competentGoalExecutionFromAcceptedCut :
    (bits : Vec.Vec Bool (suc n)) →
    Cut.verifyWeightedMaxCut graph bits ≡ true →
    Levin.CompetentExecutionWitness sameGoalExecution
  competentGoalExecutionFromAcceptedCut bits accepted = record
    { Levin.initial = bits
    ; Levin.command = tt
    ; Levin.commandAccepted = refl
    ; Levin.reachesCommandedGoal = accepted
    }
