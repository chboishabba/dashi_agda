{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.Balaban1989LiteralCombinedRGOneStepExact where

------------------------------------------------------------------------
-- LITERAL CMP119/CMP122 DICTIONARY TRAJECTORY HAS THE ACTUAL ONE-STEP LAW
--
-- The source/repository dictionary already states that its scale-indexed state
-- is the actual iteration of Gate4's `next` map:
--
--   state k = stateAt next (state 0) k.
--
-- Therefore the selected source-native trajectory itself satisfies
--
--   state (suc k) = next (state k).
--
-- This matters for composite insertions: the one-step equation to be
-- differentiated is now an actual theorem on the same source-indexed state,
-- not a fresh RG-transition assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.Balaban1989LiteralCombinedRGDictionaryExact as Dictionary
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as RG

literalCombinedRGOneStep :
  ∀ {Coupling Density State Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    {normData : RG.CombinedOneStepPolymerNormData State Bound}
    {admissibility : RG.CombinedRGAdmissibility normData}
    (dictionary : Dictionary.LiteralCombinedRGDictionary admissibility)
    (scale : Nat) →
  Dictionary.state dictionary (suc scale)
  ≡ RG.next normData (Dictionary.state dictionary scale)
literalCombinedRGOneStep {normData = normData} dictionary scale =
  trans
    (Dictionary.trajectory dictionary (suc scale))
    (cong
      (RG.next normData)
      (sym (Dictionary.trajectory dictionary scale)))

literalCombinedRGSuccessorIsActualNextLevel : ProofLevel
literalCombinedRGSuccessorIsActualNextLevel = machineChecked
