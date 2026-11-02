{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21WeightedMaxCutFixedNoGraphExact where

------------------------------------------------------------------------
-- KARP WEIGHTED MAX CUT: CONCRETE POSITIVE-W "NO" GRAPH FOR
-- MALFORMED ENCODED SOURCE WORDS IN E20 AND OTHER REDUCTIONS.
--
-- Two vertices, one edge of weight +1, positive required threshold +2.
-- Every Boolean cut has weight either 0 or 1; all four assignments
-- are eliminated by the actual source-owned signed-integer comparator.
--
-- No hypothetical false instance/Boolean status marker is required.
-- Karp (1972), original weighted MAX CUT; DASHI finite graph owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (z≤n)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Int
import Data.Integer.Properties as IntP
import Data.Vec.Base as Vec
import Data.Fin.Base as Fin
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₂)
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as Graph

fixedNoGraph : Cut.WeightedCutGraph 2
fixedNoGraph =
  Cut.graph
    (Cut.edge Fin.zero (Fin.suc Fin.zero) (λ ()) (+ 1) ∷ [])
    (+ 2)
    (Int.+≤+ z≤n , (λ ()))

fixedNoGraphInstance : Graph.GraphInstance
fixedNoGraphInstance = 2 , fixedNoGraph

-- In all four cases, the actual cut score is 0 or 1 < 2.
-- IntP.≤⇒≤ᵇ turns the alleged accepted order into an inhabitant
-- of the impossible concrete Bool predicate (T false).
fixedNoGraphRejects :
  Cut.WeightedMaxCutYES fixedNoGraph → ⊥
fixedNoGraphRejects ((false Vec.∷ false Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)
fixedNoGraphRejects ((false Vec.∷ true Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)
fixedNoGraphRejects ((true Vec.∷ false Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)
fixedNoGraphRejects ((true Vec.∷ true Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)

fixedNoGraphInstanceRejects :
  Cut.WeightedMaxCutYES (proj₂ fixedNoGraphInstance) → ⊥
fixedNoGraphInstanceRejects = fixedNoGraphRejects
