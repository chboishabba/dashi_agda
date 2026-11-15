{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21FractranPriorityFrontierExact where

------------------------------------------------------------------------
-- Karp / FRACDASH reusable machine cut.
--
-- FRACDASH: compiled fraction denominator requirements become Boolean
-- enabled guards; the FIRST enabled rule (not an arbitrary enabled rule)
-- applies its signed delta. An incremental frontier may reuse a guard
-- only when a source-supplied independence theorem certifies it stable.
--
-- This is a fully generic priority-cache correctness proof. It DOES NOT
-- instantiate the original N21 reader, machine clock, or PR.InNP.
-- No prime-power integers, Peano magnitude execution, or oracle guards.
--
-- Provenance: chboishabba/FRACDASH architecture.md and
-- BRIDGE_CORRECTNESS.md (compiled priority / delta semantics).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

module Machine
  (State Rule : Set)
  (enabled : Rule → State → Bool)
  (apply : Rule → State → State)
  (affected : Rule → State → State → Bool)
  (unaffected-stable :
    ∀ r before after →
    affected r before after ≡ false →
    enabled r before ≡ enabled r after)
  where

  Cache : Set
  Cache = List (Rule × Bool)

  populate : List Rule → State → Cache
  populate [] state = []
  populate (rule ∷ rules) state =
    (rule , enabled rule state) ∷ populate rules state

  -- Unlike a full population, the false branch reuses its cached bit.
  refreshEntry : Rule → Bool → State → State → Bool
  refreshEntry rule cached before after with affected rule before after
  ... | true = enabled rule after
  ... | false = cached

  refreshCache : Cache → State → State → Cache
  refreshCache [] before after = []
  refreshCache ((rule , bit) ∷ rest) before after =
    (rule , refreshEntry rule bit before after) ∷
    refreshCache rest before after

  refreshEntryCorrect :
    ∀ rule before after →
    refreshEntry rule (enabled rule before) before after
      ≡ enabled rule after
  refreshEntryCorrect rule before after
    with affected rule before after in guard
  ... | true = refl
  ... | false = unaffected-stable rule before after guard

  -- An exactly populated cache remains exact under selective refresh.
  refreshPopulationCorrect :
    ∀ rules before after →
    refreshCache (populate rules before) before after
      ≡ populate rules after
  refreshPopulationCorrect [] before after = refl
  refreshPopulationCorrect (rule ∷ rules) before after =
    cong₂ _∷_
      (cong (λ b → rule , b)
        (refreshEntryCorrect rule before after))
      (refreshPopulationCorrect rules before after)

  -- The same theorem for a persistent cache, given its prior receipt.
  refreshStoredCorrect :
    ∀ rules cached before after →
    cached ≡ populate rules before →
    refreshCache cached before after ≡ populate rules after
  refreshStoredCorrect rules cached before after exact =
    trans
      (cong (λ c → refreshCache c before after) exact)
      (refreshPopulationCorrect rules before after)

  -- Standard ordered FRACTRAN priority: first enabled, not any enabled.
  firstEnabled : List Rule → State → Maybe Rule
  firstEnabled [] state = nothing
  firstEnabled (rule ∷ rest) state with enabled rule state
  ... | true = just rule
  ... | false = firstEnabled rest state

  firstCached : Cache → Maybe Rule
  firstCached [] = nothing
  firstCached ((rule , true) ∷ rest) = just rule
  firstCached ((rule , false) ∷ rest) = firstCached rest

  firstPopulatedCorrect :
    ∀ rules state →
    firstCached (populate rules state) ≡ firstEnabled rules state
  firstPopulatedCorrect [] state = refl
  firstPopulatedCorrect (rule ∷ rest) state
    with enabled rule state
  ... | true = refl
  ... | false = firstPopulatedCorrect rest state

  -- Incremental frontier cannot reorder first-enabled priority.
  firstRefreshedCorrect :
    ∀ rules cached before after →
    cached ≡ populate rules before →
    firstCached (refreshCache cached before after)
      ≡ firstEnabled rules after
  firstRefreshedCorrect rules cached before after exact =
    trans
      (cong firstCached
        (refreshStoredCorrect rules cached before after exact))
      (firstPopulatedCorrect rules after)

  executeChosen : Maybe Rule → State → Maybe State
  executeChosen nothing state = nothing
  executeChosen (just rule) state = just (apply rule state)

  directStep : List Rule → State → Maybe State
  directStep rules state =
    executeChosen (firstEnabled rules state) state

  cachedStep : Cache → State → Maybe State
  cachedStep cached state =
    executeChosen (firstCached cached) state

  -- Same selected operation and same successor/halt for ANY rule list.
  cachedStepCorrect :
    ∀ rules cached before after →
    cached ≡ populate rules before →
    cachedStep (refreshCache cached before after) after
      ≡ directStep rules after
  cachedStepCorrect rules cached before after exact =
    cong (λ choice → executeChosen choice after)
      (firstRefreshedCorrect rules cached before after exact)
