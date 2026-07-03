module DASHI.Core.GrammarGeneratedCategory where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC

----------------------------------------------------------------------
-- GrammarGeneratedCategory: a grammar Γ generates a projection
-- category 𝓟Γ.
--
--   Γ ↦ 𝓟Γ
--
-- The grammar is the structured object (simulation context, molecular
-- machinery, representation theory data, lattice geometry, etc.)
-- that determines the admissible objects and morphisms of the
-- projection category.
----------------------------------------------------------------------

record GrammarGeneratedCategory : Set₁ where
  field
    Grammar : Set
    𝓟       : Grammar → PC.ProjectionCategory

  -- Recover the Hom-space for a specific grammar instance
  HomSpace : (γ : Grammar) (A B : PC.Obj (𝓟 γ)) → Set
  HomSpace γ A B = PC.Hom (𝓟 γ) A B

  -- Guards
  field
    grammarReading : String

open GrammarGeneratedCategory public

----------------------------------------------------------------------
-- Canonical instance (trivial grammar, trivial category)
----------------------------------------------------------------------

canonicalGrammarGeneratedCategory : GrammarGeneratedCategory
canonicalGrammarGeneratedCategory = record
  { Grammar        = ⊤
  ; 𝓟              = λ _ → PC.canonicalProjectionCategory
  ; grammarReading = "Canonical GrammarGeneratedCategory: trivial grammar, trivial projection category."
  }
