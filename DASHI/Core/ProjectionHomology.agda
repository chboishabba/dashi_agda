module DASHI.Core.ProjectionHomology where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionCategory as PC

----------------------------------------------------------------------
-- ProjectionHomology: what survives grammar change?
--
-- A grammar change Γ → Γ' transports the projection category:
--
--   𝓟Γ → 𝓟Γ'
--
-- Homology measures what persists across this transport.
--
-- Examples:
--   Translation: ATG ↦ Met survives most code grammars,
--                UGA ↦ Stop does not (mitochondrial).
--   TFL:         Which prediction topology survives knot
--                refinement, monotonicity changes?
--   Prot2Prop:   Which latent structures survive all
--                task-head projections?
--   NS surrogate: Which flow structures survive mesh
--                refinement and solver changes?
--   Moonshine:    Which modular/representation structures
--                survive across equivalent construction
--                grammars?
--
-- Category governs admissibility.  Homology measures persistence.
----------------------------------------------------------------------

record ProjectionHomology (G : GGC.GrammarGeneratedCategory) : Set₁ where
  open GGC.GrammarGeneratedCategory G

  field
    -- A morphism (change) between grammar instances
    GrammarMorphism  : (Γ Γ' : Grammar) → Set

    -- Transport: a grammar morphism induces a functor between
    -- projection categories.
    TransportFunctor : ∀ {Γ Γ'} → GrammarMorphism Γ Γ'
                     → PC.ProjectionCategory

    -- Transport: preserves structure
    transportPreservesId     : ∀ {Γ Γ'} (φ : GrammarMorphism Γ Γ')
                              → PC.Obj (𝓟 Γ) → PC.Obj (TransportFunctor φ)
    transportPreservesHom    : ∀ {Γ Γ'} (φ : GrammarMorphism Γ Γ')
                              → ∀ {A B} → PC.Hom (𝓟 Γ) A B
                              → PC.Hom (TransportFunctor φ)
                                  (transportPreservesId φ A)
                                  (transportPreservesId φ B)

    -- Homology: what survives?
    HomologySet : ∀ {Γ Γ'} (φ : GrammarMorphism Γ Γ') → Set

    -- Persistence: an object/morphism belongs to the homology
    -- if its image under the transport is non-trivial.
    persists : ∀ {Γ Γ'} (φ : GrammarMorphism Γ Γ')
             → PC.Obj (𝓟 Γ) → HomologySet φ → Set

    -- Guard
    homologyReading : String

open ProjectionHomology public

----------------------------------------------------------------------
-- Canonical instance (trivial)
----------------------------------------------------------------------

canonicalProjectionHomology : ProjectionHomology
  GGC.canonicalGrammarGeneratedCategory
canonicalProjectionHomology = record
  { GrammarMorphism         = λ _ _ → ⊤
  ; TransportFunctor        = λ _ → PC.canonicalProjectionCategory
  ; transportPreservesId     = λ _ x → x
  ; transportPreservesHom    = λ _ f → f
  ; HomologySet             = λ _ → ⊤
  ; persists                = λ _ _ _ → ⊤
  ; homologyReading          = "Canonical ProjectionHomology: trivial grammar, trivial persistence."
  }
