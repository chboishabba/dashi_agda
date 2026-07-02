module DASHI.Core.ProjectionGrammar where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

----------------------------------------------------------------------
-- ProjectionGrammar: the core abstraction.
--
-- A Grammar (Γ) generates the admissible Hom-space of morphisms
-- from Carrier to Observable.  A Projection is a choice of γ : Γ
-- together with h ∈ HomSpace(γ).
--
--   Grammar  ──→  HomSpace(γ) ⊆ Hom(Carrier, Observable)
--      │
--      │  (grammar change transports morphisms)
--      ▼
--   Grammar'
--
-- This replaces the older "Context" view: Context was always itself
-- a structured carrier (grammar).  The grammar generates the
-- projection space; ContextIndexedEncoding projected a single
-- morphism per context, whereas ProjectionGrammar makes the entire
-- admissible space explicit.
----------------------------------------------------------------------

record ProjectionGrammar : Set₁ where
  field
    -- The hidden object (carrier) and observable target
    Carrier    : Set
    Observable : Set

    -- The grammar that generates the admissible morphism space
    Grammar    : Set

    -- For each grammar instance γ, the set of admissible morphisms
    HomSpace   : Grammar → Set

    -- Apply a morphism to a carrier
    apply      : ∀ {γ} → HomSpace γ → Carrier → Observable

    -- Structure guards (following DASHI conventions)
    forbiddenPromotions : List String
    allowedOperations   : List String
    encodingReading     : String

  -- A projection is a choice of grammar instance γ and admissible morphism h
  Projection : Set
  Projection = Σ Grammar λ γ → HomSpace γ

  -- Evaluate a projection at a carrier
  eval : Projection → Carrier → Observable
  eval (γ , h) = apply h

open ProjectionGrammar public

----------------------------------------------------------------------
-- Canonical instance (all carriers collapsed to ⊤)
----------------------------------------------------------------------

canonicalProjectionGrammar : ProjectionGrammar
canonicalProjectionGrammar = record
  { Carrier             = ⊤
  ; Observable          = ⊤
  ; Grammar             = ⊤
  ; HomSpace            = λ _ → ⊤
  ; apply               = λ _ _ → tt
  ; forbiddenPromotions =
      "noContextIndependentProjection" ∷
      "noCrossGrammarShortcut" ∷ []
  ; allowedOperations   =
      "grammarGeneratedProjection" ∷
      "grammarTransport" ∷
      "residualMeasurement" ∷ []
  ; encodingReading     =
      "Canonical ProjectionGrammar: all types ⊤, Hom-space is trivial. Projection = grammar × hom-space element."
  }

----------------------------------------------------------------------
-- Two-grammar authority
--
-- A projection grammar generates predictions; an authority grammar
-- generates reference measurements or proofs.  The residual compares
-- a projection morphism against an authority morphism on compatible
-- carriers.
----------------------------------------------------------------------

record TwoGrammarAuthority (ProjG AuthG : ProjectionGrammar) : Set₁ where
  field
    -- Bridge from projection carrier to authority carrier
    -- (often they are the same — the hidden object)
    carrierCoercion : Carrier ProjG → Carrier AuthG

    -- The residual compares a projection (grammar + morphism choice)
    -- against an authority morphism.
    residual : Projection ProjG → Projection AuthG → Set

    -- Gate: is the residual controlled/small enough?
    residualControlled : Projection ProjG → Projection AuthG → Bool

    -- Reading
    authorityReading : String

open TwoGrammarAuthority public

canonicalTwoGrammarAuthority : TwoGrammarAuthority
  canonicalProjectionGrammar canonicalProjectionGrammar
canonicalTwoGrammarAuthority = record
  { carrierCoercion    = λ x → x
  ; residual           = λ _ _ → ⊤
  ; residualControlled = λ _ _ → true
  ; authorityReading   =
      "Canonical TwoGrammarAuthority: trivial coercion, trivial residual, gate open."
  }
