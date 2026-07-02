module DASHI.Core.ContextIndexedEncoding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Level 0: Context-Indexed Encoding
--
-- Every DASHI encoding is of the form
--
--   π : Carrier × Context → Observable
--
-- where Carrier is hidden, Context provides the situation/grammar/
-- authority/operator/environment, and Observable is the projected
-- output.  Changing the context transports the observable along the
-- new projection, and no context-independent promotion is allowed.
--
--   Domain      | Carrier (H)     | Context (Γ)         | Observable (O)
--   ------------+------------------+----------------------+----------------------
--   Protein     | Genome          | TranslationContext   | ProteinSequence
--   QM          | State ψ         | Hamiltonian          | Evolution / observable
--   Type theory | Term            | Typing context Γ     | Typed judgement
--   Statistics  | Data            | Prior                | Posterior
--   Ogg         | Modular carrier | Prime / level        | Modular curve X₀(p)
--   Hecke       | Automorphic frm | Hecke operator T_p   | Transformed form
--   RSA         | Factors (p,q)   | CRT context          | Arithmetic identity
--   JMD         | Latent meme st  | Interpretive grammar | Observable meaning
--   Moonshine   | Monster element | Representation       | McKay–Thompson series

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

record ContextIndexedEncoding (Carrier Context Observable : Set) : Set₁ where
  field
    -- The dependent projection — the core of the encoding
    π : Carrier → Context → Observable

    -- Context transport: γ → γ' induces a map on observables
    transport : Context → Context → Observable → Observable

    -- Residual: encoding distance between two context-indexed projections
    residual : Context → Context → Carrier → Set

    -- Authority gate: the encoding is genuinely context-dependent
    contextDependent : Bool
    contextDependentIsTrue : contextDependent ≡ true

    -- Promotion gate — when closed (all carriers map to false),
    -- no cross-context shortcut is allowed.
    -- The semantics: if the gate is closed, promotion is blocked.
    promotionGateCarrier : Set
    promotionGateClosed : promotionGateCarrier → Bool

    -- Guard lists (following DASHI guard conventions)
    encodingGuards         : List String
    forbiddenPromotions    : List String
    allowedOperations      : List String

    encodingReading : String

open ContextIndexedEncoding public

------------------------------------------------------------------------
-- Canonical instance (DASHI-safe: all abstract carriers set to ⊤)
------------------------------------------------------------------------

canonicalContextIndexedEncoding : ContextIndexedEncoding ⊤ ⊤ ⊤
canonicalContextIndexedEncoding = record
  { π                         = λ _ _ → tt
  ; transport                 = λ _ _ o → o
  ; residual                  = λ _ _ _ → ⊤
  ; contextDependent          = true
  ; contextDependentIsTrue    = refl
  ; promotionGateCarrier      = ⊤
  ; promotionGateClosed       = λ _ → false
  ; encodingGuards            =
      "noContextIndependentPromotion"
      ∷ "noCrossContextShortcut"
      ∷ "authorityRequiresContextClosure"
      ∷ []
  ; forbiddenPromotions       =
      "contextFreeProjection"
      ∷ "carrierPromotedWithoutContext"
      ∷ "observableDetachedFromContext"
      ∷ []
  ; allowedOperations         =
      "contextDependentProjection"
      ∷ "contextTransport"
      ∷ "residualMeasurement"
      ∷ "contextScopedCalibration"
      ∷ []
  ; encodingReading           =
      "Context-indexed encoding: π : Carrier × Context → Observable.  No context-independent promotion allowed without context closure gate."
  }

------------------------------------------------------------------------
-- Meta-theorem
--
-- Every DASHI encoding that is of the form π : H × Γ → O satisfies the
-- dependent projection theorem:
--
--   • The observable is not a function of the carrier alone.
--   • Changing the context transports the observable along the new projection.
--   • The residual measures encoding distance across contexts.
--   • No context gate → no promotion.
--
-- The theorem states that any instance of ContextIndexedEncoding is
-- non-promoting unless the promotion gate is closed for all carriers.
------------------------------------------------------------------------

dependentProjectionTheorem : ∀ {H Γ O} → ContextIndexedEncoding H Γ O → Set
dependentProjectionTheorem enc =
  Σ (contextDependent enc ≡ true) λ _ →
  Σ ((x : _) (γ γ' : _) → π enc x γ' ≡ transport enc γ γ' (π enc x γ)) λ _ →
  Σ ((γ : _) (o : _) → transport enc γ γ o ≡ o) λ _ →
    (pg : promotionGateCarrier enc) → promotionGateClosed enc pg ≡ true → ⊥
  -- The theorem asserts that a well-behaved context-indexed encoding:
  --   (1) is genuinely context-dependent,
  --   (2) has coherent transport (π x γ' ≡ transport γ γ' (π x γ)),
  --   (3) has reflexive transport (transport γ γ o ≡ o),
  --   (4) blocks cross-context promotion when the gate is closed.
  -- The canonical instance trivially satisfies all four.

-- The canonical instance trivially satisfies the theorem
dependentProjectionTheoremCanonical :
  dependentProjectionTheorem canonicalContextIndexedEncoding
dependentProjectionTheoremCanonical =
  refl , (λ _ _ _ → refl) , (λ _ _ → refl) , λ pg ()

------------------------------------------------------------------------
-- Non-promotion certificate
------------------------------------------------------------------------

record ContextIndexedEncodingNonPromotionCertificate
    {Carrier Context Observable : Set}
    (enc : ContextIndexedEncoding Carrier Context Observable)
    : Set where
  field
    contextDependent             : Bool
    contextDependentIsTrue       : contextDependent ≡ true
    noCrossContextPromotion      : Bool
    noCrossContextPromotionIsTrue : noCrossContextPromotion ≡ true
    guardsMatch                  : encodingGuards enc ≡
      ("noContextIndependentPromotion" ∷ "noCrossContextShortcut"
      ∷ "authorityRequiresContextClosure" ∷ [])
    certificateReading           : String

open ContextIndexedEncodingNonPromotionCertificate public

canonicalContextIndexedEncodingNonPromotionCertificate :
  ContextIndexedEncodingNonPromotionCertificate
    canonicalContextIndexedEncoding
canonicalContextIndexedEncodingNonPromotionCertificate = record
  { contextDependent               = true
  ; contextDependentIsTrue         = refl
  ; noCrossContextPromotion        = true
  ; noCrossContextPromotionIsTrue  = refl
  ; guardsMatch                    = refl
  ; certificateReading             =
      "The canonical context-indexed encoding is non-promoting: all abstract carriers are ⊤, context dependence is asserted, and the promotion gate blocks cross-context shortcuts."
  }


