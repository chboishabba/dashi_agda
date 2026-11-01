module DASHI.Geometry.Isotropy where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Ultrametric as UMetric

record Group (G : Set) : Set₁ where
  field
    _∙_  : G → G → G
    e    : G
    inv  : G → G
    assoc : ∀ a b c → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
    idL   : ∀ a → e ∙ a ≡ a
    invL  : ∀ a → (inv a) ∙ a ≡ e

record Isotropy
       {S : Set}
       (U : UMetric.Ultrametric S)
       (T : S → S)
       : Set₁ where

  open UMetric.Ultrametric U
  field
    G      : Set
    group  : Group G
    act    : G → S → S
    preservesMetric :
      ∀ g x y → d (act g x) (act g y) ≡ d x y
    commutesWithT :
      ∀ g x → T (act g x) ≡ act g (T x)

-- Trivial isotropy: one element group acting by identity.
trivialIsotropy :
  ∀ {S : Set} (U : UMetric.Ultrametric S) (T : S → S) →
  Isotropy U T
trivialIsotropy U T =
  record
    { G = ⊤
    ; group = record
        { _∙_ = λ _ _ → tt
        ; e = tt
        ; inv = λ _ → tt
        ; assoc = λ _ _ _ → refl
        ; idL = λ _ → refl
        ; invL = λ _ → refl
        }
    ; act = λ _ x → x
    ; preservesMetric = λ _ _ _ → refl
    ; commutesWithT = λ _ _ → refl
    }

