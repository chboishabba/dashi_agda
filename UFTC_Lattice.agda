module UFTC_Lattice where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as Eq using (sym; trans; cong)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans; ≤-antisym;
  ⊔-idem; ⊔-comm; ⊔-assoc; ⊔-mono-≤; ⊔-monoˡ-≤; ⊔-monoʳ-≤)
open import Data.Nat using (_≤_; _⊔_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Severity levels (0..9). (You can restrict further if you want Fin 10.)

Severity : Set
Severity = Nat

_⊑_ : Severity → Severity → Set
_⊑_ = _≤_

-- Join = max severity wins.
_⊔s_ : Severity → Severity → Severity
_⊔s_ = _⊔_

------------------------------------------------------------------------
-- Join-semilattice laws (assoc/comm/idempotent).

⊔s-idem : ∀ a → a ⊔s a ≡ a
⊔s-idem a = NatP.⊔-idem a

⊔s-comm : ∀ a b → a ⊔s b ≡ b ⊔s a
⊔s-comm a b = NatP.⊔-comm a b

⊔s-assoc : ∀ a b c → (a ⊔s b) ⊔s c ≡ a ⊔s (b ⊔s c)
⊔s-assoc a b c = NatP.⊔-assoc a b c

------------------------------------------------------------------------
-- Monotonicity of join (the key “max severity wins cannot be masked”).

⊔s-monoˡ : ∀ {a a' b} → a ⊑ a' → (a ⊔s b) ⊑ (a' ⊔s b)
⊔s-monoˡ {a} {a'} {b} a≤a' =
  NatP.⊔-monoˡ-≤ b a≤a'

⊔s-monoʳ : ∀ {a b b'} → b ⊑ b' → (a ⊔s b) ⊑ (a ⊔s b')
⊔s-monoʳ {a} {b} {b'} b≤b' =
  NatP.⊔-monoʳ-≤ a b≤b'

------------------------------------------------------------------------
-- A minimal “code” model: normal trit + special codes with severity.
-- (Map VOID/PARA/META etc. into severity levels.)

data Code : Set where
  normal : Nat → Code               -- placeholder for trits
  special : Severity → Code          -- special failure code with severity

severity : Code → Severity
severity (normal _)    = 0
severity (special sev) = sev

-- Propagation rule: combine codes by max severity.
C_XOR : Code → Code → Code
C_XOR x y = special (severity x ⊔s severity y)

C_ROT : Code → Code
C_ROT x = x  -- rotation doesn't reduce severity (your fast path can refine)

-- Monotone wrt severity preorder:
Monotone₂ : (Code → Code → Code) → Set
Monotone₂ f =
  ∀ x x' y y' →
    severity x ⊑ severity x' →
    severity y ⊑ severity y' →
    severity (f x y) ⊑ severity (f x' y')

C_XOR-monotone : Monotone₂ C_XOR
C_XOR-monotone x x' y y' sx sy =
  NatP.⊔-mono-≤ sx sy

-- Rotation monotonicity (trivial in this stub; replace with your real ROT):
C_ROT-monotone :
  ∀ x x' → severity x ⊑ severity x' → severity (C_ROT x) ⊑ severity (C_ROT x')
C_ROT-monotone x x' sx = sx

------------------------------------------------------------------------
-- Cone interior monotonicity (structured seam).
-- Matches empirical: preserved in the interior, boundary cases allowed.

record ConeInterior {X : Set} : Set₁ where
  field
    InInterior : X → Set
    Boundary   : X → Set

open ConeInterior public

record ConeInteriorPreserved {X : Set} (T : X → X) (C : ConeInterior {X}) : Set₁ where
  field
    preserve :
      ∀ x →
      InInterior C x →
      InInterior C (T x) ⊎ Boundary C (T x)

open ConeInteriorPreserved public
