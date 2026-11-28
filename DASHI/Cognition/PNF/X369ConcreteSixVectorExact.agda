module DASHI.Cognition.PNF.X369ConcreteSixVectorExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- NO functional-extensionality premise: six cells are a constructor,
-- and pointwise equality is converted to equality by six patterns.
open import Agda.Builtin.Fin using (Fin; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Cognition.PNF.X369BinaryBlockExecutionExact as Binary
import DASHI.Cognition.PNF.X369SignedSixBlockBackendExact as Signed

data Six (A : Set) : Set where
  six : A → A → A → A → A → A → Six A

lookup : ∀ {A} → Six A → Fin 6 → A
lookup (six a b c d e f) zero = a
lookup (six a b c d e f) (suc zero) = b
lookup (six a b c d e f) (suc (suc zero)) = c
lookup (six a b c d e f) (suc (suc (suc zero))) = d
lookup (six a b c d e f) (suc (suc (suc (suc zero)))) = e
lookup (six a b c d e f) (suc (suc (suc (suc (suc zero))))) = f

tabulate : ∀ {A} → (Fin 6 → A) → Six A
tabulate f =
  six (f zero) (f (suc zero)) (f (suc (suc zero)))
    (f (suc (suc (suc zero))))
    (f (suc (suc (suc (suc zero)))))
    (f (suc (suc (suc (suc (suc zero))))))

lookupTabulate : ∀ {A} (f : Fin 6 → A) (i : Fin 6) →
  lookup (tabulate f) i ≡ f i
lookupTabulate f zero = refl
lookupTabulate f (suc zero) = refl
lookupTabulate f (suc (suc zero)) = refl
lookupTabulate f (suc (suc (suc zero))) = refl
lookupTabulate f (suc (suc (suc (suc zero)))) = refl
lookupTabulate f (suc (suc (suc (suc (suc zero))))) = refl

sixCong : ∀ {A} {a b c d e f a' b' c' d' e' f' : A} →
  a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f' →
  six a b c d e f ≡ six a' b' c' d' e' f'
sixCong refl refl refl refl refl refl = refl

tabulateExt : ∀ {A} {f g : Fin 6 → A} →
  ((i : Fin 6) → f i ≡ g i) → tabulate f ≡ tabulate g
tabulateExt p =
  sixCong (p zero) (p (suc zero)) (p (suc (suc zero)))
    (p (suc (suc (suc zero))))
    (p (suc (suc (suc (suc zero)))))
    (p (suc (suc (suc (suc (suc zero))))))

sixEta : ∀ {A} (v : Six A) → tabulate (lookup v) ≡ v
sixEta (six a b c d e f) = refl

-- The same six-slot geometry previously required a function extensionality
-- premise. This instance instead exposes concrete vector equality.
module Carrier {Value : Set}
  (flip : Value → Value)
  (involution : (v : Value) → flip (flip v) ≡ v) where

