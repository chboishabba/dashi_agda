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


  State = Six Value

  record Code : Set where
    constructor code
    field
      source : Six (Fin 6)
      negative : Six Bool
  open Code

  xor : Bool → Bool → Bool
  xor false b = b
  xor true false = true
  xor true true = false

  sign : Bool → Value → Value
  sign false v = v
  sign true v = flip v

  signCompose : (a b : Bool) (v : Value) →
    sign (xor a b) v ≡ sign a (sign b v)
  signCompose false false v = refl
  signCompose false true v = refl
  signCompose true false v = refl
  signCompose true true v = symInvolution v
    where
      sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
      sym refl = refl
      symInvolution : (x : Value) → x ≡ flip (flip x)
      symInvolution x = sym (involution x)

  identity : Code
  identity = code (tabulate (λ i → i)) (tabulate (λ i → false))

  then : Code → Code → Code
  then a b = code
    (tabulate (λ i → lookup (source a) (lookup (source b) i)))
    (tabulate (λ i → xor (lookup (negative b) i)
      (lookup (negative a) (lookup (source b) i))))

  apply : Code → State → State
  apply a v = tabulate (λ i →
    sign (lookup (negative a) i) (lookup v (lookup (source a) i)))

  identityLaw : (z : State) → apply identity z ≡ z
  identityLaw z = sixEta z

  composeLaw : (a b : Code) (z : State) →
    apply (then a b) z ≡ apply b (apply a z)
  composeLaw a b z =
    sixCong (at a b z zero) (at a b z (suc zero))
      (at a b z (suc (suc zero)))
      (at a b z (suc (suc (suc zero))))
      (at a b z (suc (suc (suc (suc zero)))))
      (at a b z (suc (suc (suc (suc (suc zero))))))
    where
      at : (a b : Code) (z : State) (i : Fin 6) →
        lookup (apply (then a b) z) i ≡
        lookup (apply b (apply a z)) i
      at a b z i
        rewrite lookupTabulate
          (λ j → sign (lookup (negative (then a b)) j)
            (lookup z (lookup (source (then a b)) j))) i
          | lookupTabulate
              (λ j → sign (lookup (negative b) j)
                (lookup (apply a z) (lookup (source b) j))) i
          | lookupTabulate
              (λ j → xor (lookup (negative b) j)
                (lookup (negative a) (lookup (source b) j))) i
          | lookupTabulate
              (λ j → lookup (source a) (lookup (source b) j)) i
          | lookupTabulate
              (λ j → sign (lookup (negative a) j)
                (lookup z (lookup (source a) j))) (lookup (source b) i)
          = signCompose (lookup (negative b) i)
              (lookup (negative a) (lookup (source b) i))
              (lookup z (lookup (source a) (lookup (source b) i)))

  module WithAtom (atom : Code) where
    module Collapsed = Binary.Collapsed (apply atom)
      identity atom then apply identityLaw
      (λ z → refl) composeLaw

    binaryCorrect : (n : Binary.Count) (z : State) →
      apply (Collapsed.compile n) z ≡
      Collapsed.E.repeat (Binary.value n) z
    binaryCorrect = Collapsed.correct

  -- Inverses require actual signed-permutation bijectivity. For a
  -- declared pair of inverses, a matrix identity is a *finite receipt*
  -- and it implies both directions of semantic execution exactly.
  record InverseReceipt (a inverse : Code) : Set where
    field
      left : then a inverse ≡ identity
      right : then inverse a ≡ identity

  useInverseLeft : (a inverse : Code) →
    InverseReceipt a inverse → (z : State) →
    apply inverse (apply a z) ≡ z
  useInverseLeft a inverse receipt z =
    trans (symEq (composeLaw a inverse z))
      (trans (congApply (InverseReceipt.left receipt) z)
        (identityLaw z))
    where
      symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
      symEq refl = refl
      trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      trans refl p = p
      congApply : ∀ {x y : Code} → x ≡ y → (z : State) →
        apply x z ≡ apply y z
      congApply refl z = refl

  -- Admitted ten literal/guard actions, independently recoverable by
  -- applying the original two-register endpoint to six basis columns.
  -- The signed entries are DATA, not a target-label oracle in execution.
  f0 : Fin 6
  f0 = zero
  f1 : Fin 6
  f1 = suc zero
  f2 : Fin 6
  f2 = suc (suc zero)
  f3 : Fin 6
  f3 = suc (suc (suc zero))
  f4 : Fin 6
  f4 = suc (suc (suc (suc zero)))
  f5 : Fin 6
  f5 = suc (suc (suc (suc (suc zero))))

  allPositive : Six Bool
  allPositive = six false false false false false false

  translation : Code
  translation = code (six f2 f0 f1 f5 f3 f4) allPositive

  translation² : Code
  translation² = then translation translation

  reflection : Code
  reflection = code (six f0 f2 f1 f3 f5 f4)
    (six false false false true true true)

  negation : Code
  negation = code (six f0 f1 f2 f3 f4 f5)
    (six true true true true true true)

  data Literal : Set where
    a0 a1 a2 b0 b1 b2 j0 j1 n0 n1 : Literal

  literal : Literal → Code
  literal a0 = identity
  literal a1 = translation
  literal a2 = translation²
  literal b0 = identity
  literal b1 = translation
  literal b2 = translation²
  literal j0 = identity
  literal j1 = reflection
  literal n0 = identity
  literal n1 = negation

  inverseLiteral : Literal → Literal
  inverseLiteral a0 = a0
  inverseLiteral a1 = a2
  inverseLiteral a2 = a1
  inverseLiteral b0 = b0
  inverseLiteral b1 = b2
  inverseLiteral b2 = b1
  inverseLiteral j0 = j0
  inverseLiteral j1 = j1
  inverseLiteral n0 = n0
  inverseLiteral n1 = n1

  inverseReceipt : (u : Literal) →
    InverseReceipt (literal u) (literal (inverseLiteral u))
  inverseReceipt a0 = record { left = refl ; right = refl }
  inverseReceipt a1 = record { left = refl ; right = refl }
  inverseReceipt a2 = record { left = refl ; right = refl }
  inverseReceipt b0 = record { left = refl ; right = refl }
  inverseReceipt b1 = record { left = refl ; right = refl }
  inverseReceipt b2 = record { left = refl ; right = refl }
  inverseReceipt j0 = record { left = refl ; right = refl }
  inverseReceipt j1 = record { left = refl ; right = refl }
  inverseReceipt n0 = record { left = refl ; right = refl }
  inverseReceipt n1 = record { left = refl ; right = refl }

  literalRoundtrip : (u : Literal) (z : State) →
    apply (literal (inverseLiteral u)) (apply (literal u) z) ≡ z
  literalRoundtrip u z = useInverseLeft
    (literal u) (literal (inverseLiteral u)) (inverseReceipt u) z
