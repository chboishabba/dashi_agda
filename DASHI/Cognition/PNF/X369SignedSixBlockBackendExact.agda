module DASHI.Cognition.PNF.X369SignedSixBlockBackendExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Concrete SIX-slot signed-index execution, with explicit value involution.
-- This is fixed-size action composition, NOT a native Torch equivalence.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F
import DASHI.Cognition.PNF.X369BinaryBlockExecutionExact as Binary

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

module SignedSix {Value : Set}
  (flip : Value → Value)
  (flipInvolutive : (v : Value) → flip (flip v) ≡ v)
  -- Finite-index function equality is stated explicitly; no unproved
  -- global functional extensionality or conversion of pointwise to equal
  -- bytes is assumed by the X369 compiler.
  (sixExt : {f g : Fin 6 → Value} →
    ((i : Fin 6) → f i ≡ g i) → f ≡ g) where

  State : Set
  State = Fin 6 → Value

  record Code : Set where
    constructor code
    field
      source : Fin 6 → Fin 6
      negative : Fin 6 → Bool
  open Code

  sign : Bool → Value → Value
  sign false v = v
  sign true v = flip v

  signCompose : (a b : Bool) (v : Value) →
    sign (xor a b) v ≡ sign a (sign b v)
  signCompose false false v = refl
  signCompose false true v = refl
  signCompose true false v = refl
  signCompose true true v = flipInvolutive v

  identity : Code
  identity = code (λ i → i) (λ i → false)

  then : Code → Code → Code
  then a b = code
    (λ i → source a (source b i))
    (λ i → xor (negative b i) (negative a (source b i)))

  apply : Code → State → State
  apply a v i = sign (negative a i) (v (source a i))

  identityLaw : (z : State) → apply identity z ≡ z
  identityLaw z = sixExt (λ i → refl)

  composeLaw : (a b : Code) (z : State) →
    apply (then a b) z ≡ apply b (apply a z)
  composeLaw a b z =
    sixExt (λ i → signCompose (negative b i)
      (negative a (source b i)) (z (source a (source b i))))

  -- A concrete atom is supplied by a verified source ten-literal table.
  -- Arbitrary index maps are admitted for closure; bijectivity is a
  -- separate inverse receipt, not implied by these three laws.
  module WithAtom (atom : Code) where
    module C = Binary.Collapsed (apply atom)
      identity atom then apply identityLaw
      (λ z → refl) composeLaw

    binaryExact : (n : Binary.Count) (z : State) →
      apply (C.compile n) z ≡ C.E.repeat (Binary.value n) z
    binaryExact = C.correct
