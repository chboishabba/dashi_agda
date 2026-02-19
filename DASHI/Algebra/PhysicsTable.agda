module DASHI.Algebra.PhysicsTable where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)

open import DASHI.Algebra.PhysicsSignature using (Sig15; sig15)

-- State is literally an enumeration of the witness inputs
data State : Set where
  s0 s1 s2 s3 s4 : State
  -- add as many as your computed witness set needs

-- The witness list you claim coverage on
vectors : List State
vectors = s0 ∷ s1 ∷ s2 ∷ s3 ∷ s4 ∷ []

-- Implementation signature (paste from computed output)
implSig : State → Sig15
implSig s0 = sig15 true false false true  false  true  false false true  false false true  false true  false
implSig s1 = sig15 false false true  true  false false true  false true  false true  false false true  true
implSig s2 = sig15 true true  false false true  false false true  false true  false false true  false true
implSig s3 = sig15 false true  false true  true  true  false false false true  true  false true  false false
implSig s4 = sig15 true false true  false true  false true  false true  false true  false true  false true

-- Spec signature: either definitional (preferred), or also tabled.
-- If you can’t define it yet, you can table it too (still honest).
specSig : State → Sig15
specSig = implSig
