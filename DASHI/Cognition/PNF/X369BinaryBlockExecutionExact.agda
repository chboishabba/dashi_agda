module DASHI.Cognition.PNF.X369BinaryBlockExecutionExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Binary syntax represents a repetition count without unary expansion.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

data Count : Set where
  end : Count
  even odd : Count → Count

value : Count → Nat
value end = zero
value (even b) = value b + value b
value (odd b) = suc (value b + value b)

module Execution {State : Set} (f : State → State) where
  repeat : Nat → State → State
  repeat zero z = z
  repeat (suc n) z = repeat n (f z)

  appendRepeat : (m n : Nat) (z : State) →
    repeat (m + n) z ≡ repeat n (repeat m z)
  appendRepeat zero n z = refl
  appendRepeat (suc m) n z = appendRepeat m n (f z)

  -- Explicit composition tree; a finite signed-permutation backend
  -- can collapse each node to a fixed-size action.
  data Tree : Set where
    identity atom : Tree
    then : Tree → Tree → Tree

  run : Tree → State → State
  run identity z = z
  run atom z = f z
  run (then a b) z = run b (run a z)

  compile : Count → Tree
  compile end = identity
  compile (even b) = then (compile b) (compile b)
  compile (odd b) = then atom (then (compile b) (compile b))

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

  correct : (b : Count) (z : State) →
    repeat (value b) z ≡ run (compile b) z
  correct end z = refl
  correct (even b) z =
    trans (appendRepeat (value b) (value b) z)
      (trans (correct b (repeat (value b) z))
        (F.cong (run (compile b)) (correct b z)))
  correct (odd b) z =
    trans (appendRepeat (value b) (value b) (f z))
      (trans (correct b (repeat (value b) (f z)))
        (F.cong (run (compile b)) (correct b (f z))))

-- Shared compilation schedule counts one doubling and at most one
-- extra composition per digit. The expanded Tree above is not itself
-- a proof of logarithmic evaluation cost without sharing/collapse.
digits : Count → Nat
digits end = zero
digits (even b) = suc (digits b)
digits (odd b) = suc (digits b)

compositions : Count → Nat
compositions end = zero
compositions (even b) = suc (compositions b)
compositions (odd b) = suc (suc (compositions b))

-- Actual collapsed carrier: the two copies of the recursive result
-- share one compiled value. The composition law is the backend premise.
module Collapsed {State Code : Set}
  (f : State → State)
  (identity atom : Code)
  (then : Code → Code → Code)
  (apply : Code → State → State)
  (identityLaw : (z : State) → apply identity z ≡ z)
  (atomLaw : (z : State) → apply atom z ≡ f z)
  (composeLaw : (a b : Code) (z : State) →
    apply (then a b) z ≡ apply b (apply a z)) where

  module E = Execution f

  compile : Count → Code
  compile end = identity
  compile (even b) = let c = compile b in then c c
  compile (odd b) = let c = compile b in then atom (then c c)

  sound : (b : Count) (z : State) →
    apply (compile b) z ≡ E.run (E.compile b) z
  sound end z = identityLaw z
  sound (even b) z =
    E.trans (composeLaw (compile b) (compile b) z)
      (E.trans (sound b (apply (compile b) z))
        (F.cong (E.run (E.compile b)) (sound b z)))
  sound (odd b) z =
    E.trans (composeLaw atom (then (compile b) (compile b)) z)
      (E.trans (composeLaw (compile b) (compile b) (apply atom z))
        (E.trans (sound b (apply (compile b) (apply atom z)))
          (E.trans (F.cong (E.run (E.compile b)) (sound b (apply atom z)))
            (F.cong (λ x → E.run (E.compile b) (E.run (E.compile b) x))
              (atomLaw z)))))

  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  correct : (b : Count) (z : State) →
    apply (compile b) z ≡ E.repeat (value b) z
  correct b z = E.trans (sound b z) (sym (E.correct b z))


-- Exact charged count for the SHARED collapsed schedule. Its operator
-- executions do not expand the Tree; each digit makes one square and
-- every set digit up to one additional composition.
ones : Count → Nat
ones end = zero
ones (even b) = ones b
ones (odd b) = suc (ones b)

compositionsExact : (b : Count) →
  compositions b ≡ digits b + ones b
compositionsExact end = refl
compositionsExact (even b) =
  F.cong suc (compositionsExact b)
compositionsExact (odd b)
  rewrite N.+-suc (digits b) (ones b) =
  F.cong (λ n → suc (suc n)) (compositionsExact b)

weaken : ∀ {m n} → m ≤ n → m ≤ suc n
weaken z≤n = z≤n
weaken (s≤s p) = s≤s (weaken p)

onesAtMostDigits : (b : Count) → ones b ≤ digits b
onesAtMostDigits end = z≤n
onesAtMostDigits (even b) = weaken (onesAtMostDigits b)
onesAtMostDigits (odd b) = s≤s (onesAtMostDigits b)

plusMonoRight : (m : Nat) {n k : Nat} →
  n ≤ k → m + n ≤ m + k
plusMonoRight zero p = p
plusMonoRight (suc m) p = s≤s (plusMonoRight m p)

transportBound : ∀ {m n k} → m ≡ n → n ≤ k → m ≤ k
transportBound refl p = p

twiceDigitsBound : (b : Count) →
  compositions b ≤ digits b + digits b
twiceDigitsBound b =
  transportBound (compositionsExact b)
    (plusMonoRight (digits b) (onesAtMostDigits b))

-- This bound charges abstract fixed-size compositions, not the cost of
-- arbitrary-precision chronological value payloads or GPU kernels.
