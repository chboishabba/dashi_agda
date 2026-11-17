{-# OPTIONS --safe #-}
module DASHI.Codec.NeuralActivationDAGTransportExact where

-- Concrete finite compositional transport lemma, with no assumptions about
-- activation repetition, entropy reduction, or physical network performance.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)
import DASHI.Codec.NeuralActivationStateTransportExact as Codec

-- Replacing a single typed graph edge by the exact transport codec cannot
-- change the result seen by an arbitrary downstream function.
edge-substitution : ∀ {n} {B : Set} (S : Codec.ActivationStream n)
  (s : Codec.Context S) (x : Vec Bool n) (consumer : Vec Bool n → B) →
  consumer (Codec.decode S s (Codec.encode S s x))
    ≡ consumer x
edge-substitution S s x consumer =
  cong consumer (Codec.decode-encode S s x)

-- A composed two-edge path preserves downstream observations, even when
-- the two edges use different widths, contexts and codec predictors.
two-edge-substitution : ∀ {n m} {B : Set}
  (S : Codec.ActivationStream n)
  (T : Codec.ActivationStream m)
  (s : Codec.Context S) (t : Codec.Context T)
  (x : Vec Bool n) (step : Vec Bool n → Vec Bool m)
  (observe : Vec Bool m → B) →
  observe (Codec.decode T t
    (Codec.encode T t
      (step (Codec.decode S s (Codec.encode S s x)))))
    ≡ observe (step x)
two-edge-substitution S T s t x step observe =
  trans
    (cong observe (Codec.decode-encode T t
      (step (Codec.decode S s (Codec.encode S s x)))))
    (cong (λ z → observe (step z)) (Codec.decode-encode S s x))

-- A parallel fan-out uses the same canonical input on both branches.
-- Replacing the transport on each branch preserves any join function.
fork-join-substitution : ∀ {n} {B C D : Set}
  (S : Codec.ActivationStream n)
  (s : Codec.Context S) (x : Vec Bool n)
  (left : Vec Bool n → B) (right : Vec Bool n → C)
  (join : B → C → D) →
  join (left (Codec.decode S s (Codec.encode S s x)))
       (right (Codec.decode S s (Codec.encode S s x)))
    ≡ join (left x) (right x)
fork-join-substitution S s x left right join
  rewrite Codec.decode-encode S s x = refl
