{-# OPTIONS --safe #-}
module DASHI.Unified.NeuralActivationTransportTOEExact where

-- Thin proof-bearing TOE adapter; does not overwrite central import surfaces.
-- Source inspiration: DASHI.Combinatorics.TriadicVideoCodecObservationQuotient.
-- Concrete proofs owned by DASHI.Codec.NeuralActivationStateTransportExact
-- and DASHI.Codec.NeuralActivationStreamRegressionExact.

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

import DASHI.Codec.NeuralActivationStateTransportExact as Transport
import DASHI.Codec.NeuralActivationStreamRegressionExact as Stream

inference-transport-invariant : ∀ {n} (S : Transport.ActivationStream n)
  (s : Transport.Context S) (x : Vec Bool n) →
  Transport.decode S s (Transport.encode S s x) ≡ x
inference-transport-invariant = Transport.decode-encode

downstream-observer-invariant : ∀ {B : Set}
  (f : Vec Bool Stream.width → B)
  (s : Stream.Session) (x : Vec Bool Stream.width) →
  f (Transport.decode Stream.stream s
       (Transport.encode Stream.stream s x)) ≡ f x
downstream-observer-invariant = Stream.downstream-congruence
