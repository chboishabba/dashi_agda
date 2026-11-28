module DASHI.Mathematics.Complexity.RecursiveHyperfabricQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.GovernedIndexedResidualCubeExact as Cube
import DASHI.Mathematics.Complexity.PNPHyperfabricConsumerExact as Consumer
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as HT

-- A section lifts an inhabited quotient key; it is not an inverse on X.
-- No physical clock is inferred from the cardinality of a fibre.
record QuotientStep (X K Y : Set) (f : X → Y) (g : K → Y) : Set where
  field
    contract : X → K
    lift : K → X
    section : ∀ k → contract (lift k) ≡ k
    closed : ∀ x → g (contract x) ≡ f x
open QuotientStep public

sameKey : ∀ {X K Y : Set} {f : X → Y} {g : K → Y}
  (q : QuotientStep X K Y f g) x y →
  contract q x ≡ contract q y → f x ≡ f y
sameKey {g = g} q x y e =
  trans (sym (closed q x)) (trans (cong g e) (closed q y))

fibre : ∀ {X K Y : Set} {f : X → Y} {g : K → Y}
  (q : QuotientStep X K Y f g) → K → Bidi.ResidualFibre X
fibre q k x = contract q x ≡ k

fibreInhabited : ∀ {X K Y : Set} {f : X → Y} {g : K → Y}
  (q : QuotientStep X K Y f g) k → fibre q k (lift q k)
fibreInhabited q k = section q k

fibreIdentified : ∀ {X K Y : Set} {f : X → Y} {g : K → Y}
  (q : QuotientStep X K Y f g) k → Bidi.PointIdentifies (fibre q k) f
fibreIdentified q k x y hx hy = sameKey q x y (trans hx (sym hy))

compose : ∀ {X K L Y : Set} {f : X → Y} {g : K → Y} {h : L → Y} →
  QuotientStep X K Y f g → QuotientStep K L Y g h → QuotientStep X L Y f h
compose q r = record
  { contract = λ x → contract r (contract q x)
  ; lift = λ l → lift q (lift r l)
  ; section = λ l → trans (cong (contract r) (section q (lift r l))) (section r l)
  ; closed = λ x → trans (closed r (contract q x)) (closed q x)
  }

-- Declared work and actual measured physical cost are different fields.
-- A caller supplies a physical execution witness and proves its bound.
record PaidStep (X K Y : Set) (f : X → Y) (g : K → Y)
  (Physical : Nat → Set) : Set where
  field
    quotient : QuotientStep X K Y f g
    discovery applyCost liftCost auditCost failedCost : Nat
    rankBefore rankAfter : Nat
    physical : Physical (discovery + applyCost + liftCost + auditCost + failedCost)

module Indexed (X Time Key Decision Version Depth Frob : Set)
  (key : Time → X → Key) (consumer : Time → X → Decision)
  (version : Time → Version) where
  module A = Consumer.Actual X Time Key Decision Version key consumer version

  atIndex : (i : Cube.Index X Time Depth Frob Version)
    (g : Key → Decision)
    (q : QuotientStep X Key Decision (consumer (Cube.Index.time i)) g) →
    (∀ x → contract q x ≡ key (Cube.Index.time i) x) →
    A.indexedClosure i
  atIndex i g q aligns =
    A.preservesToClosure (Cube.Index.time i)
      (λ x y e → sameKey q x y
        (trans (aligns x) (trans e (sym (aligns y))))) (Cube.Index.history i)

-- Exact cube faces transport endpoints; not every residual face closes.
cubeEndpoint : ∀ {c : Cube.Cube} {r : Cube.Faces c} →
  Cube.ExactFaces c r → (x : Cube.A c) → Cube.xyz c x ≡ Cube.zyx c x
cubeEndpoint = Cube.xyz-zyx
