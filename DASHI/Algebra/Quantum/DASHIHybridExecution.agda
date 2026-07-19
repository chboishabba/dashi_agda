module DASHI.Algebra.Quantum.DASHIHybridExecution where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Quantum.DASHIQuantumBridge

------------------------------------------------------------------------
-- A DASHI-controlled quantum round:
--
--   semantic state
--     -> compile/lift
--     -> reversible wave transport
--     -> observe
--     -> certified semantic contraction.
--
-- The crucial bridge law states that observed transport agrees with the
-- certified DASHI step.  MDL descent then follows from the existing proof.
------------------------------------------------------------------------

record HybridExecution
    (D : StrictDescentSystem)
    (B : CertifiedQuantumBridge D) : Set₁ where
  field
    observedTransportIsStep :
      ∀ s → waveThenObserve D B s ≡ step D s

open HybridExecution public

hybridStep :
  (D : StrictDescentSystem) →
  (B : CertifiedQuantumBridge D) →
  HybridExecution D B →
  State D →
  State D
hybridStep D B H = waveThenObserve D B

hybridStep-agrees-with-DASHI :
  (D : StrictDescentSystem) →
  (B : CertifiedQuantumBridge D) →
  (H : HybridExecution D B) →
  ∀ s → hybridStep D B H s ≡ step D s
hybridStep-agrees-with-DASHI D B H = observedTransportIsStep H

hybrid-codeLength-descent :
  (D : StrictDescentSystem) →
  (B : CertifiedQuantumBridge D) →
  (H : HybridExecution D B) →
  ∀ s → codeLength D (hybridStep D B H s) ≤ codeLength D s
hybrid-codeLength-descent D B H s
  rewrite hybridStep-agrees-with-DASHI D B H s =
  codeLengthDescent D s

------------------------------------------------------------------------
-- Iterated hybrid execution.
------------------------------------------------------------------------

iterate : ∀ {A : Set} → Nat → (A → A) → A → A
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

hybrid-iterate :
  (D : StrictDescentSystem) →
  (B : CertifiedQuantumBridge D) →
  HybridExecution D B →
  Nat →
  State D →
  State D
hybrid-iterate D B H n = iterate n (hybridStep D B H)
