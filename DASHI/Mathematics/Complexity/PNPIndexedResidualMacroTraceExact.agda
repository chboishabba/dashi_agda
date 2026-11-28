{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.PNPIndexedResidualMacroTraceExact where

-- Concrete finite Boolean violation vector: no target changes, no oracle.
-- Uses the existing basin descent convention of a fixed Nat potential,
-- but allows neutral/damaging legal prefixes inside a certified macro.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

violations : ∀ {m} → Vec Bool m → Nat
violations [] = zero
violations (false ∷ v) = violations v
violations (true ∷ v) = suc (violations v)

repairs : ∀ {m} → Vec Bool m → Vec Bool m → Nat
repairs [] [] = zero
repairs (true ∷ x) (false ∷ y) = suc (repairs x y)
repairs (false ∷ x) (false ∷ y) = repairs x y
repairs (false ∷ x) (true ∷ y) = repairs x y
repairs (true ∷ x) (true ∷ y) = repairs x y

damage : ∀ {m} → Vec Bool m → Vec Bool m → Nat
damage [] [] = zero
damage (false ∷ x) (true ∷ y) = suc (damage x y)
damage (false ∷ x) (false ∷ y) = damage x y
damage (true ∷ x) (false ∷ y) = damage x y
damage (true ∷ x) (true ∷ y) = damage x y

signedLedger : ∀ {m} (x y : Vec Bool m) →
  violations y + repairs x y ≡ violations x + damage x y
signedLedger [] [] = refl
signedLedger (false ∷ x) (false ∷ y) = signedLedger x y
signedLedger (true ∷ x) (true ∷ y) = cong suc (signedLedger x y)
signedLedger (false ∷ x) (true ∷ y)
  rewrite N.+-suc (violations x) (damage x y) =
  cong suc (signedLedger x y)
signedLedger (true ∷ x) (false ∷ y)
  rewrite N.+-suc (violations y) (repairs x y) =
  cong suc (signedLedger x y)

violationsBound : ∀ {m} (v : Vec Bool m) → violations v ≤ m
violationsBound [] = z≤n
violationsBound (false ∷ v) = N.≤-trans (violationsBound v) (N.n≤1+n _)
violationsBound (true ∷ v) = s≤s (violationsBound v)

-- Actual source relation remains a parameter; it is never replaced by
-- equality of residuals. Endpoints and every legal prefix are retained.
data SourceTrace {S : Set} (Legal : S → S → Set) : S → S → Set where
  done : ∀ {x} → SourceTrace Legal x x
  step : ∀ {x y z} → Legal x y → SourceTrace Legal y z → SourceTrace Legal x z

traceRepairs : ∀ {S : Set} {m} {Legal : S → S → Set}
  (b : S → Vec Bool m) {x y} → SourceTrace Legal x y → Nat
traceRepairs b done = zero
traceRepairs b (step {x} {y} edge rest) =
  repairs (b x) (b y) + traceRepairs b rest

traceDamage : ∀ {S : Set} {m} {Legal : S → S → Set}
  (b : S → Vec Bool m) {x y} → SourceTrace Legal x y → Nat
traceDamage b done = zero
traceDamage b (step {x} {y} edge rest) =
  damage (b x) (b y) + traceDamage b rest

-- Compose exact ledgers without subtracting naturals.
swapLast : (a b c : Nat) → a + (b + c) ≡ (a + c) + b
swapLast a b c = trans (cong (λ t → a + t) (N.+-comm b c))
  (sym (N.+-assoc a c b))

joinLedger : (a b c r s p q : Nat) →
  b + r ≡ c + p → a + s ≡ b + q →
  a + (r + s) ≡ c + (p + q)
joinLedger a b c r s p q first rest =
  trans (swapLast a r s)
    (trans (cong (λ t → t + r) rest)
      (trans (N.+-assoc b q r)
        (trans (swapLast b q r)
          (trans (cong (λ t → t + q) first)
            (N.+-assoc c p q)))))

traceLedger : ∀ {S : Set} {m} {Legal : S → S → Set}
  (b : S → Vec Bool m) {x y} (t : SourceTrace Legal x y) →
  violations (b y) + traceRepairs b t ≡
  violations (b x) + traceDamage b t
traceLedger b done = refl
traceLedger b (step {x} {y} {z} edge rest) =
  joinLedger (violations (b z)) (violations (b y)) (violations (b x))
    (repairs (b x) (b y)) (traceRepairs b rest)
    (damage (b x) (b y)) (traceDamage b rest)
    (signedLedger (b x) (b y)) (traceLedger b rest)

-- Each strict outer step contains a real source trace and an independently
-- established persistent-target inequality; no assertion of universal
-- availability or affordability is smuggled into this inductive type.
data StrictMacros {S : Set} {m : Nat}
  (Legal : S → S → Set) (b : S → Vec Bool m) :
  Nat → S → S → Set where
  stop : ∀ {x} → StrictMacros Legal b zero x x
  descend : ∀ {k x y z} →
    SourceTrace Legal x y →
    violations (b y) < violations (b x) →
    StrictMacros Legal b k y z →
    StrictMacros Legal b (suc k) x z

strictMacroCount : ∀ {S : Set} {m : Nat}
  {Legal : S → S → Set} {b : S → Vec Bool m} {k x y} →
  StrictMacros Legal b k x y → k ≤ violations (b x)
strictMacroCount stop = z≤n
strictMacroCount (descend trace decreases rest) =
  N.≤-trans (s≤s (strictMacroCount rest)) decreases

strictMacroCountBound : ∀ {S : Set} {m : Nat}
  {Legal : S → S → Set} {b : S → Vec Bool m} {k x y} →
  StrictMacros Legal b k x y → k ≤ m
strictMacroCountBound {b = b} {x = x} run =
  N.≤-trans (strictMacroCount run) (violationsBound (b x))
