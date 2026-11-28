module DASHI.Mathematics.Complexity.PNPDAGCutsetFactorizationExact where

-- Structural cut of the ORIGINAL newest-first indexed gate program.
-- All bypass inputs are retained in the interface. No extensional
-- combiner of uncharged size is introduced.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Repair
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C

data Suffix (n g : Nat) : Nat → Set where
  stop : Suffix n g g
  next : ∀ {h} → Suffix n g h → C.Gate n h → Suffix n g (suc h)

attach : ∀ {n g h} → C.GateProgram n g → Suffix n g h → C.GateProgram n h
attach p stop = p
attach p (next s a) = C.appendGate (attach p s) a

evalFrom : ∀ {n g h} → Suffix n g h → Vec Bool n → Vec Bool g → Vec Bool h
evalFrom stop x v = v
evalFrom (next s a) x v = C.evaluateGate a x (evalFrom s x v) ∷ evalFrom s x v

attachExact : ∀ {n g h} (p : C.GateProgram n g) (s : Suffix n g h)
  (x : Vec Bool n) →
  C.evaluateProgram (attach p s) x ≡ evalFrom s x (C.evaluateProgram p x)
attachExact p stop x = refl
attachExact p (next s a) x rewrite attachExact p s x = refl

outputFactor : ∀ {n g h} (p : C.GateProgram n g) (s : Suffix n g h)
  (w : C.WireRef n h) (x : Vec Bool n) →
  C.evaluateWire w x (C.evaluateProgram (attach p s) x) ≡
  C.evaluateWire w x (evalFrom s x (C.evaluateProgram p x))
outputFactor p s w x = cong (C.evaluateWire w x) (attachExact p s x)

-- A structural suffix is not an arbitrary Boolean lookup table.
-- Each next constructor is exactly one original gate. The sparse
-- live cut is a refinement of this complete boundary; unused input
-- and prefix wires may be dropped only after dependency certification.

record Cut {n h k : Nat} (p : C.GateProgram n (h + k)) : Set where
  constructor cut
  field
    prefix : C.GateProgram n k
    suffix : Suffix n k (h + k)
    reassemble : attach prefix suffix ≡ p

splitBySuffix : ∀ {n} (h k : Nat) (p : C.GateProgram n (h + k)) → Cut {h = h} {k = k} p
splitBySuffix zero k p = cut p stop refl
splitBySuffix (suc h) k (C.appendGate p a) with splitBySuffix h k p
... | cut pre s eq = cut pre (next s a) (cong (λ q → C.appendGate q a) eq)

splitOutputExact : ∀ {n} (h k : Nat) (p : C.GateProgram n (h + k))
  (w : C.WireRef n (h + k)) (x : Vec Bool n) →
  let c = splitBySuffix h k p in
  C.evaluateWire w x (C.evaluateProgram p x) ≡
  C.evaluateWire w x (evalFrom (Cut.suffix c) x (C.evaluateProgram (Cut.prefix c) x))
splitOutputExact h k p w x with splitBySuffix h k p
... | cut pre s eq =
  trans (cong (λ q → C.evaluateWire w x (C.evaluateProgram q x)) (sym eq))
    (outputFactor pre s w x)

-- Every original gate program of size h+k now has the original
-- k-gate prefix and h-gate suffix, retaining input bypass wires.

-- Reuse the exact donor behind anyActualTwinResidualMustSeparate:
-- the original gate-prefix observation can omit input bypasses, and
-- those bypasses are a typed residual of the cut.
module ActualCut {n g h : Nat}
  (p : C.GateProgram n g) (s : Suffix n g h)
  (w : C.WireRef n h) where

  coarse : Vec Bool n → Vec Bool g
  coarse = C.evaluateProgram p

  consumer : Vec Bool n → Bool
  consumer x = C.evaluateWire w x (C.evaluateProgram (attach p s) x)

  combine : Vec Bool g × Vec Bool n → Bool
  combine (v , x) = C.evaluateWire w x (evalFrom s x v)

  repair : Repair.ResidualRepair coarse (λ x → x) consumer
  repair = record
    { Repair.jointSufficient = λ x y same →
        trans (outputFactor p s w x)
          (trans (cong combine same) (sym (outputFactor p s w y)))
    }

  -- ANY repair, not just the full original input, must separate each
  -- actual prefix collision with distinct final decision.
  cutResidualMustSeparate : ∀ {R : Set} (r : Vec Bool n → R) →
    (collision : Repair.ConsumerRelevantCollision coarse consumer) →
    Repair.ResidualRepair coarse r consumer →
    r (Repair.left collision) ≡ r (Repair.right collision) → ⊥
  cutResidualMustSeparate r collision correct same =
    Repair.residualMustSeparateRelevantCollision collision correct same

-- This transfers consumer-indexed necessity, not arithmetic primality
-- results or a universal SAT circuit lower bound.
