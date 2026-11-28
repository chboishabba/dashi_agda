module DASHI.Mathematics.Complexity.PNPDAGCutsetFactorizationExact where

-- Structural cut of the ORIGINAL newest-first indexed gate program.
-- All bypass inputs are retained in the interface. No extensional
-- combiner of uncharged size is introduced.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; _∷_)
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
