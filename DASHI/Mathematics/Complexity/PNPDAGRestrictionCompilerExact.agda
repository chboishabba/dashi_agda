module DASHI.Mathematics.Complexity.PNPDAGRestrictionCompilerExact where

-- Cost-bearing constant propagation on the original indexed GateProgram.
-- One original gate creates at most one target gate. Shared wires use
-- the same image map; no expression-tree duplication.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNPDAGSparseDependencyExact as Sparse

data Image (n h : Nat) : Set where
  known : Bool → Image n h
  wire : C.WireRef n h → Image n h

observe : ∀ {n h} → Image n h → Vec Bool n → Vec Bool h → Bool
observe (known b) x v = b
observe (wire w) x v = C.evaluateWire w x v

weaken : ∀ {n h} → Image n h → Image n (suc h)
weaken (known b) = known b
weaken (wire w) = wire (Sparse.lift w)

weakenExact : ∀ {n h} (i : Image n h) (x : Vec Bool n) (v : Vec Bool h) (b : Bool) →
  observe (weaken i) x (b ∷ v) ≡ observe i x v
weakenExact (known b) x v a = refl
weakenExact (wire (C.inputWire i)) x v a = refl
weakenExact (wire (C.gateWire i)) x v a = refl

data Plan (n h : Nat) : Set where
  alias : Image n h → Plan n h
  fresh : C.Gate n h → Plan n h

evalPlan : ∀ {n h} → Plan n h → Vec Bool n → Vec Bool h → Bool
evalPlan (alias i) = observe i
evalPlan (fresh a) = C.evaluateGate a

notPlan : ∀ {n h} → Image n h → Plan n h
notPlan (known b) = alias (known (Cook.notBool b))
notPlan (wire w) = fresh (C.notGate w)

andPlan : ∀ {n h} → Image n h → Image n h → Plan n h
andPlan (known false) b = alias (known false)
andPlan (known true) b = alias b
andPlan (wire a) (known false) = alias (known false)
andPlan (wire a) (known true) = alias (wire a)
andPlan (wire a) (wire b) = fresh (C.andGate a b)

orPlan : ∀ {n h} → Image n h → Image n h → Plan n h
orPlan (known false) b = alias b
orPlan (known true) b = alias (known true)
orPlan (wire a) (known false) = alias (wire a)
orPlan (wire a) (known true) = alias (known true)
orPlan (wire a) (wire b) = fresh (C.orGate a b)

notExact : ∀ {n h} (a : Image n h) (x : Vec Bool n) (v : Vec Bool h) →
  evalPlan (notPlan a) x v ≡ Cook.notBool (observe a x v)
notExact (known b) x v = refl
notExact (wire w) x v = refl

andExact : ∀ {n h} (a b : Image n h) (x : Vec Bool n) (v : Vec Bool h) →
  evalPlan (andPlan a b) x v ≡ Cook.andBool (observe a x v) (observe b x v)
andExact (known false) b x v = refl
andExact (known true) b x v = refl
andExact (wire a) (known false) x v with C.evaluateWire a x v
... | false = refl
... | true = refl
andExact (wire a) (known true) x v with C.evaluateWire a x v
... | false = refl
... | true = refl
andExact (wire a) (wire b) x v = refl

orExact : ∀ {n h} (a b : Image n h) (x : Vec Bool n) (v : Vec Bool h) →
  evalPlan (orPlan a b) x v ≡ Cook.orBool (observe a x v) (observe b x v)
orExact (known false) b x v = refl
orExact (known true) b x v = refl
orExact (wire a) (known false) x v with C.evaluateWire a x v
... | false = refl
... | true = refl
orExact (wire a) (known true) x v with C.evaluateWire a x v
... | false = refl
... | true = refl
orExact (wire a) (wire b) x v = refl

planGate : ∀ {n g h} → (C.WireRef n g → Image n h) → C.Gate n g → Plan n h
planGate im (C.constantGate b) = alias (known b)
planGate im (C.notGate w) = notPlan (im w)
planGate im (C.andGate u v) = andPlan (im u) (im v)
planGate im (C.orGate u v) = orPlan (im u) (im v)

planExact : ∀ {n g h} (im : C.WireRef n g → Image n h)
  (a : C.Gate n g) (x y : Vec Bool n) (v : Vec Bool g) (u : Vec Bool h) →
  (∀ w → observe (im w) y u ≡ C.evaluateWire w x v) →
  evalPlan (planGate im a) y u ≡ C.evaluateGate a x v
planExact im (C.constantGate b) x y v u eq = refl
planExact im (C.notGate w) x y v u eq =
  trans (notExact (im w) y u) (cong Cook.notBool (eq w))
planExact im (C.andGate w z) x y v u eq =
  trans (andExact (im w) (im z) y u) (cong₂ Cook.andBool (eq w) (eq z))
planExact im (C.orGate w z) x y v u eq =
  trans (orExact (im w) (im z) y u) (cong₂ Cook.orBool (eq w) (eq z))

pinImage : ∀ {n h} → (Fin n → Maybe Bool) → Fin n → Image n h
pinImage pin i with pin i
... | just b = known b
... | nothing = wire (C.inputWire i)

InputAgreement : ∀ {n} → (Fin n → Maybe Bool) → Vec Bool n → Vec Bool n → Set
InputAgreement pin x y =
  ∀ i → observe (pinImage {h = zero} pin i) y [] ≡ C.lookupVec i x

record Compilation {n g : Nat} (pin : Fin n → Maybe Bool)
  (p : C.GateProgram n g) : Set where
  field
    count : Nat
    program : C.GateProgram n count
    image : C.WireRef n g → Image n count
    bound : count ≤ g
    exact : ∀ x y → InputAgreement pin x y → ∀ w →
      observe (image w) y (C.evaluateProgram program y) ≡
      C.evaluateWire w x (C.evaluateProgram p x)
open Compilation

extendAlias : ∀ {n g h} → (C.WireRef n g → Image n h) → Image n h →
  C.WireRef n (suc g) → Image n h
extendAlias im a (C.inputWire i) = im (C.inputWire i)
extendAlias im a (C.gateWire fzero) = a
extendAlias im a (C.gateWire (fsuc i)) = im (C.gateWire i)

extendFresh : ∀ {n g h} → (C.WireRef n g → Image n h) →
  C.WireRef n (suc g) → Image n (suc h)
extendFresh im (C.inputWire i) = weaken (im (C.inputWire i))
extendFresh im (C.gateWire fzero) = wire (C.gateWire fzero)
extendFresh im (C.gateWire (fsuc i)) = weaken (im (C.gateWire i))

compile : ∀ {n g} (pin : Fin n → Maybe Bool) (p : C.GateProgram n g) → Compilation pin p
compile pin C.noGates = record
  { count = zero ; program = C.noGates
  ; image = λ { (C.inputWire i) → pinImage pin i ; (C.gateWire ()) }
  ; bound = z≤n
  ; exact = λ { x y h (C.inputWire i) → h i ; x y h (C.gateWire ()) } }
compile pin (C.appendGate p a) with compile pin p
... | old with planGate (image old) a in eq
...   | alias v = record
  { count = count old ; program = program old ; image = extendAlias (image old) v
  ; bound = N.≤-step (bound old)
  ; exact = λ
    { x y h (C.inputWire i) → exact old x y h (C.inputWire i)
    ; x y h (C.gateWire (fsuc i)) → exact old x y h (C.gateWire i)
    ; x y h (C.gateWire fzero) →
        trans (cong (λ z → evalPlan z y (C.evaluateProgram (program old) y)) (sym eq))
          (planExact (image old) a x y (C.evaluateProgram p x)
            (C.evaluateProgram (program old) y) (exact old x y h)) } }
...   | fresh b = record
  { count = suc (count old) ; program = C.appendGate (program old) b
  ; image = extendFresh (image old) ; bound = s≤s (bound old)
  ; exact = λ
    { x y h (C.inputWire i) →
        trans (weakenExact (image old (C.inputWire i)) y
          (C.evaluateProgram (program old) y) _) (exact old x y h (C.inputWire i))
    ; x y h (C.gateWire (fsuc i)) →
        trans (weakenExact (image old (C.gateWire i)) y
          (C.evaluateProgram (program old) y) _) (exact old x y h (C.gateWire i))
    ; x y h (C.gateWire fzero) →
        trans (cong (λ z → evalPlan z y (C.evaluateProgram (program old) y)) (sym eq))
          (planExact (image old) a x y (C.evaluateProgram p x)
            (C.evaluateProgram (program old) y) (exact old x y h)) } }

-- Materialized restricted output is either a target wire or one final
-- constant gate; sparse dead-gate elimination is a distinct refinement.
restrictedOutput : ∀ {n g} (pin : Fin n → Maybe Bool) (p : C.GateProgram n g)
  (w : C.WireRef n g) (x y : Vec Bool n) → InputAgreement pin x y →
  let c = compile pin p in
  observe (image c w) y (C.evaluateProgram (program c) y) ≡
  C.evaluateWire w x (C.evaluateProgram p x)
restrictedOutput pin p w x y h = exact (compile pin p) x y h w

-- Materialize the final Boolean result, charging a constant gate only
-- when the restricted output has become a literal known value.
finish : ∀ {n h} → C.GateProgram n h → Image n h → C.ConcreteBooleanCircuit n
finish {h = h} p (wire w) = C.concrete-boolean-circuit h p w
finish {h = h} p (known b) =
  C.concrete-boolean-circuit (suc h) (C.appendGate p (C.constantGate b)) (C.gateWire fzero)

finishExact : ∀ {n h} (p : C.GateProgram n h) (i : Image n h) (x : Vec Bool n) →
  C.evaluateCircuit (finish p i) x ≡ observe i x (C.evaluateProgram p x)
finishExact p (wire w) x = refl
finishExact p (known b) x = refl

finishBound : ∀ {n h g} (p : C.GateProgram n h) (i : Image n h) → h ≤ g →
  C.circuitSize (finish p i) ≤ suc g
finishBound p (wire w) h = N.≤-step h
finishBound p (known b) h = s≤s h

restrictCircuit : ∀ {n} → (Fin n → Maybe Bool) →
  C.ConcreteBooleanCircuit n → C.ConcreteBooleanCircuit n
restrictCircuit pin c =
  let t = compile pin (C.program c) in finish (program t) (image t (C.outputWire c))

restrictCircuitExact : ∀ {n} (pin : Fin n → Maybe Bool)
  (c : C.ConcreteBooleanCircuit n) (x y : Vec Bool n) →
  InputAgreement pin x y →
  C.evaluateCircuit (restrictCircuit pin c) y ≡ C.evaluateCircuit c x
restrictCircuitExact pin c x y h =
  let t = compile pin (C.program c) in
  trans (finishExact (program t) (image t (C.outputWire c)) y)
    (exact t x y h (C.outputWire c))

restrictCircuitBound : ∀ {n} (pin : Fin n → Maybe Bool) (c : C.ConcreteBooleanCircuit n) →
  C.circuitSize (restrictCircuit pin c) ≤ suc (C.circuitSize c)
restrictCircuitBound pin c =
  let t = compile pin (C.program c) in
  finishBound (program t) (image t (C.outputWire c)) (bound t)
