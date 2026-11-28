module DASHI.Mathematics.Complexity.PNPHardAffineGateExact where

-- Native original-coordinate hard constraints on the existing GateProgram.
-- A normal is an explicit XOR list and its required bit. A forbidden flat
-- is a conjunction of normals; the empty flat excludes every point.
-- Duplicates are intentionally retained (XOR cancels them semantically).
-- Source-written; kernel acceptance and binary source parser separate.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base as F using (Fin)
open import Data.Vec.Base using (Vec)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as B
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T

Normal : Nat → Set
Normal n = List (Fin n) × Bool

Flat : Nat → Set
Flat n = List (Normal n)

xor : Bool → Bool → Bool
xor a b = B.andBool (B.orBool a b) (B.notBool (B.andBool a b))

parity : ∀ {n} → List (Fin n) → Vec Bool n → Bool
parity [] x = false
parity (i ∷ is) x = xor (parity is x) (C.lookupVec i x)

normalValue : ∀ {n} → Normal n → Vec Bool n → Bool
normalValue (is , true) x = parity is x
normalValue (is , false) x = B.notBool (parity is x)

flatValue : ∀ {n} → Flat n → Vec Bool n → Bool
flatValue [] x = true
flatValue (a ∷ as) x = B.andBool (normalValue a x) (flatValue as x)

allowed : ∀ {n} → List (Flat n) → Vec Bool n → Bool
allowed [] x = true
allowed (a ∷ as) x = B.andBool (B.notBool (flatValue a x)) (allowed as x)

hardValue : ∀ {n} → Flat n → List (Flat n) → Vec Bool n → Bool
hardValue h fs x = B.andBool (flatValue h x) (allowed fs x)

-- Single-output specialization of the existing T.Built wire-transport
-- discipline; no new gate, interpreter, CNF or source variable allocation.
record Result {n g} (p : C.GateProgram n g) (f : Vec Bool n → Bool) : Set where
  field
    gates : Nat
    program : C.GateProgram n gates
    wire : C.WireRef n gates
    lift : C.WireRef n g → C.WireRef n gates
    liftExact : ∀ w x → T.eval program (lift w) x ≡ T.eval p w x
    exact : ∀ x → T.eval program wire x ≡ f x
open Result

constant : ∀ {n g} (p : C.GateProgram n g) (b : Bool) → Result p (λ _ → b)
constant {g = g} p b = record
  { gates = suc g ; program = C.appendGate p (C.constantGate b)
  ; wire = C.gateWire F.zero ; lift = T.shift
  ; liftExact = T.shiftExact p (C.constantGate b)
  ; exact = λ x → refl }

negateResult : ∀ {n g} {p : C.GateProgram n g} {f}
  (r : Result p f) → Result p (λ x → B.notBool (f x))
negateResult r = record
  { gates = suc (gates r) ; program = C.appendGate (program r) ng
  ; wire = C.gateWire F.zero ; lift = λ w → T.shift (lift r w)
  ; liftExact = λ w x → trans (T.shiftExact (program r) ng (lift r w) x) (liftExact r w x)
  ; exact = λ x → cong B.notBool (exact r x) }
  where ng = C.notGate (wire r)

andResult : ∀ {n g} {p : C.GateProgram n g} {f h}
  (r : Result p f) (s : Result (program r) h) →
  Result p (λ x → B.andBool (f x) (h x))
andResult r s = record
  { gates = suc (gates s) ; program = C.appendGate (program s) ag
  ; wire = C.gateWire F.zero
  ; lift = λ w → T.shift (lift s (lift r w))
  ; liftExact = λ w x → trans (T.shiftExact (program s) ag (lift s (lift r w)) x)
      (trans (liftExact s (lift r w) x) (liftExact r w x))
  ; exact = λ x → cong₂ B.andBool (trans (liftExact s (wire r) x) (exact r x)) (exact s x) }
  where ag = C.andGate (lift s (wire r)) (wire s)

xorInput : ∀ {n g} {p : C.GateProgram n g} {f} (r : Result p f) (i : Fin n) →
  Result p (λ x → xor (f x) (C.lookupVec i x))
xorInput {f = f} r i = record
  { gates = suc (suc (suc (suc (gates r))))
  ; program = C.appendGate q3 g4 ; wire = C.gateWire F.zero
  ; lift = λ w → T.shift (T.shift (T.shift (T.shift (lift r w))))
  ; liftExact = λ w x →
      trans (T.shiftExact q3 g4 _ x)
        (trans (T.shiftExact q2 g3 _ x)
          (trans (T.shiftExact q1 g2 _ x)
            (trans (T.shiftExact q g1 _ x) (liftExact r w x))))
  ; exact = correct }
  where
    q = program r
    a = wire r
    b = C.inputWire i
    g1 = C.orGate a b
    q1 = C.appendGate q g1
    g2 = C.andGate (T.shift a) (C.inputWire i)
    q2 = C.appendGate q1 g2
    g3 = C.notGate (C.gateWire F.zero)
    q3 = C.appendGate q2 g3
    g4 = C.andGate (C.gateWire (F.suc (F.suc F.zero))) (C.gateWire F.zero)
    correct : ∀ x → T.eval (C.appendGate q3 g4) (C.gateWire F.zero) x
      ≡ xor (f x) (C.lookupVec i x)
    correct x = cong₂ B.andBool
      (cong (λ z → B.orBool z (C.lookupVec i x)) (exact r x))
      (cong B.notBool (cong (λ z → B.andBool z (C.lookupVec i x))
        (trans (T.shiftExact q g1 a x) (exact r x))))

compileParity : ∀ {n g} (p : C.GateProgram n g) (is : List (Fin n)) →
  Result p (parity is)
compileParity p [] = constant p false
compileParity p (i ∷ is) = xorInput (compileParity p is) i

compileNormal : ∀ {n g} (p : C.GateProgram n g) (a : Normal n) →
  Result p (normalValue a)
compileNormal p (is , true) = compileParity p is
compileNormal p (is , false) = negateResult (compileParity p is)

compileFlat : ∀ {n g} (p : C.GateProgram n g) (as : Flat n) →
  Result p (flatValue as)
compileFlat p [] = constant p true
compileFlat p (a ∷ as) = andResult r (compileFlat (program r) as)
  where r = compileNormal p a

compileAllowed : ∀ {n g} (p : C.GateProgram n g) (fs : List (Flat n)) →
  Result p (allowed fs)
compileAllowed p [] = constant p true
compileAllowed p (a ∷ as) = andResult r (compileAllowed (program r) as)
  where r = negateResult (compileFlat p a)

compileHard : ∀ {n g} (p : C.GateProgram n g) (h : Flat n) (fs : List (Flat n)) →
  Result p (hardValue h fs)
compileHard p h fs = andResult r (compileAllowed (program r) fs)
  where r = compileFlat p h

-- Attach the actual aggregate DAG to the actual hard prefix. Old hard
-- output is transported, not recomputed or expanded into a truth table.
compileDemand : ∀ {n} → Flat n → List (Flat n) → T.Rows n → Nat → C.ConcreteBooleanCircuit n
compileDemand h fs rs k = C.concrete-boolean-circuit _ final (C.gateWire F.zero)
  where
    r = compileHard C.noGates h fs
    a = T.buildAggregate (program r) rs
    t = T.buildTable (T.program a) (T.outputs a) (suc k)
    q = C.appendGate (T.program t) (C.constantGate false)
    ng = C.notGate (T.at (C.gateWire F.zero) (suc k) (map T.shift (T.outputs t)))
    q1 = C.appendGate q ng
    hw = T.transport t (T.transport a (wire r))
    final = C.appendGate q1 (C.andGate (T.shift (T.shift hw)) (C.gateWire F.zero))

demandExact : ∀ {n} (h : Flat n) (fs : List (Flat n)) (rs : T.Rows n) k (x : Vec Bool n) →
  C.evaluateCircuit (compileDemand h fs rs k) x ≡
  B.andBool (hardValue h fs x) (T.aggregateAccept rs k x)
demandExact h fs rs k x = cong₂ B.andBool hardRead aggRead
  where
    r = compileHard C.noGates h fs
    a = T.buildAggregate (program r) rs
    t = T.buildTable (T.program a) (T.outputs a) (suc k)
    q = C.appendGate (T.program t) (C.constantGate false)
    ng = C.notGate (T.at (C.gateWire F.zero) (suc k) (map T.shift (T.outputs t)))
    hw = T.transport t (T.transport a (wire r))
    hardRead = trans (T.shiftExact q ng (T.shift hw) x)
      (trans (T.shiftExact (T.program t) (C.constantGate false) hw x)
        (trans (T.transportExact t (T.transport a (wire r)) x)
          (trans (T.transportExact a (wire r) x) (exact r x))))
    aggRead = cong B.notBool
      (trans (T.atValues q (C.gateWire F.zero) (suc k) (map T.shift (T.outputs t)) x)
        (cong (T.at false (suc k))
          (trans (T.shiftValues (T.program t) (C.constantGate false) (T.outputs t) x)
            (trans (T.outputsExact t x)
              (cong (λ bs → T.table bs (suc k)) (T.outputsExact a x))))))
