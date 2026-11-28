module DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact where

-- Concrete native threshold rows on the existing newest-first GateProgram.
-- Each adjacent pair costs two gates, old rows are shared, never inlined.
-- Exact circuit semantics are at the Boolean table level. Natural-number
-- excess/ceiling arithmetic has an independent Lean proof source.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base as F using (Fin)
open import Data.Vec.Base using (Vec)
open import Data.List.Base using (List; []; _∷_; map; replicate; drop; length; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as B
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as S

eval : ∀ {n g} → C.GateProgram n g → C.WireRef n g → Vec Bool n → Bool
eval p w x = C.evaluateWire w x (C.evaluateProgram p x)

values : ∀ {n g} → C.GateProgram n g → List (C.WireRef n g) → Vec Bool n → List Bool
values p [] x = []
values p (w ∷ ws) x = eval p w x ∷ values p ws x

shift : ∀ {n g} → C.WireRef n g → C.WireRef n (suc g)
shift (C.inputWire i) = C.inputWire i
shift (C.gateWire i) = C.gateWire (F.suc i)

shiftExact : ∀ {n g} (p : C.GateProgram n g) (a : C.Gate n g)
  (w : C.WireRef n g) (x : Vec Bool n) →
  eval (C.appendGate p a) (shift w) x ≡ eval p w x
shiftExact p a (C.inputWire i) x = refl
shiftExact p a (C.gateWire i) x = refl

-- Local builder receipt: every previous wire remains available with its
-- original semantics. No oracle fields are used in the constructors below.
record Built {n g} (p : C.GateProgram n g)
    (spec : Vec Bool n → List Bool) : Set where
  field
    gates : Nat
    program : C.GateProgram n gates
    transport : C.WireRef n g → C.WireRef n gates
    transportExact : ∀ w x → eval program (transport w) x ≡ eval p w x
    outputs : List (C.WireRef n gates)
    outputsExact : ∀ x → values program outputs x ≡ spec x
open Built

empty : ∀ {n g} (p : C.GateProgram n g) → Built p (λ _ → [])
empty p = record
  { gates = _ ; program = p ; transport = λ w → w
  ; transportExact = λ w x → refl ; outputs = []
  ; outputsExact = λ x → refl }

transportValues : ∀ {n g} {p : C.GateProgram n g} {spec}
  (b : Built p spec) (ws : List (C.WireRef n g)) (x : Vec Bool n) →
  values (program b) (map (transport b) ws) x ≡ values p ws x
transportValues b [] x = refl
transportValues b (w ∷ ws) x
  rewrite transportExact b w x | transportValues b ws x = refl

shiftValues : ∀ {n g} (p : C.GateProgram n g) (a : C.Gate n g)
  (ws : List (C.WireRef n g)) (x : Vec Bool n) →
  values (C.appendGate p a) (map shift ws) x ≡ values p ws x
shiftValues p a [] x = refl
shiftValues p a (w ∷ ws) x
  rewrite shiftExact p a w x | shiftValues p a ws x = refl

repeatValues : ∀ {n g} (p : C.GateProgram n g) (k : Nat)
  (w : C.WireRef n g) (x : Vec Bool n) →
  values p (replicate k w) x ≡ replicate k (eval p w x)
repeatValues p zero w x = refl
repeatValues p (suc k) w x rewrite repeatValues p k w x = refl

appendValues : ∀ {n g} (p : C.GateProgram n g) (a b : List (C.WireRef n g)) x →
  values p (a ++ b) x ≡ values p a x ++ values p b x
appendValues p [] b x = refl
appendValues p (w ∷ ws) b x rewrite appendValues p ws b x = refl

dropValues : ∀ {n g} (p : C.GateProgram n g) k (ws : List (C.WireRef n g)) x →
  values p (drop k ws) x ≡ drop k (values p ws x)
dropValues p zero ws x = refl
dropValues p (suc k) [] x = refl
dropValues p (suc k) (w ∷ ws) x = dropValues p k ws x

nextTail : Bool → Bool → List Bool → List Bool
nextTail b a [] = []
nextTail b a (c ∷ cs) =
  B.orBool c (B.andBool b a) ∷ nextTail b c cs

nextRow : Bool → List Bool → List Bool
nextRow b [] = []
nextRow b (a ∷ as) = a ∷ nextTail b a as

table : List Bool → Nat → List Bool
table [] k = true ∷ replicate k false
table (b ∷ bs) k = nextRow b (table bs k)

buildTail : ∀ {n g} (p : C.GateProgram n g)
  (b a : C.WireRef n g) (ws : List (C.WireRef n g)) →
  Built p (λ x → nextTail (eval p b x) (eval p a x) (values p ws x))
buildTail p b a [] = empty p
buildTail p b a (c ∷ cs) = record
  { gates = suc (suc (gates rest))
  ; program = C.appendGate q₁ og
  ; transport = λ w → shift (shift (transport rest w))
  ; transportExact = λ w x →
      trans (shiftExact q₁ og (shift (transport rest w)) x)
        (trans (shiftExact q ag (transport rest w) x)
          (transportExact rest w x))
  ; outputs = C.gateWire F.zero ∷ map shift (map shift (outputs rest))
  ; outputsExact = correct
  }
  where
    rest = buildTail p b c cs
    q = program rest
    ag = C.andGate (transport rest b) (transport rest a)
    q₁ = C.appendGate q ag
    og = C.orGate (shift (transport rest c)) (C.gateWire F.zero)
    correct : ∀ x →
      values (C.appendGate q₁ og)
        (C.gateWire F.zero ∷ map shift (map shift (outputs rest))) x
      ≡ nextTail (eval p b x) (eval p a x) (values p (c ∷ cs) x)
    correct x
      rewrite shiftExact q ag (transport rest c) x
            | transportExact rest c x
            | transportExact rest b x
            | transportExact rest a x
            | shiftValues q₁ og (map shift (outputs rest)) x
            | shiftValues q ag (outputs rest) x
            | outputsExact rest x = refl

buildRow : ∀ {n g} (p : C.GateProgram n g)
  (b : C.WireRef n g) (ws : List (C.WireRef n g)) →
  Built p (λ x → nextRow (eval p b x) (values p ws x))
buildRow p b [] = empty p
buildRow p b (a ∷ as) = record
  { gates = gates rest ; program = program rest
  ; transport = transport rest ; transportExact = transportExact rest
  ; outputs = transport rest a ∷ outputs rest
  ; outputsExact = λ x → cong₂-cons (transportExact rest a x) (outputsExact rest x)
  }
  where
    rest = buildTail p b a as
    cong₂-cons : ∀ {a b : Bool} {as bs : List Bool} →
      a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
    cong₂-cons refl refl = refl

buildTable : ∀ {n g} (p : C.GateProgram n g)
  (ws : List (C.WireRef n g)) (k : Nat) →
  Built p (λ x → table (values p ws x) k)
buildTable {g = g} p [] k = record
  { gates = suc (suc g) ; program = q
  ; transport = λ w → shift (shift w)
  ; transportExact = λ w x →
      trans (shiftExact p₁ (C.constantGate false) (shift w) x)
        (shiftExact p (C.constantGate true) w x)
  ; outputs = C.gateWire (F.suc F.zero) ∷ replicate k (C.gateWire F.zero)
  ; outputsExact = λ x → cong (true ∷_) (repeatValues q k (C.gateWire F.zero) x)
  }
  where
    p₁ = C.appendGate p (C.constantGate true)
    q = C.appendGate p₁ (C.constantGate false)
buildTable p (w ∷ ws) k = record
  { gates = gates row ; program = program row
  ; transport = λ v → transport row (transport rest v)
  ; transportExact = λ v x →
      trans (transportExact row (transport rest v) x) (transportExact rest v x)
  ; outputs = outputs row
  ; outputsExact = correct
  }
  where
    rest = buildTable p ws k
    row = buildRow (program rest) (transport rest w) (outputs rest)
    correct : ∀ x → values (program row) (outputs row) x
      ≡ table (values p (w ∷ ws) x) k
    correct x = trans (outputsExact row x)
      (cong₂-next (transportExact rest w x) (outputsExact rest x))
      where
        cong₂-next : ∀ {b c : Bool} {as bs : List Bool} →
          b ≡ c → as ≡ bs → nextRow b as ≡ nextRow c bs
        cong₂-next refl refl = refl

-- Original rows are finite original input coordinate lists and capacities.
Rows : Nat → Set
Rows n = List (List (Fin n) × Nat)

inputBits : ∀ {n} → List (Fin n) → Vec Bool n → List Bool
inputBits [] x = []
inputBits (i ∷ is) x = C.lookupVec i x ∷ inputBits is x

inputValuesExact : ∀ {n g} (p : C.GateProgram n g) (is : List (Fin n)) x →
  values p (map C.inputWire is) x ≡ inputBits is x
inputValuesExact p [] x = refl
inputValuesExact p (i ∷ is) x rewrite inputValuesExact p is x = refl

aggregateBits : ∀ {n} → Rows n → Vec Bool n → List Bool
aggregateBits [] x = []
aggregateBits ((is , cap) ∷ rs) x =
  drop (suc cap) (table (inputBits is x) (length is)) ++ aggregateBits rs x

buildAggregate : ∀ {n g} (p : C.GateProgram n g) (rs : Rows n) →
  Built p (aggregateBits rs)
buildAggregate p [] = empty p
buildAggregate p ((is , cap) ∷ rs) = record
  { gates = gates row ; program = program row
  ; transport = λ w → transport row (transport rest w)
  ; transportExact = λ w x →
      trans (transportExact row (transport rest w) x) (transportExact rest w x)
  ; outputs = drop (suc cap) (outputs row) ++ map (transport row) (outputs rest)
  ; outputsExact = correct
  }
  where
    rest = buildAggregate p rs
    row = buildTable (program rest) (map C.inputWire is) (length is)
    correct : ∀ x →
      values (program row)
        (drop (suc cap) (outputs row) ++ map (transport row) (outputs rest)) x
      ≡ aggregateBits ((is , cap) ∷ rs) x
    correct x
      rewrite appendValues (program row) (drop (suc cap) (outputs row))
                (map (transport row) (outputs rest)) x
            | dropValues (program row) (suc cap) (outputs row) x
            | outputsExact row x
            | inputValuesExact (program rest) is x
            | transportValues row (outputs rest) x
            | outputsExact rest x = refl

at : ∀ {A : Set} → A → Nat → List A → A
at d k [] = d
at d zero (a ∷ as) = a
at d (suc k) (a ∷ as) = at d k as

atValues : ∀ {n g} (p : C.GateProgram n g) (d : C.WireRef n g)
  (k : Nat) (ws : List (C.WireRef n g)) x →
  eval p (at d k ws) x ≡ at (eval p d x) k (values p ws x)
atValues p d k [] x = refl
atValues p d zero (w ∷ ws) x = refl
atValues p d (suc k) (w ∷ ws) x = atValues p d k ws x

aggregateAccept : ∀ {n} → Rows n → Nat → Vec Bool n → Bool
aggregateAccept rs k x =
  B.notBool (at false (suc k) (table (aggregateBits rs x) (suc k)))

-- Construct an actual shared circuit: row DP, aggregate DP, NOT output.
-- The caller may first clamp k to the finite total row degree; the supplied
-- Python compiler already performs that guard.
aggregateCircuit : ∀ {n} → Rows n → Nat → C.ConcreteBooleanCircuit n
aggregateCircuit rs k =
  C.concrete-boolean-circuit _ final (C.gateWire F.zero)
  where
    r = buildAggregate C.noGates rs
    t = buildTable (program r) (outputs r) (suc k)
    q = C.appendGate (program t) (C.constantGate false)
    final = C.appendGate q
      (C.notGate (at (C.gateWire F.zero) (suc k) (map shift (outputs t))))

aggregateCircuitExact : ∀ {n} (rs : Rows n) (k : Nat) (x : Vec Bool n) →
  C.evaluateCircuit (aggregateCircuit rs k) x ≡ aggregateAccept rs k x
aggregateCircuitExact rs k x =
  cong B.notBool
    (trans (atValues q (C.gateWire F.zero) (suc k) (map shift (outputs t)) x)
      (cong (at false (suc k))
        (trans (shiftValues (program t) (C.constantGate false) (outputs t) x)
          (trans (outputsExact t x)
            (cong (λ bs → table bs (suc k)) (outputsExact r x))))))
  where
    r = buildAggregate C.noGates rs
    t = buildTable (program r) (outputs r) (suc k)
    q = C.appendGate (program t) (C.constantGate false)

-- BIDI on the actual Cook formula: only the aggregate-specific arithmetic
-- interpretation and source bit-cost admission remain, not Tseitin semantics.
aggregateToSAT : ∀ {n} (rs : Rows n) (k : Nat) (x : Vec Bool n) →
  aggregateAccept rs k x ≡ true →
  B.Satisfiable (S.sharedAcceptanceFormula (aggregateCircuit rs k))
aggregateToSAT rs k x yes =
  S.acceptedInputGivesSharedSatisfiable (aggregateCircuit rs k) x
    (trans (aggregateCircuitExact rs k x) yes)

aggregateFromSAT : ∀ {n} (rs : Rows n) (k : Nat) →
  B.Satisfiable (S.sharedAcceptanceFormula (aggregateCircuit rs k)) →
  Σ (Vec Bool n) (λ x → aggregateAccept rs k x ≡ true)
aggregateFromSAT rs k sat
  with S.sharedSatisfiableGivesAcceptedInput (aggregateCircuit rs k) sat
... | x , yes = x , trans (sym (aggregateCircuitExact rs k x)) yes
