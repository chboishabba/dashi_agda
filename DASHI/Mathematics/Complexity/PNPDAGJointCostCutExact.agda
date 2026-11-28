module DASHI.Mathematics.Complexity.PNPDAGJointCostCutExact where

-- Existing original structural split and reassembly are inverse at
-- the level of exact gate budget and original consumer. This removes
-- width-only nonfactorization as a separate lower-bound requirement.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Vec.Base using (Vec)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.PNPDAGCutsetFactorizationExact as Cut

record CircuitAtCost {n : Nat} (f : Vec Bool n → Bool) (s : Nat) : Set where
  constructor circuit-at-cost
  field
    program : C.GateProgram n s
    output : C.WireRef n s
    correct : ∀ x → C.evaluateWire output x (C.evaluateProgram program x) ≡ f x

record JointCut {n : Nat} (f : Vec Bool n → Bool) (k h : Nat) : Set where
  constructor joint-cut
  field
    prefix : C.GateProgram n k
    suffix : Cut.Suffix n k (h + k)
    output : C.WireRef n (h + k)
    correct : ∀ x → C.evaluateWire output x
      (Cut.evalFrom suffix x (C.evaluateProgram prefix x)) ≡ f x

toJoint : ∀ {n} {f : Vec Bool n → Bool} (k h : Nat) →
  CircuitAtCost f (h + k) → JointCut f k h
toJoint k h (circuit-at-cost p w correct) with Cut.splitBySuffix h k p
... | Cut.cut pre s eq = joint-cut pre s w
  (λ x → trans (sym (Cut.outputFactor pre s w x))
    (trans (cong (λ q → C.evaluateWire w x (C.evaluateProgram q x)) eq)
      (correct x)))

fromJoint : ∀ {n} {f : Vec Bool n → Bool} {k h} →
  JointCut f k h → CircuitAtCost f (h + k)
fromJoint (joint-cut p s w correct) =
  circuit-at-cost (Cut.attach p s) w
    (λ x → trans (Cut.outputFactor p s w x) (correct x))

-- The paid prefix and paid suffix use exactly the original gate
-- budget h+k. Original input bypasses are explicit in evalFrom.
-- Neither separate subcircuit sizes nor an arbitrary uncharged
-- extensional combiner are substituted for that joint budget.
noJointGivesNoCircuit : ∀ {n} {f : Vec Bool n → Bool} {k h} →
  (JointCut f k h → ⊥) → CircuitAtCost f (h + k) → ⊥
noJointGivesNoCircuit {k = k} {h = h} noJoint c = noJoint (toJoint k h c)

noCircuitGivesNoJoint : ∀ {n} {f : Vec Bool n → Bool} {k h} →
  (CircuitAtCost f (h + k) → ⊥) → JointCut f k h → ⊥
noCircuitGivesNoJoint noCircuit c = noCircuit (fromJoint c)

-- Thus excluding every joint cut at each polynomial gate budget is
-- exactly an unrestricted circuit lower bound in this model. That is
-- an independent mathematical obligation, not a consequence of the
-- finite factorization theorem or of a pigeonhole on internal keys.
