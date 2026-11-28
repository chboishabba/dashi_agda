module DASHI.Mathematics.Complexity.PNPAggregateGateCountExact where

-- Structural counts on the actual native DAG, not an expanded formula.
-- The ceiling is clamped to the number of excess-indicator wires before
-- building the final table, even for a large binary-encoded requested bound.
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; length; map; replicate; drop; _++_)
open import Data.Vec.Base using (Vec)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T
import DASHI.Mathematics.Complexity.PNPAggregateThresholdArithmeticExact as A
import DASHI.Mathematics.Complexity.PNPAggregateHardCNFWeldExact as H
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact as F

twice : Nat → Nat
twice zero = zero
twice (suc d) = suc (suc (twice d))

tableCost : Nat → Nat → Nat
tableCost zero k = 2
tableCost (suc d) k = twice k + tableCost d k

lenMap : ∀ {X Y : Set} (f : X → Y) (xs : List X) →
  length (map f xs) ≡ length xs
lenMap f [] = refl
lenMap f (x ∷ xs) = cong suc (lenMap f xs)

lenRep : ∀ {X : Set} (k : Nat) (x : X) → length (replicate k x) ≡ k
lenRep zero x = refl
lenRep (suc k) x = cong suc (lenRep k x)

lenAppend : ∀ {X : Set} (xs ys : List X) →
  length (xs ++ ys) ≡ length xs + length ys
lenAppend [] ys = refl
lenAppend (x ∷ xs) ys = cong suc (lenAppend xs ys)

lenDrop : ∀ {X : Set} (k : Nat) (xs : List X) →
  length (drop k xs) ≡ A.sub (length xs) k
lenDrop zero xs = refl
lenDrop (suc k) [] = refl
lenDrop (suc k) (x ∷ xs) = lenDrop k xs

tailLength : ∀ {n g} (p : C.GateProgram n g)
  (b a : C.WireRef n g) (ws : List (C.WireRef n g)) →
  length (T.outputs (T.buildTail p b a ws)) ≡ length ws
tailLength p b a [] = refl
tailLength p b a (c ∷ cs)
  rewrite lenMap T.shift (map T.shift (T.outputs (T.buildTail p b c cs)))
        | lenMap T.shift (T.outputs (T.buildTail p b c cs))
        | tailLength p b c cs = refl

tailGates : ∀ {n g} (p : C.GateProgram n g)
  (b a : C.WireRef n g) (ws : List (C.WireRef n g)) →
  T.gates (T.buildTail p b a ws) ≡ twice (length ws) + g
tailGates p b a [] = refl
tailGates p b a (c ∷ cs) = cong (λ q → suc (suc q)) (tailGates p b c cs)

rowLength : ∀ {n g} (p : C.GateProgram n g)
  (b : C.WireRef n g) (ws : List (C.WireRef n g)) →
  length (T.outputs (T.buildRow p b ws)) ≡ length ws
rowLength p b [] = refl
rowLength p b (a ∷ as) = cong suc (tailLength p b a as)

rowGates : ∀ {n g} (p : C.GateProgram n g)
  (b : C.WireRef n g) (ws : List (C.WireRef n g)) →
  T.gates (T.buildRow p b ws) ≡ twice (A.sub (length ws) 1) + g
rowGates p b [] = refl
rowGates p b (a ∷ as) = tailGates p b a as

tableLength : ∀ {n g} (p : C.GateProgram n g)
  (ws : List (C.WireRef n g)) k →
  length (T.outputs (T.buildTable p ws k)) ≡ suc k
tableLength p [] k = cong suc (lenRep k _)
tableLength p (w ∷ ws) k =
  trans (rowLength (T.program rest) (T.transport rest w) (T.outputs rest))
    (tableLength p ws k)
  where rest = T.buildTable p ws k

tableGates : ∀ {n g} (p : C.GateProgram n g)
  (ws : List (C.WireRef n g)) k →
  T.gates (T.buildTable p ws k) ≡ tableCost (length ws) k + g
tableGates p [] k = refl
tableGates {g = g} p (w ∷ ws) k
  rewrite rowGates (T.program rest) (T.transport rest w) (T.outputs rest)
        | tableLength p ws k | tableGates p ws k =
  sym (N.+-assoc (twice k) (tableCost (length ws) k) g)
  where rest = T.buildTable p ws k

rowCost : ∀ {n} → T.Rows n → Nat
rowCost [] = zero
rowCost ((is , c) ∷ rs) = tableCost (length is) (length is) + rowCost rs

excessBound : ∀ {n} → T.Rows n → Nat
excessBound [] = zero
excessBound ((is , c) ∷ rs) = A.sub (length is) c + excessBound rs

aggregateLength : ∀ {n g} (p : C.GateProgram n g) (rs : T.Rows n) →
  length (T.outputs (T.buildAggregate p rs)) ≡ excessBound rs
aggregateLength p [] = refl
aggregateLength p ((is , c) ∷ rs)
  rewrite lenAppend (drop (suc c) (T.outputs row)) (map (T.transport row) (T.outputs rest))
        | lenDrop (suc c) (T.outputs row)
        | tableLength (T.program rest) (map C.inputWire is) (length is)
        | lenMap (T.transport row) (T.outputs rest)
        | aggregateLength p rs = refl
  where
    rest = T.buildAggregate p rs
    row = T.buildTable (T.program rest) (map C.inputWire is) (length is)

aggregateGates : ∀ {n g} (p : C.GateProgram n g) (rs : T.Rows n) →
  T.gates (T.buildAggregate p rs) ≡ rowCost rs + g
aggregateGates p [] = refl
aggregateGates {g = g} p ((is , c) ∷ rs)
  rewrite tableGates (T.program rest) (map C.inputWire is) (length is)
        | lenMap C.inputWire is | aggregateGates p rs =
  sym (N.+-assoc (tableCost (length is) (length is)) (rowCost rs) g)
  where rest = T.buildAggregate p rs

gateCountExact : ∀ {n} (rs : T.Rows n) k →
  C.gateCount (T.aggregateCircuit rs k) ≡
    suc (suc (tableCost (excessBound rs) (suc k) + (rowCost rs + zero)))
gateCountExact rs k
  rewrite tableGates (T.program r) (T.outputs r) (suc k)
        | aggregateLength C.noGates rs
        | aggregateGates C.noGates rs = refl
  where r = T.buildAggregate C.noGates rs

inputLength : ∀ {n} (is : List (Fin n)) (x : Vec Bool n) →
  length (T.inputBits is x) ≡ length is
inputLength [] x = refl
inputLength (i ∷ is) x = cong suc (inputLength is x)

potentialBound : ∀ {n} (rs : T.Rows n) (x : Vec Bool n) →
  A.potential rs x ≤ excessBound rs
potentialBound [] x = z≤n
potentialBound ((is , c) ∷ rs) x =
  N.+-mono-≤
    (A.subMono
      (subst (λ k → A.count (T.inputBits is x) ≤ k)
        (inputLength is x) (A.countBound (T.inputBits is x))) c)
    (potentialBound rs x)

minLeft : (a b : Nat) → A.mn a b ≤ a
minLeft a zero = z≤n
minLeft zero (suc b) = z≤n
minLeft (suc a) (suc b) = s≤s (minLeft a b)

minRight : (a b : Nat) → A.mn a b ≤ b
minRight a zero = z≤n
minRight zero (suc b) = z≤n
minRight (suc a) (suc b) = s≤s (minRight a b)

minGreatest : ∀ {w a b} → w ≤ a → w ≤ b → w ≤ A.mn a b
minGreatest z≤n q = z≤n
minGreatest (s≤s p) (s≤s q) = s≤s (minGreatest p q)

clamp : ∀ {n} → T.Rows n → Nat → Nat
clamp rs k = A.mn k (excessBound rs)

clampSound : ∀ {n} (rs : T.Rows n) k (x : Vec Bool n) →
  A.potential rs x ≤ clamp rs k → A.potential rs x ≤ k
clampSound rs k x h = N.≤-trans h (minLeft k (excessBound rs))

clampComplete : ∀ {n} (rs : T.Rows n) k (x : Vec Bool n) →
  A.potential rs x ≤ k → A.potential rs x ≤ clamp rs k
clampComplete rs k x h = minGreatest h (potentialBound rs x)

boundedCircuit : ∀ {n} → T.Rows n → Nat → C.ConcreteBooleanCircuit n
boundedCircuit rs k = T.aggregateCircuit rs (clamp rs k)

boundedDemandCNF : ∀ {n} (rs : T.Rows n) k → CNF.CNF n →
  CNF.CNF (n + C.gateCount (boundedCircuit rs k))
boundedDemandCNF rs k hard = H.DemandCNF rs (clamp rs k) hard

boundedDecode : ∀ {n} (rs : T.Rows n) k (hard : CNF.CNF n)
  (bits : CNF.Bits (n + C.gateCount (boundedCircuit rs k))) →
  CNF.evaluateCNF (boundedDemandCNF rs k hard) bits ≡ true →
  (H.hardValue hard (F.inputVectorFromGlobal bits) ≡ true) ×
  (A.potential rs (F.inputVectorFromGlobal bits) ≤ k)
boundedDecode rs k hard bits yes with H.decodeDemand rs (clamp rs k) hard bits yes
... | hd , cap = hd , clampSound rs k (F.inputVectorFromGlobal bits) cap

boundedEncode : ∀ {n} (rs : T.Rows n) k (hard : CNF.CNF n)
  (x : Vec Bool n) → H.hardValue hard x ≡ true → A.potential rs x ≤ k →
  CNF.evaluateCNF (boundedDemandCNF rs k hard)
    (H.canonicalBits rs (clamp rs k) x) ≡ true
boundedEncode rs k hard x hd cap =
  H.encodeDemand rs (clamp rs k) hard x hd (clampComplete rs k x cap)
