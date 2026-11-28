module DASHI.Mathematics.Complexity.PNPHardAffineGateCountExact where

-- Exact count on the actual hard-prefix + aggregate GateProgram.
-- Counts emitted gates, not solver runtime or formula expansion.
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import Data.Nat.Properties as N
import DASHI.Mathematics.Complexity.PNPHardAffineGateExact as H
import DASHI.Mathematics.Complexity.PNPAggregateGateCountExact as G
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C

parityCost : ∀ {n} → List (Fin n) → Nat
parityCost [] = 1
parityCost (i ∷ is) = suc (suc (suc (suc (parityCost is))))

normalCost : ∀ {n} → H.Normal n → Nat
normalCost (is , true) = parityCost is
normalCost (is , false) = suc (parityCost is)

flatCost : ∀ {n} → H.Flat n → Nat
flatCost [] = 1
flatCost (a ∷ as) = suc (flatCost as + normalCost a)

allowedCost : ∀ {n} → List (H.Flat n) → Nat
allowedCost [] = 1
allowedCost (a ∷ as) = suc (allowedCost as + suc (flatCost a))

hardCost : ∀ {n} → H.Flat n → List (H.Flat n) → Nat
hardCost h fs = suc (allowedCost fs + flatCost h)

parityGates : ∀ {n g} (p : C.GateProgram n g) (is : List (Fin n)) →
  H.Result.gates (H.compileParity p is) ≡ parityCost is + g
parityGates p [] = refl
parityGates p (i ∷ is) = cong (λ z → suc (suc (suc (suc z)))) (parityGates p is)

normalGates : ∀ {n g} (p : C.GateProgram n g) (a : H.Normal n) →
  H.Result.gates (H.compileNormal p a) ≡ normalCost a + g
normalGates p (is , true) = parityGates p is
normalGates p (is , false) = cong suc (parityGates p is)

flatGates : ∀ {n g} (p : C.GateProgram n g) (as : H.Flat n) →
  H.Result.gates (H.compileFlat p as) ≡ flatCost as + g
flatGates p [] = refl
flatGates {g = g} p (a ∷ as)
  rewrite flatGates (H.Result.program (H.compileNormal p a)) as
        | normalGates p a = cong suc (sym (N.+-assoc (flatCost as) (normalCost a) g))

allowedGates : ∀ {n g} (p : C.GateProgram n g) (fs : List (H.Flat n)) →
  H.Result.gates (H.compileAllowed p fs) ≡ allowedCost fs + g
allowedGates p [] = refl
allowedGates {g = g} p (a ∷ as)
  rewrite allowedGates (H.Result.program (H.negateResult (H.compileFlat p a))) as
        | flatGates p a = cong suc (sym (N.+-assoc (allowedCost as) (suc (flatCost a)) g))

hardGates : ∀ {n g} (p : C.GateProgram n g) (h : H.Flat n) (fs : List (H.Flat n)) →
  H.Result.gates (H.compileHard p h fs) ≡ hardCost h fs + g
hardGates {g = g} p h fs
  rewrite allowedGates (H.Result.program (H.compileFlat p h)) fs
        | flatGates p h = cong suc (sym (N.+-assoc (allowedCost fs) (flatCost h) g))

combinedGates : ∀ {n} (h : H.Flat n) (fs : List (H.Flat n)) (rs : T.Rows n) k →
  C.gateCount (H.compileDemand h fs rs k) ≡
  suc (suc (suc (G.tableCost (G.excessBound rs) (suc k) +
    (G.rowCost rs + (hardCost h fs + zero)))))
combinedGates h fs rs k
  rewrite G.tableGates (T.program a) (T.outputs a) (suc k)
        | G.aggregateLength (H.Result.program r) rs
        | G.aggregateGates (H.Result.program r) rs
        | hardGates C.noGates h fs = refl
  where
    r = H.compileHard C.noGates h fs
    a = T.buildAggregate (H.Result.program r) rs

-- For the actual bounded demand replace k by G.clamp rs k.
-- Four gates per XOR occurrence, one constant per parity/conjunction,
-- one optional negation per equation and one exclusion per flat.
-- Thus linear hard-prefix cost plus the existing quadratic aggregate.
