module DASHI.Mathematics.Complexity.PNPCookEndpointOffsetsExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (take)
import Data.Nat.Properties as N
import Data.Fin.Base as Fin
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import DASHI.Mathematics.Complexity.PNPCookPlacedWindowAffineLengthExact as P
import DASHI.Mathematics.Complexity.PNPCookAffineSeekGeometryExact as A
import DASHI.Mathematics.Complexity.PNPCookFlattenedPrefixExact as F
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as T
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as D
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as R
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as G
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as E
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global

zerosBefore : ∀ {n} → Nat → CNF.Bits n → Nat
zerosBefore zero bits = zero
zerosBefore (suc k) CNF.[]ᵇ = zero
zerosBefore (suc k) (false CNF.∷ᵇ xs) = suc (zerosBefore k xs)
zerosBefore (suc k) (true CNF.∷ᵇ xs) = zerosBefore k xs

zerosBound : ∀ {n} k (bits : CNF.Bits n) → zerosBefore k bits ≤ k
zerosBound zero bits = z≤n
zerosBound (suc k) CNF.[]ᵇ = z≤n
zerosBound (suc k) (false CNF.∷ᵇ xs) = s≤s (zerosBound k xs)
zerosBound (suc k) (true CNF.∷ᵇ xs) =
  N.≤-trans (zerosBound k xs) (N.n≤1+n k)

unitPrefixWidth : ∀ {n m} (rename : Fin.Fin n → Fin.Fin m) p
  (bits : CNF.Bits n) k → k ≤ n →
  (∀ i → Fin.toℕ (rename i) ≡ p + Fin.toℕ i) →
  F.bodyWidth (take k (E.unitClausesForTarget rename bits)) ≡
    F.tri k + (p + 5) * k + zerosBefore k bits
unitPrefixWidth rename p bits zero hk h =
  solve 1 (λ p → con 0 := con 0 :+ (p :+ con 5) :* con 0 :+ con 0) refl p
unitPrefixWidth rename p (false CNF.∷ᵇ bits) (suc k) (s≤s hk) h
  rewrite h Fin.zero |
    unitPrefixWidth (λ i → rename (Fin.suc i)) (suc p) bits k hk next =
  solve 4 (λ p k t z → con 6 :+ p :+ (t :+ (con 1 :+ p :+ con 5) :* k :+ z) :=
    (t :+ k) :+ (p :+ con 5) :* (con 1 :+ k) :+ (con 1 :+ z))
    refl p k (F.tri k) (zerosBefore k bits)
  where
    next : ∀ i → Fin.toℕ (rename (Fin.suc i)) ≡ suc p + Fin.toℕ i
    next i = trans (h (Fin.suc i)) (N.+-suc p (Fin.toℕ i))
unitPrefixWidth rename p (true CNF.∷ᵇ bits) (suc k) (s≤s hk) h
  rewrite h Fin.zero |
    unitPrefixWidth (λ i → rename (Fin.suc i)) (suc p) bits k hk next =
  solve 4 (λ p k t z → con 5 :+ p :+ (t :+ (con 1 :+ p :+ con 5) :* k :+ z) :=
    (t :+ k) :+ (p :+ con 5) :* (con 1 :+ k) :+ z)
    refl p k (F.tri k) (zerosBefore k bits)
  where
    next : ∀ i → Fin.toℕ (rename (Fin.suc i)) ≡ suc p + Fin.toℕ i
    next i = trans (h (Fin.suc i)) (N.+-suc p (Fin.toℕ i))

initialPrefixWidth : ∀ {machine steps cols}
  (bits : CNF.Bits (D.RowBitsWidth machine cols)) k →
  k ≤ D.RowBitsWidth machine cols →
  F.bodyWidth (take k (E.initialEndpointCNF {machine} {steps} {cols} bits)) ≡
    F.tri k + 5 * k + zerosBefore k bits
initialPrefixWidth {machine} {steps} {cols} bits k h =
  unitPrefixWidth (E.initialRowExtendedRename {machine} {steps} {cols}) zero bits k h
    (λ i → trans (A.leftIndex _) (A.rowIndex {machine} {steps} {cols} G.here i))

finSum : ∀ {n} a c → List (Fin.Fin n) → Nat
finSum a c = P.sumMap (λ i → a * Fin.toℕ i + c)

shiftFinSum : ∀ {n} a c (xs : List (Fin.Fin n)) →
  finSum a c (E.mapFinSuc xs) ≡ finSum a (a + c) xs
shiftFinSum a c [] = refl
shiftFinSum a c (x ∷ xs) rewrite shiftFinSum a c xs =
  cong (_+ finSum a (a + c) xs)
    (solve 3 (λ a x c → a :* (con 1 :+ x) :+ c :=
      a :* x :+ (a :+ c)) refl a (Fin.toℕ x) c)

takeFinShift : ∀ {n} k (xs : List (Fin.Fin n)) →
  take k (E.mapFinSuc xs) ≡ E.mapFinSuc (take k xs)
takeFinShift zero xs = refl
takeFinShift (suc k) [] = refl
takeFinShift (suc k) (x ∷ xs) rewrite takeFinShift k xs = refl

finPrefixSum : ∀ a c k n → k ≤ n →
  finSum a c (take k (E.finList n)) ≡ a * F.tri k + c * k
finPrefixSum a c zero n h = P.allSlotSum a c zero
finPrefixSum a c (suc k) (suc n) (s≤s h)
  rewrite takeFinShift k (E.finList n)
        | shiftFinSum a c (take k (E.finList n))
        | finPrefixSum a (a + c) k n h =
  solve 4 (λ a c k u → (a :* con 0 :+ c) :+
    (a :* u :+ (a :+ c) :* k) :=
    a :* (u :+ k) :+ c :* (con 1 :+ k)) refl a c k (F.tri k)

finFullSum : ∀ a c n → finSum a c (E.finList n) ≡ a * F.tri n + c * n
finFullSum a c zero = P.allSlotSum a c zero
finFullSum a c (suc n)
  rewrite shiftFinSum a c (E.finList n) | finFullSum a (a + c) n =
  solve 4 (λ a c n u → (a :* con 0 :+ c) :+
    (a :* u :+ (a :+ c) :* n) :=
    a :* (u :+ n) :+ c :* (con 1 :+ n)) refl a c n (F.tri n)

module Acceptance (machine : L.ConcreteTapeMachine) (steps cols : Nat)
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine)) where

  gw = T.GlobalTraceWidth machine steps cols
  rw = D.RowBitsWidth machine cols
  w = C.CellWidth machine

  coeff : Fin.Fin (E.AcceptanceLocalWidth machine) → P.Coeff
  coeff Fin.zero = P.coeff 0 1 gw
  coeff (Fin.suc i) = P.coeff 0 w (steps * rw + Fin.toℕ i)

  coeffExact : ∀ (j : Fin.Fin cols) i →
    Fin.toℕ (E.acceptanceLocalRename {machine} {steps} {cols} (E.finToSlot j) i) ≡
      P.eval (coeff i) zero (Fin.toℕ j)
  coeffExact j Fin.zero
    rewrite E.acceptanceLocalRename_zero_eq_witnessIndex {machine} {steps} {cols} j =
    trans (A.rightIndex gw j)
      (solve 2 (λ g j → g :+ j := con 0 :* con 0 :+ con 1 :* j :+ g) refl gw (Fin.toℕ j))
  coeffExact j (Fin.suc i) =
    trans (A.leftIndex _)
      (trans (A.cellIndex {machine} {steps} {cols} (E.finalRowSlot steps) (E.finToSlot j) i)
        (solve 5 (λ t row j w k → t :* row :+ (j :* w :+ k) :=
          con 0 :* con 0 :+ w :* j :+ (t :* row :+ k))
          refl steps rw (Fin.toℕ j) w (Fin.toℕ i)))

  template = CNF.truthTableCNF (E.witnessAcceptingPredicate {machine} sc ac)
  block = P.bodyCoeff coeff template

  blockExact : ∀ j →
    F.bodyWidth (Placed.compilePlaced
      (E.acceptancePlacedPredicate {machine} {steps} {cols} sc ac (E.finToSlot j))) ≡
      P.eval block zero (Fin.toℕ j)
  blockExact j = P.bodyExact coeff
    (E.acceptanceLocalRename {machine} {steps} {cols} (E.finToSlot j))
    zero (Fin.toℕ j) (coeffExact j) template

  implicationSum : ∀ (xs : List (Fin.Fin cols)) →
    F.bodyWidth (Placed.compilePlacedAll
      (E.acceptanceImplicationPredicatesFin {machine} {steps} {cols} sc ac xs)) ≡
      finSum (P.column block) (P.constant block) xs
  implicationSum [] = refl
  implicationSum (j ∷ xs)
    rewrite F.placedAppendSame
      (Placed.compilePlaced (E.acceptancePlacedPredicate {machine} {steps} {cols} sc ac (E.finToSlot j)))
      (Placed.compilePlacedAll (E.acceptanceImplicationPredicatesFin {machine} {steps} {cols} sc ac xs))
    | F.bodyWidthAppend
      (Placed.compilePlaced (E.acceptancePlacedPredicate {machine} {steps} {cols} sc ac (E.finToSlot j)))
      (Placed.compilePlacedAll (E.acceptanceImplicationPredicatesFin {machine} {steps} {cols} sc ac xs))
    | blockExact j | implicationSum xs
    | N.*-zeroʳ (P.time block) = refl

  implicationPrefix : ∀ k → k ≤ cols →
    F.bodyWidth (Placed.compilePlacedAll
      (E.acceptanceImplicationPredicatesFin {machine} {steps} {cols} sc ac (take k (E.finList cols)))) ≡
      P.column block * F.tri k + P.constant block * k
  implicationPrefix k hk =
    trans (implicationSum (take k (E.finList cols)))
      (finPrefixSum (P.column block) (P.constant block) k cols hk)

  witnessClause : List (Fin.Fin cols) → CNF.Clause (E.ExtendedGlobalWidth machine steps cols)
  witnessClause xs = E.allWitnessPositiveLiterals
    (λ i → CNF.positive (E.witnessIndex {machine} {steps} {cols} i)) xs

  witnessWidth : ∀ xs → F.clauseWidth (witnessClause xs) ≡ suc (finSum 1 (gw + 3) xs)
  witnessWidth [] = refl
  witnessWidth (j ∷ xs)
    rewrite A.rightIndex gw j | witnessWidth xs =
    solve 3 (λ g j s → con 1 :+ (con 2 :+ (g :+ j) :+ (con 1 :+ s)) :=
      con 1 :+ (con 1 :* j :+ (g :+ con 3) :+ s))
      refl gw (Fin.toℕ j) (finSum 1 (gw + 3) xs)

  witnessBodyWidth :
    suc (F.clauseWidth (E.someAcceptanceWitnessClause {machine} {steps} {cols})) ≡
      2 + (F.tri cols + (gw + 3) * cols)
  witnessBodyWidth rewrite witnessWidth (E.finList cols)
    | finFullSum 1 (gw + 3) cols | N.*-identityˡ (F.tri cols) = refl

  acceptanceWidth :
    F.bodyWidth (E.acceptingEndpointCNF {machine} {steps} {cols} sc ac) ≡
      (2 + (F.tri cols + (gw + 3) * cols)) +
      (P.column block * F.tri cols + P.constant block * cols)
  acceptanceWidth
    rewrite implicationSum (E.finList cols)
      | finFullSum (P.column block) (P.constant block) cols =
    trans (sym (N.+-assoc 1 (F.clauseWidth (E.someAcceptanceWitnessClause {machine} {steps} {cols}))
      (P.column block * F.tri cols + P.constant block * cols)))
      (cong (λ x → x + (P.column block * F.tri cols + P.constant block * cols)) witnessBodyWidth)

-- Exact initial prefixes and actual acceptance template offsets. Native
-- end-to-end arithmetic seek still needs implementation of the compact ABI
-- and kernel acceptance. No assertion of own-horizon physical execution.
