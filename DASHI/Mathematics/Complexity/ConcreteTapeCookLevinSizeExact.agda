module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact where

------------------------------------------------------------------------
-- EXACT / POLYNOMIAL SIZE ACCOUNTING FOR THE CONCRETE COOK--LEVIN FORMULA
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

listLength :
  ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

mapLength :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  listLength (map f xs) ≡ listLength xs
mapLength f [] = refl
mapLength f (x ∷ xs)
    rewrite mapLength f xs =
  refl

allBitsLength :
  (n : Nat) →
  listLength (CNF.allBits n) ≡ 2 ^ n
allBitsLength zero = refl
allBitsLength (suc n)
    rewrite allBitsLength n =
  arithmetic
  where
    arithmetic :
      listLength
        (CNF.append
          (CNF.prependBit false (CNF.allBits n))
          (CNF.prependBit true (CNF.allBits n)))
      ≡ 2 ^ suc n
    arithmetic
      rewrite mapLength (λ bits → false CNF.∷ᵇ bits) (CNF.allBits n)
            | mapLength (λ bits → true CNF.∷ᵇ bits) (CNF.allBits n)
            | allBitsLength n =
      appendArithmetic
      where
        appendLength :
          ∀ {A : Set} (xs ys : List A) →
          listLength (CNF.append xs ys)
          ≡ listLength xs + listLength ys
        appendLength [] ys = refl
        appendLength (x ∷ xs) ys
            rewrite appendLength xs ys =
          refl

        appendArithmetic :
          listLength
            (CNF.append
              (CNF.prependBit false (CNF.allBits n))
              (CNF.prependBit true (CNF.allBits n)))
          ≡ 2 ^ suc n
        appendArithmetic
            rewrite appendLength
              (CNF.prependBit false (CNF.allBits n))
              (CNF.prependBit true (CNF.allBits n))
                  | mapLength
                      (λ bits → false CNF.∷ᵇ bits)
                      (CNF.allBits n)
                  | mapLength
                      (λ bits → true CNF.∷ᵇ bits)
                      (CNF.allBits n)
                  | allBitsLength n =
          refl

compileRejectedRows_length_le_source :
  ∀ {n}
    (predicate : CNF.Bits n → Bool)
    (rows : List (CNF.Bits n)) →
  Σ Nat (λ slack →
    listLength (CNF.compileRejectedRows predicate rows) + slack
    ≡ listLength rows)
compileRejectedRows_length_le_source predicate [] =
  zero , refl
compileRejectedRows_length_le_source predicate (row ∷ rows)
    with predicate row
... | true
    with compileRejectedRows_length_le_source predicate rows
... | slack , equality =
  suc slack , cong suc equality
... | false
    with compileRejectedRows_length_le_source predicate rows
... | slack , equality =
  slack , cong suc equality

truthTableCNF_clause_bound :
  ∀ {n}
    (predicate : CNF.Bits n → Bool) →
  Σ Nat (λ slack →
    listLength (CNF.truthTableCNF predicate) + slack
    ≡ 2 ^ n)
truthTableCNF_clause_bound {n} predicate
    with compileRejectedRows_length_le_source
      predicate (CNF.allBits n)
... | slack , equality
    rewrite allBitsLength n =
  slack , equality

timeSlotCount :
  (steps : Nat) →
  listLength (Transition.allSlots steps) ≡ steps
timeSlotCount zero = refl
timeSlotCount (suc steps)
    rewrite timeSlotCount steps
          | shiftLength (Transition.allSlots steps) =
  refl
  where
    shiftLength :
      ∀ {n} (xs : List (Transition.SomeSlot n)) →
      listLength (Transition.mapShiftSlots xs)
      ≡ listLength xs
    shiftLength [] = refl
    shiftLength (x ∷ xs)
        rewrite shiftLength xs =
      refl

windowStartCount :
  (cols : Nat) →
  Σ Nat (λ count →
    listLength (Transition.allWindowStarts cols) ≡ count)
windowStartCount zero = zero , refl
windowStartCount (suc zero) = zero , refl
windowStartCount (suc (suc zero)) = zero , refl
windowStartCount (suc (suc (suc rest)))
    with windowStartCount (suc (suc rest))
... | count , h =
  suc count , countStep
  where
    shiftLength :
      ∀ {n} (xs : List (Transition.SomeWindowStart n)) →
      listLength (Transition.mapShiftWindowStarts xs)
      ≡ listLength xs
    shiftLength [] = refl
    shiftLength (x ∷ xs)
        rewrite shiftLength xs =
      refl

    countStep :
      listLength
        (Transition.allWindowStarts
          (suc (suc (suc rest))))
      ≡ suc count
    countStep
        rewrite shiftLength
          (Transition.allWindowStarts (suc (suc rest)))
              | h =
      refl

extendedGlobalWidth_exact :
  ∀ (machine : Local.ConcreteTapeMachine)
    (steps cols : Nat) →
  Endpoint.ExtendedGlobalWidth machine steps cols
  ≡
  ((suc steps) * (cols * Canonical.CellWidth machine))
  + (steps * Selector.RuleWidth machine)
  + cols
extendedGlobalWidth_exact machine steps cols =
  refl

localTransitionTemplateWidth_machineConstant :
  ∀ (machine : Local.ConcreteTapeMachine) →
  Selected.TransitionLocalWidth machine
  ≡ Selector.RuleWidth machine + Canonical.WindowWidth machine
localTransitionTemplateWidth_machineConstant machine =
  refl

acceptanceTemplateWidth_machineConstant :
  ∀ (machine : Local.ConcreteTapeMachine) →
  Endpoint.AcceptanceLocalWidth machine
  ≡ suc (Canonical.CellWidth machine)
acceptanceTemplateWidth_machineConstant machine =
  refl

record ConcreteCookLevinSizeReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    exactVariableFormulaPaid : Bool
    localTransitionWidthMachineConstantPaid : Bool
    acceptanceWidthMachineConstantPaid : Bool
    truthTableClauseExponentialOnlyInMachineConstantPaid : Bool
    exactTimeSlotCountPaid : Bool
    finiteWindowStartCountPaid : Bool
    transitionGridPolynomialPaid : Bool
    endpointClausePolynomialPaid : Bool
    totalClausePolynomialPaid : Bool
    manyOneReductionPaid : Bool
    pVsNPResolved : Bool

concreteCookLevinSizeReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  ConcreteCookLevinSizeReceipt machine
concreteCookLevinSizeReceipt machine = record
  { exactVariableFormulaPaid = true
  ; localTransitionWidthMachineConstantPaid = true
  ; acceptanceWidthMachineConstantPaid = true
  ; truthTableClauseExponentialOnlyInMachineConstantPaid = true
  ; exactTimeSlotCountPaid = true
  ; finiteWindowStartCountPaid = true
  ; transitionGridPolynomialPaid = false
  ; endpointClausePolynomialPaid = false
  ; totalClausePolynomialPaid = false
  ; manyOneReductionPaid = false
  ; pVsNPResolved = false
  }
