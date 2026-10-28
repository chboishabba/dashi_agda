module DASHI.Arithmetic.PrimegameTypedNumericFirstApplicableBidiExact where

------------------------------------------------------------------------
-- GUY'S 14 TYPED SSP FACTOR RULES <-> EXACT NUMERIC RULE PRIORITY
--
-- Original mathematics: Conway (1987), Guy (1983) FRACTRAN.
-- Source owners: PrimegameSSP15CarrierFactorisationExact owns
-- the precise ordered 14-rule program with ten SSP prime factors.
-- FRACDASHNumericInterpreterTargetExact owns FirstApplicableStep.
--
-- NEW: rule renaming through the exact factorisation preserves AND
-- reflects the same first applicable rule and blocked-program halt.
-- This explicitly closes the *program representation* BIDI seam.
-- It does not claim that any external signed-SSP/FRACDASH runtime
-- has its integer arithmetic evaluator or compiled state aligned.
--
-- ExactFractionApplies is mathematical denominator divisibility,
-- witnessed by an integer successor and a nonzero denominator.
-- A concrete apply operation must additionally produce that
-- successor; it is NOT silently postulated here.
--
-- Do not conflate 14 programme rules, 10 factors, 15 SSP lanes,
-- 3×3×3 geometry, 3×5 Ibrahim orbit codes or Monster 3B.
-- This is source-written / Agda-kernel pending; no ESD edits.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (_≟_; *-identityʳ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; trans; subst; sym)
open import Data.Empty using (⊥-elim)
import Data.Nat.DivMod as DivMod
open DivMod using (_/_; _%_)

import DASHI.Arithmetic.PrimegameSSP15CarrierFactorisationExact as Guy
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Programmes.FRACDASHNumericInterpreterTargetExact as First

RuleNumbers : Set
RuleNumbers = Nat × Nat

TypedApplies :
  (Nat → RuleNumbers → Set) →
  Nat → Guy.TypedFraction → Set
TypedApplies applies n fraction =
  applies n (Guy.fractionNumbers fraction)

TypedApply :
  (Nat → RuleNumbers → Nat) →
  Nat → Guy.TypedFraction → Nat
TypedApply apply n fraction =
  apply n (Guy.fractionNumbers fraction)

-- Actual numeric integrality criterion for one fraction a/d.
-- n*a = next*d with d nonzero. A witness is not inferred from
-- simply carrying the numerator and denominator prime labels.
ExactFractionApplies : Nat → RuleNumbers → Set
ExactFractionApplies n fraction =
  (proj₂ fraction ≢ zero) ×
  Σ Nat (λ next →
    next * proj₂ fraction ≡ n * proj₁ fraction)

TypedExactFractionApplies : Nat → Guy.TypedFraction → Set
TypedExactFractionApplies =
  TypedApplies ExactFractionApplies

-- A concrete evaluator has to return precisely the integer
-- successor certified by the guard. This remains an explicit
-- execution receipt, not an unproved claim about a satellite.
record ExactFractionEvaluator : Set where
  field
    next : Nat → RuleNumbers → Nat
    preservesExactValue :
      (n : Nat) (rule : RuleNumbers) →
      ExactFractionApplies n rule →
      next n rule * proj₂ rule ≡ n * proj₁ rule

open ExactFractionEvaluator public

-- Directly reuse the source-owned inductive priority semantics.
-- The recursive proof retains *every failed prefix guard*.
typedStepToNumeric :
  ∀ {applies : Nat → RuleNumbers → Set}
    {apply : Nat → RuleNumbers → Nat}
    {rules : List Guy.TypedFraction}
    {before after : Nat} →
  First.FirstApplicableStep
    (TypedApplies applies) (TypedApply apply)
    rules before after →
  First.FirstApplicableStep
    applies apply
    (Guy.mapFractionNumbers rules) before after
typedStepToNumeric (First.choose-head present) =
  First.choose-head present
typedStepToNumeric (First.skip-head blocked rest) =
  First.skip-head blocked (typedStepToNumeric rest)

numericStepToTyped :
  ∀ {applies : Nat → RuleNumbers → Set}
    {apply : Nat → RuleNumbers → Nat}
    {rules : List Guy.TypedFraction}
    {before after : Nat} →
  First.FirstApplicableStep
    applies apply
    (Guy.mapFractionNumbers rules) before after →
  First.FirstApplicableStep
    (TypedApplies applies) (TypedApply apply)
    rules before after
numericStepToTyped (First.choose-head present) =
  First.choose-head present
numericStepToTyped (First.skip-head blocked rest) =
  First.skip-head blocked (numericStepToTyped rest)

-- Specialise to the historical 14-rule Guy list using the
-- *inherited* typed-factorisation equality, not a re-entered list.
guyTypedToNumeric :
  (applies : Nat → RuleNumbers → Set)
  (apply : Nat → RuleNumbers → Nat)
  {before after : Nat} →
  First.FirstApplicableStep
    (TypedApplies applies) (TypedApply apply)
    Guy.guyFourteenTyped before after →
  First.FirstApplicableStep
    applies apply Guy.guyFourteenNumeric before after
guyTypedToNumeric applies apply {before} {after} step =
  subst
    (λ rules → First.FirstApplicableStep
      applies apply rules before after)
    Guy.typedFractionsAreExactGuyFourteen
    (typedStepToNumeric step)

guyNumericToTyped :
  (applies : Nat → RuleNumbers → Set)
  (apply : Nat → RuleNumbers → Nat)
  {before after : Nat} →
  First.FirstApplicableStep
    applies apply Guy.guyFourteenNumeric before after →
  First.FirstApplicableStep
    (TypedApplies applies) (TypedApply apply)
    Guy.guyFourteenTyped before after
guyNumericToTyped applies apply {before} {after} step =
  numericStepToTyped
    (subst
      (λ rules → First.FirstApplicableStep
        applies apply rules before after)
      (sym Guy.typedFractionsAreExactGuyFourteen)
      step)

-- A list halts when *no* fraction guard is applicable.
-- This is stronger than a test that merely fails the first rule.
NoApplicable : ∀ {Rule : Set} →
  (Nat → Rule → Set) → Nat → List Rule → Set
NoApplicable applies n [] = ⊤
NoApplicable applies n (r ∷ rest) =
  ¬ (applies n r) × NoApplicable applies n rest

typedHaltToNumeric :
  ∀ {applies : Nat → RuleNumbers → Set}
    {rules : List Guy.TypedFraction} {n : Nat} →
  NoApplicable (TypedApplies applies) n rules →
  NoApplicable applies n (Guy.mapFractionNumbers rules)
typedHaltToNumeric {rules = []} halt = tt
typedHaltToNumeric {rules = _ ∷ _} (blocked , rest) =
  blocked , typedHaltToNumeric rest

numericHaltToTyped :
  ∀ {applies : Nat → RuleNumbers → Set}
    {rules : List Guy.TypedFraction} {n : Nat} →
  NoApplicable applies n (Guy.mapFractionNumbers rules) →
  NoApplicable (TypedApplies applies) n rules
numericHaltToTyped {rules = []} halt = tt
numericHaltToTyped {rules = _ ∷ _} (blocked , rest) =
  blocked , numericHaltToTyped rest

guyTypedHaltToNumeric :
  (applies : Nat → RuleNumbers → Set) {n : Nat} →
  NoApplicable (TypedApplies applies) n Guy.guyFourteenTyped →
  NoApplicable applies n Guy.guyFourteenNumeric
guyTypedHaltToNumeric applies {n} halt =
  subst
    (NoApplicable applies n)
    Guy.typedFractionsAreExactGuyFourteen
    (typedHaltToNumeric halt)

guyNumericHaltToTyped :
  (applies : Nat → RuleNumbers → Set) {n : Nat} →
  NoApplicable applies n Guy.guyFourteenNumeric →
  NoApplicable (TypedApplies applies) n Guy.guyFourteenTyped
guyNumericHaltToTyped applies {n} halt =
  numericHaltToTyped
    (subst
      (NoApplicable applies n)
      (sym Guy.typedFractionsAreExactGuyFourteen)
      halt)

-- Concrete exact denominator guard; the action still needs an
-- evaluator receipt to enter a full signed machine proof.
guyExactGuardPriorityForward :
  (evaluator : ExactFractionEvaluator) {before after : Nat} →
  First.FirstApplicableStep
    TypedExactFractionApplies (TypedApply (next evaluator))
    Guy.guyFourteenTyped before after →
  First.FirstApplicableStep
    ExactFractionApplies (next evaluator)
    Guy.guyFourteenNumeric before after
guyExactGuardPriorityForward evaluator =
  guyTypedToNumeric ExactFractionApplies (next evaluator)

guyExactGuardPriorityBackward :
  (evaluator : ExactFractionEvaluator) {before after : Nat} →
  First.FirstApplicableStep
    ExactFractionApplies (next evaluator)
    Guy.guyFourteenNumeric before after →
  First.FirstApplicableStep
    TypedExactFractionApplies (TypedApply (next evaluator))
    Guy.guyFourteenTyped before after
guyExactGuardPriorityBackward evaluator =
  guyNumericToTyped ExactFractionApplies (next evaluator)

historicalRuleCount : Signed.listCount Guy.guyFourteenTyped ≡ 14
historicalRuleCount = Guy.guyProgrammeRuleCountIsFourteen

------------------------------------------------------------------------
-- CONCRETE ARITHMETIC EVALUATOR. The canonical stdlib quotient
-- closes the exact Nat successor, with *no* action oracle.
-- Only the signed-SSP/FRACDASH state alignment remains separate.
------------------------------------------------------------------------

exactNumericNext : Nat → RuleNumbers → Nat
exactNumericNext n (a , zero) = zero
exactNumericNext n (a , suc d) = (n * a) / suc d

-- For d>0 with m*d=n*a, division's remainder vanishes. Reuse
-- the canonical division algorithm and multiple-modulo theorem.
exactNumericNextIsCorrect :
  (n : Nat) (rule : RuleNumbers) →
  ExactFractionApplies n rule →
  exactNumericNext n rule * proj₂ rule ≡ n * proj₁ rule
exactNumericNextIsCorrect n (a , zero) (nonzero , _) =
  ⊥-elim (nonzero refl)
exactNumericNextIsCorrect n (a , suc d)
    (_ , (integralNext , productEq)) =
  sym
    (trans
      (DivMod.m≡m%n+[m/n]*n (n * a) (suc d))
      (trans
        (cong
          (λ r → r + ((n * a) / suc d) * suc d)
          (trans
            (cong (λ v → v % suc d) (sym productEq))
            (DivMod.m*n%n≡0 integralNext (suc d))))
        refl))

concreteExactFractionEvaluator : ExactFractionEvaluator
concreteExactFractionEvaluator = record
  { next = exactNumericNext
  ; preservesExactValue = exactNumericNextIsCorrect
  }

guyConcreteExactPriorityForward :
  {before after : Nat} →
  First.FirstApplicableStep
    TypedExactFractionApplies (TypedApply exactNumericNext)
    Guy.guyFourteenTyped before after →
  First.FirstApplicableStep
    ExactFractionApplies exactNumericNext
    Guy.guyFourteenNumeric before after
guyConcreteExactPriorityForward =
  guyExactGuardPriorityForward concreteExactFractionEvaluator

guyConcreteExactPriorityBackward :
  {before after : Nat} →
  First.FirstApplicableStep
    ExactFractionApplies exactNumericNext
    Guy.guyFourteenNumeric before after →
  First.FirstApplicableStep
    TypedExactFractionApplies (TypedApply exactNumericNext)
    Guy.guyFourteenTyped before after
guyConcreteExactPriorityBackward =
  guyExactGuardPriorityBackward concreteExactFractionEvaluator

------------------------------------------------------------------------
-- DECIDABLE ACTUAL FIRST-APPLICABLE NUMERIC INTERPRETER.
-- This closes the remaining *numerical* scanner cut. Its relation
-- proof reuses FirstApplicableStep and NoApplicable above.
------------------------------------------------------------------------

exactFractionApplies? :
  (n : Nat) (rule : RuleNumbers) →
  Dec (ExactFractionApplies n rule)
exactFractionApplies? n (a , zero) =
  no (λ (nonzero , _) → nonzero refl)
exactFractionApplies? n (a , suc d)
  with ((n * a) % suc d) ≟ zero
... | yes remainderZero =
  yes
    ( (λ ())
    , ( (n * a) / suc d
      , sym
          (trans
            (DivMod.m≡m%n+[m/n]*n (n * a) (suc d))
            (trans
              (cong
                (λ r → r + ((n * a) / suc d) * suc d)
                remainderZero)
              refl))
      ))
... | no remainderNonzero =
  no (λ (_ , (candidate , productEq)) →
    remainderNonzero
      (trans
        (cong (λ v → v % suc d) (sym productEq))
        (DivMod.m*n%n≡0 candidate (suc d))))

firstApplicableNumeric : List RuleNumbers → Nat → Maybe Nat
firstApplicableNumeric [] n = nothing
firstApplicableNumeric (rule ∷ rest) n
  with exactFractionApplies? n rule
... | yes _ = just (exactNumericNext n rule)
... | no _ = firstApplicableNumeric rest n

firstApplicableNumericSound :
  (rules : List RuleNumbers) (n : Nat) {after : Nat} →
  firstApplicableNumeric rules n ≡ just after →
  First.FirstApplicableStep
    ExactFractionApplies exactNumericNext
    rules n after
firstApplicableNumericSound [] n ()
firstApplicableNumericSound (rule ∷ rest) n {after} equality
  with exactFractionApplies? n rule
... | yes applicable with equality
... | yes applicable | refl = First.choose-head applicable
... | no blocked =
  First.skip-head blocked
    (firstApplicableNumericSound rest n equality)

firstApplicableNumericHalt :
  (rules : List RuleNumbers) (n : Nat) →
  firstApplicableNumeric rules n ≡ nothing →
  NoApplicable ExactFractionApplies n rules
firstApplicableNumericHalt [] n equal = tt
firstApplicableNumericHalt (rule ∷ rest) n equal
  with exactFractionApplies? n rule
... | yes applicable with equal
... | yes applicable | ()
... | no blocked =
  blocked , firstApplicableNumericHalt rest n equal

-- Specialise back to the actual historical Guy list, not an
-- arbitrary 14-element bag.
guyNumericExecutableStepSound :
  (n : Nat) {after : Nat} →
  firstApplicableNumeric Guy.guyFourteenNumeric n ≡ just after →
  First.FirstApplicableStep
    ExactFractionApplies exactNumericNext
    Guy.guyFourteenNumeric n after
guyNumericExecutableStepSound =
  firstApplicableNumericSound Guy.guyFourteenNumeric

guyTypedExecutableStepSound :
  (n : Nat) {after : Nat} →
  firstApplicableNumeric Guy.guyFourteenNumeric n ≡ just after →
  First.FirstApplicableStep
    TypedExactFractionApplies (TypedApply exactNumericNext)
    Guy.guyFourteenTyped n after
guyTypedExecutableStepSound n witness =
  guyConcreteExactPriorityBackward
    (guyNumericExecutableStepSound n witness)

guyNumericExecutableHalt :
  (n : Nat) →
  firstApplicableNumeric Guy.guyFourteenNumeric n ≡ nothing →
  NoApplicable ExactFractionApplies n Guy.guyFourteenNumeric
guyNumericExecutableHalt =
  firstApplicableNumericHalt Guy.guyFourteenNumeric

guyTypedExecutableHalt :
  (n : Nat) →
  firstApplicableNumeric Guy.guyFourteenNumeric n ≡ nothing →
  NoApplicable TypedExactFractionApplies n Guy.guyFourteenTyped
guyTypedExecutableHalt n witness =
  guyNumericHaltToTyped ExactFractionApplies
    (guyNumericExecutableHalt n witness)

-- Executable policy has its own test fixture. Its source-level proof
-- does not assert a compiled signed SSP/FRACDASH executor or a global
-- theorem about all prime readouts.

------------------------------------------------------------------------
-- HISTORICAL READOUT ≠ HALTING.
-- Guy's final fraction is 55/1. Every Nat state has an applicable
-- rule. The source computation may emit prime markers along an
-- ongoing trace, never by ordinary terminal program halting.
------------------------------------------------------------------------

guyLastRuleAlwaysApplies : (n : Nat) →
  ExactFractionApplies n (55 , 1)
guyLastRuleAlwaysApplies n =
  (λ ()) , ((n * 55) , *-identityʳ (n * 55))

guyBlockedPrefixCannotIncludeLast :
  (n : Nat) →
  NoApplicable ExactFractionApplies n Guy.guyFourteenNumeric →
  (ExactFractionApplies n (55 , 1) → ⊥)
guyBlockedPrefixCannotIncludeLast n blocked =
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (blocked))))))))))))))

guyNumericScannerNeverHalts :
  (n : Nat) →
  firstApplicableNumeric Guy.guyFourteenNumeric n ≡ nothing → ⊥
guyNumericScannerNeverHalts n apparentHalt =
  guyBlockedPrefixCannotIncludeLast n
    (guyNumericExecutableHalt n apparentHalt)
    (guyLastRuleAlwaysApplies n)

-- This theorem blocks the false claim that a prime marker is an
-- ordinary terminal output. No universal prime-emission theorem
-- follows from the existence of this always-applicable last rule.
