module DASHI.Codec.DNAProductionConstraints where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base; A; C; G; T; complement; ConstraintMachine )

infixr 6 _&&_
_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

not : Bool → Bool
not true = false
not false = true

baseEq : Base → Base → Bool
baseEq A A = true
baseEq C C = true
baseEq G G = true
baseEq T T = true
baseEq _ _ = false

isGC : Base → Bool
isGC C = true
isGC G = true
isGC _ = false

data Last : Set where
  noLast : Last
  last : Base → Last

data Run : Set where
  run0 run1 run2 run3 : Run

runAllows : Last → Run → Base → Bool
runAllows noLast r b = true
runAllows (last x) run3 b = not (baseEq x b)
runAllows (last x) r b = true

nextRun : Last → Run → Base → Run
nextRun noLast r b = run1
nextRun (last x) run1 b with baseEq x b
... | true = run2
... | false = run1
nextRun (last x) run2 b with baseEq x b
... | true = run3
... | false = run1
nextRun (last x) run3 b with baseEq x b
... | true = run3
... | false = run1
nextRun (last x) run0 b = run1

data Debt : Set where
  debtM2 debtM1 debt0 debtP1 debtP2 : Debt

debtAllows : Debt → Base → Bool
debtAllows debtM2 b = isGC b
debtAllows debtP2 b = not (isGC b)
debtAllows d b = true

nextDebt : Debt → Base → Debt
nextDebt debtM2 b with isGC b
... | true = debtM1
... | false = debtM2
nextDebt debtM1 b with isGC b
... | true = debt0
... | false = debtM2
nextDebt debt0 b with isGC b
... | true = debtP1
... | false = debtM1
nextDebt debtP1 b with isGC b
... | true = debtP2
... | false = debt0
nextDebt debtP2 b with isGC b
... | true = debtP2
... | false = debtP1

data MaybeBase : Set where
  none : MaybeBase
  some : Base → MaybeBase

record History9 : Set where
  constructor history9
  field
    h0 h1 h2 h3 h4 h5 h6 h7 h8 : MaybeBase
open History9 public

emptyHistory : History9
emptyHistory = history9 none none none none none none none none none

shiftHistory : History9 → Base → History9
shiftHistory h b =
  history9 (h1 h) (h2 h) (h3 h) (h4 h) (h5 h)
           (h6 h) (h7 h) (h8 h) (some b)

matches : MaybeBase → Base → Bool
matches none b = false
matches (some x) b = baseEq x b

forbidden4 : History9 → Base → Bool
forbidden4 h b =
  (matches (h6 h) G && matches (h7 h) A && matches (h8 h) T && baseEq b C)
  ||
  (matches (h6 h) C && matches (h7 h) T && matches (h8 h) A && baseEq b G)
  where
  infixr 5 _||_
  _||_ : Bool → Bool → Bool
  true || q = true
  false || q = q

hairpin3x4 : History9 → Base → Bool
hairpin3x4 h b =
  matchComplement (h2 h) (h7 h) &&
  matchComplement (h1 h) (h8 h) &&
  matchComplement (h0 h) (some b)
  where
  matchComplement : MaybeBase → MaybeBase → Bool
  matchComplement none y = false
  matchComplement x none = false
  matchComplement (some x) (some y) = baseEq (complement x) y

record ProductionState : Set where
  constructor productionState
  field
    previous : Last
    run : Run
    debt : Debt
    history : History9
open ProductionState public

initialState : ProductionState
initialState = productionState noLast run0 debt0 emptyHistory

legal? : ProductionState → Base → Bool
legal? s b =
  runAllows (previous s) (run s) b &&
  debtAllows (debt s) b &&
  not (forbidden4 (history s) b) &&
  not (hairpin3x4 (history s) b)

step : ProductionState → Base → ProductionState
step s b =
  productionState
    (last b)
    (nextRun (previous s) (run s) b)
    (nextDebt (debt s) b)
    (shiftHistory (history s) b)

IsTrue : Bool → Set
IsTrue b = b ≡ true

productionMachine : ConstraintMachine
productionMachine = record
  { State = ProductionState
  ; initial = initialState
  ; admissible = λ s b → IsTrue (legal? s b)
  ; step = step
  }

legal-witness-sound : ∀ {s b} → IsTrue (legal? s b) → legal? s b ≡ true
legal-witness-sound proof = proof

record ProductionConstraintReceipt : Set where
  field
    finiteInitial : ProductionState
    decision : ProductionState → Base → Bool
    transition : ProductionState → Base → ProductionState
    decisionMatchesMachine :
      ∀ {s b} → IsTrue (decision s b) → decision s b ≡ true

productionConstraintReceipt : ProductionConstraintReceipt
productionConstraintReceipt = record
  { finiteInitial = initialState
  ; decision = legal?
  ; transition = step
  ; decisionMatchesMachine = legal-witness-sound
  }
