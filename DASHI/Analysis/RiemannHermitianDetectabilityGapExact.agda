module DASHI.Analysis.RiemannHermitianDetectabilityGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / SCALE CALIBRATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- Their prime-side Theorem [thm:traces] gives
--
--   tr Gtilde^2
--     = (T L / 2pi) (ell_1^2 + L^2/3) (1 + O(E_T)),
--
-- not a quantity tending to zero.  Therefore a Hermitian transverse defect can
-- only force RH from this lane after subtracting/identifying the compatible
-- main term and proving the surviving defect is detectable above the remaining
-- arithmetic error floor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
congSuc refl = refl

congTail : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
congTail refl c = refl

congTwoTails :
  {a b : Nat} → a ≡ b → (c d : Nat) → (a + c) + d ≡ (b + c) + d
congTwoTails refl c d = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = congSuc (+-assoc a b c)

selfPlusPositiveImpossible :
  (n extra : Nat) → n + suc extra ≡ n → ⊥
selfPlusPositiveImpossible zero extra ()
selfPlusPositiveImpossible (suc n) extra eq =
  selfPlusPositiveImpossible n extra (dropSuc eq)
  where
  dropSuc : {a b : Nat} → suc a ≡ suc b → a ≡ b
  dropSuc refl = refl

record ExcessErrorLedger : Set where
  constructor excessErrorLedger
  field
    aggregateDefect : Nat
    errorBudget : Nat
    errorSlack : Nat
    aggregateWithinError :
      aggregateDefect + errorSlack ≡ errorBudget

open ExcessErrorLedger public

record HypotheticalOffLineWitness (ledger : ExcessErrorLedger) : Set where
  constructor hypotheticalOffLineWitness
  field
    singlePairDefect : Nat
    otherDefect : Nat
    pairInsideAggregate :
      singlePairDefect + otherDefect ≡ aggregateDefect ledger

open HypotheticalOffLineWitness public

record DetectabilityGap
  (ledger : ExcessErrorLedger)
  (w : HypotheticalOffLineWitness ledger) : Set where
  constructor detectabilityGap
  field
    gapPredecessor : Nat
    pairBeatsError :
      errorBudget ledger + suc gapPredecessor ≡ singlePairDefect w

open DetectabilityGap public

detectableOffLinePairContradictsGlobalErrorBound :
  (ledger : ExcessErrorLedger) →
  (w : HypotheticalOffLineWitness ledger) →
  DetectabilityGap ledger w →
  ⊥
detectableOffLinePairContradictsGlobalErrorBound ledger w gap =
  selfPlusPositiveImpossible
    (errorBudget ledger)
    positiveRemainder
    cycle
  where
  E : Nat
  E = errorBudget ledger

  g : Nat
  g = gapPredecessor gap

  o : Nat
  o = otherDefect w

  s : Nat
  s = errorSlack ledger

  positiveRemainder : Nat
  positiveRemainder = (g + o) + s

  packed : ((E + suc g) + o) + s ≡ E + suc positiveRemainder
  packed =
    trans
      (congTail (+-assoc E (suc g) o) s)
      (trans
        (+-assoc E (suc g + o) s)
        refl)

  chain : ((E + suc g) + o) + s ≡ E
  chain =
    trans
      (congTwoTails (pairBeatsError gap) o s)
      (trans
        (congTail (pairInsideAggregate w) s)
        (aggregateWithinError ledger))

  cycle : E + suc positiveRemainder ≡ E
  cycle = trans (sym packed) chain

------------------------------------------------------------------------
-- Error-floor obstruction.
------------------------------------------------------------------------

nonzeroDefectHiddenByPositiveError : ExcessErrorLedger
nonzeroDefectHiddenByPositiveError = excessErrorLedger 1 10 9 refl

hiddenAggregateDefectIsOne :
  aggregateDefect nonzeroDefectHiddenByPositiveError ≡ 1
hiddenAggregateDefectIsOne = refl

hiddenErrorBudgetIsTen :
  errorBudget nonzeroDefectHiddenByPositiveError ≡ 10
hiddenErrorBudgetIsTen = refl

oneIsNotZero : 1 ≡ zero → ⊥
oneIsNotZero ()

boundedByNonzeroErrorDoesNotForceVanishing :
  aggregateDefect nonzeroDefectHiddenByPositiveError ≡ zero → ⊥
boundedByNonzeroErrorDoesNotForceVanishing eq = oneIsNotZero eq

------------------------------------------------------------------------
-- Frontier socket.
------------------------------------------------------------------------

record RHDetectabilityProducer : Set₁ where
  field
    ZeroOrbit : Set
    offLine : ZeroOrbit → Set
    localDefect : ZeroOrbit → Nat
    localErrorBudget : ZeroOrbit → Nat
    amplificationLevel : ZeroOrbit → Nat
    detectable :
      (rho : ZeroOrbit) →
      offLine rho →
      Set

record HermitianDetectabilityBoundary : Set where
  field
    globalErrorContradictionClosed : Bool
    positiveErrorNoGoWitnessConstructed : Bool
    sourceTrG2MainTermIsNonzeroRecorded : Bool
    localizationProducerConstructedHere : Bool
    higherMomentAmplificationConstructedHere : Bool
    rhStrengthDetectabilityProvedHere : Bool

hermitianDetectabilityBoundary : HermitianDetectabilityBoundary
hermitianDetectabilityBoundary = record
  { globalErrorContradictionClosed = true
  ; positiveErrorNoGoWitnessConstructed = true
  ; sourceTrG2MainTermIsNonzeroRecorded = true
  ; localizationProducerConstructedHere = false
  ; higherMomentAmplificationConstructedHere = false
  ; rhStrengthDetectabilityProvedHere = false
  }
