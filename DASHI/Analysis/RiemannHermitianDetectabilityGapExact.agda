module DASHI.Analysis.RiemannHermitianDetectabilityGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / SCALE CALIBRATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- Their prime-side Theorem [thm:traces] gives, in the notation of the paper,
--
--   tr Gtilde^2
--     = (T L / 2pi) (ell_1^2 + L^2/3) (1 + O(E_T)),
--
-- not a quantity tending to zero.  Therefore a Hermitian transverse defect can
-- only force RH from this lane after subtracting/identifying the compatible
-- main term and proving the surviving defect is detectable above the remaining
-- arithmetic error floor.
--
-- This module closes that terminal logic exactly over Nat.  It also proves the
-- complementary obstruction: a nonzero global error allowance can contain a
-- nonzero defect, so `defect <= error` alone never implies defect = 0.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Elementary impossibility: a natural number cannot equal itself plus a
-- strictly positive amount.
------------------------------------------------------------------------

selfPlusPositiveImpossible :
  (n extra : Nat) → n + suc extra ≡ n → ⊥
selfPlusPositiveImpossible zero extra ()
selfPlusPositiveImpossible (suc n) extra eq =
  selfPlusPositiveImpossible n extra (dropSuc eq)
  where
  dropSuc : {a b : Nat} → suc a ≡ suc b → a ≡ b
  dropSuc refl = refl

------------------------------------------------------------------------
-- Source-calibrated excess/error ledger.
--
-- `aggregateDefect + errorSlack = errorBudget` is the subtraction-free form of
--
--   aggregateDefect <= errorBudget.
--
-- A hypothetical off-line pair contributes `singlePairDefect` inside the
-- aggregate.  RH-strength detection requires that this one-pair contribution
-- beat the entire permitted error floor by a strictly positive margin.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact contradiction theorem.
------------------------------------------------------------------------

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
  -- Combine
  --   pair + other = aggregate,
  --   aggregate + slack = error,
  --   error + positiveGap = pair
  -- into
  --   error + (positiveGap + other + slack) = error.
  positiveRemainder : Nat
  positiveRemainder =
    gapPredecessor gap + otherDefect w + errorSlack ledger

  reassoc :
    (a b c d : Nat) →
    ((a + suc b) + c) + d ≡ a + suc (b + c + d)
  reassoc zero b c d = refl
  reassoc (suc a) b c d =
    congSuc (reassoc a b c d)
    where
    congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
    congSuc refl = refl

  cycle :
    errorBudget ledger + suc positiveRemainder ≡ errorBudget ledger
  cycle =
    trans
      (sym (reassoc
        (errorBudget ledger)
        (gapPredecessor gap)
        (otherDefect w)
        (errorSlack ledger)))
      (trans
        (congRight
          (pairBeatsError gap)
          (otherDefect w)
          (errorSlack ledger))
        (trans
          (congTail
            (pairInsideAggregate w)
            (errorSlack ledger))
          (aggregateWithinError ledger)))
    where
    congRight :
      {a b : Nat} → a ≡ b → (c d : Nat) → (a + c) + d ≡ (b + c) + d
    congRight refl c d = refl

    congTail : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
    congTail refl c = refl

------------------------------------------------------------------------
-- Error-floor obstruction.
--
-- A positive allowance can genuinely hide a positive defect.  This checksum
-- prevents any later assembly from promoting `aggregate <= error` to
-- `aggregate = 0` without an additional shrinking/localization/amplification
-- theorem.
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
--
-- To upgrade the current second-moment lane from an aggregate transverse bound
-- to RH, one must construct detectability.  Plausible mechanisms are:
--
--   * ordinate localization: shrink the spectral window around one orbit;
--   * higher Schatten/Frobenius moments: amplify H/C > 1 multiplicatively;
--   * a stronger arithmetic identity that lowers the excess error floor.
--
-- This record names those producer outputs without claiming any is supplied by
-- Alpoge--Furman.
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
    globalErrorContradictionClosed : Agda.Builtin.Bool.Bool
    positiveErrorNoGoWitnessConstructed : Agda.Builtin.Bool.Bool
    sourceTrG2MainTermIsNonzeroRecorded : Agda.Builtin.Bool.Bool
    localizationProducerConstructedHere : Agda.Builtin.Bool.Bool
    higherMomentAmplificationConstructedHere : Agda.Builtin.Bool.Bool
    rhStrengthDetectabilityProvedHere : Agda.Builtin.Bool.Bool

open import Agda.Builtin.Bool using (true; false)

hermitianDetectabilityBoundary : HermitianDetectabilityBoundary
hermitianDetectabilityBoundary = record
  { globalErrorContradictionClosed = true
  ; positiveErrorNoGoWitnessConstructed = true
  ; sourceTrG2MainTermIsNonzeroRecorded = true
  ; localizationProducerConstructedHere = false
  ; higherMomentAmplificationConstructedHere = false
  ; rhStrengthDetectabilityProvedHere = false
  }
